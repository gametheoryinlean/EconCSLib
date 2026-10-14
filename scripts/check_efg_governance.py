#!/usr/bin/env python3
"""Check enforceable EFG architecture and lifecycle invariants.

This is intentionally a source-graph check rather than a Lean parser. It
guards the documented module register, explicit import-only facade lifecycle,
governed facade closures, root aggregate boundary, and dependency direction.
Lean elaboration and placeholder checks remain separate CI steps.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
import hashlib
from pathlib import Path
import re
import sys
from urllib.parse import unquote


IMPORT_RE = re.compile(
    r"^import\s+(EconCSLib(?:\.[A-Za-z0-9_]+)*)\s*$", re.MULTILINE
)
ANY_IMPORT_RE = re.compile(
    r"^import\s+([A-Za-z0-9_]+(?:\.[A-Za-z0-9_]+)*)\s*$", re.MULTILINE
)
MODULE_ROW_RE = re.compile(r"^\| `(EconCSLib\.[^`]+)` \|", re.MULTILINE)
STATUS_SUMMARY_ROW_RE = re.compile(
    r"^\| (Canonical|Frontend|Historical|Compatibility|Experimental|Internal) "
    r"\| (\d+) \|$",
    re.MULTILINE,
)
MARKDOWN_LINK_RE = re.compile(r"!?\[[^\]]*\]\(([^)]+)\)")
FULL_MODULE_REFERENCE_RE = re.compile(
    r"`(EconCSLib(?:\.[A-Za-z0-9_]+)+)`"
)
LARGE_MODULE_ROW_RE = re.compile(
    r"^\| `(EconCSLib\.GameTheory\.ExtensiveGame\.[^`]+)` "
    r"\| `(800-999|1000-1199|1200\+)` \|",
    re.MULTILINE,
)
DECLARATION_RE = re.compile(
    r"^(?:private\s+|protected\s+|noncomputable\s+|unsafe\s+)*"
    r"(?:abbrev|axiom|class|def|example|inductive|instance|lemma|opaque|"
    r"structure|theorem)\b",
    re.MULTILINE,
)
DEPRECATED_RE = re.compile(
    r"@\[\s*deprecated[^\]]*\]\s*"
    r"(?:private\s+|protected\s+|noncomputable\s+|unsafe\s+)*"
    r"(?:abbrev|class|def|inductive|instance|lemma|structure|theorem)\s+"
    r"([A-Za-z0-9_'.]+)",
    re.MULTILINE,
)
NONCOMPUTABLE_DATA_DECL_RE = re.compile(
    r"^\s*noncomputable\s+(?:section|abbrev|def|instance|opaque)\b",
    re.MULTILINE,
)
SEMANTIC_CERTIFICATE_THEOREM_RE = re.compile(
    r"^\s*(?:theorem|lemma)\s+[A-Za-z0-9_'.]*"
    r"(?:_eq_|_represents(?:_|\b))[A-Za-z0-9_'.]*\b",
    re.MULTILINE,
)

EFG_PREFIX = "EconCSLib.GameTheory.ExtensiveGame."
LARGE_EFG_LINE_THRESHOLD = 800

# Every import-only source module is an explicit navigation surface. Adding a
# new one therefore requires a deliberate entry here, not merely a file with a
# convenient transitive closure.
CANONICAL_IMPORT_ONLY_MODULES = {
    "EconCSLib",
    "EconCSLib.Examples",
    "EconCSLib.OpenProblem",
    "EconCSLib.GameTheory.GameForm",
    "EconCSLib.Math.Probability.FiniteLaw",
    "EconCSLib.Math.Probability.Effective",
    "EconCSLib.Math.Probability.Effective.Analytic",
    f"{EFG_PREFIX}Interface.StructuralCore",
    f"{EFG_PREFIX}Interface.Core",
    f"{EFG_PREFIX}Interface.Objective",
    f"{EFG_PREFIX}Interface.Winning",
    f"{EFG_PREFIX}Interface.Winning.Stochastic",
    f"{EFG_PREFIX}Interface.Execution.Finite",
    f"{EFG_PREFIX}Interface.Execution.Infinite",
    f"{EFG_PREFIX}Interface.Execution.Analytic",
    f"{EFG_PREFIX}Interface.Relations.Discrete",
    f"{EFG_PREFIX}Interface.Preservation",
    f"{EFG_PREFIX}Interface.Equilibrium.Discrete",
    f"{EFG_PREFIX}Interface.Equilibrium.Analytic",
    f"{EFG_PREFIX}Interface.Restart",
    f"{EFG_PREFIX}Interface.Compilation.Discrete",
    f"{EFG_PREFIX}Observed.Controlled.Infrastructure",
    f"{EFG_PREFIX}Observed.Controlled.Morphism",
}

# Compatibility wrappers are allowed only while explicitly listed here and in
# the module-status register. The current pre-release hard migration leaves no
# temporary wrappers.
TEMPORARY_COMPATIBILITY_IMPORT_ONLY_MODULES: set[str] = set()

# These paths were intentionally removed after their internal consumers were
# migrated. Recreating a redirect stub or importing one is a governance error.
REMOVED_MODULE_PATHS = {
    "EconCSLib.Foundation.Player",
    f"{EFG_PREFIX}Play",
    f"{EFG_PREFIX}BehaviorStrategy",
    f"{EFG_PREFIX}FOSG.FOSGSequentialization",
    f"{EFG_PREFIX}Observed.Morphism",
    f"{EFG_PREFIX}Observed.Morphism.Fiber",
    f"{EFG_PREFIX}Observed.Refinement",
    f"{EFG_PREFIX}Observed.BehaviorRefinement",
    f"{EFG_PREFIX}Observed.DeferredSampling",
    f"{EFG_PREFIX}Observed.KuhnConditioning",
    f"{EFG_PREFIX}Observed.PathLawEquivalence",
    f"{EFG_PREFIX}Interface.Execution.Discrete",
    f"{EFG_PREFIX}Interface.Relations",
    f"{EFG_PREFIX}Interface.Equilibrium",
    f"{EFG_PREFIX}Interface.Compilation",
    f"{EFG_PREFIX}Interface.SimulationFramework",
    f"{EFG_PREFIX}Simulation.ObservedMeasurableKernelRestartCompatibility",
    f"{EFG_PREFIX}Probability.ConditionalSampling",
    f"{EFG_PREFIX}Probability.ConditionalProduct",
    f"{EFG_PREFIX}Probability.DeferredSampling",
    f"{EFG_PREFIX}Probability.FiniteProductCoupling",
    "EconCSLib.GameTheory.GameForm.Continuation",
    f"{EFG_PREFIX}Execution.DependentFiber",
    f"{EFG_PREFIX}Execution.StochasticNaturality",
}

EXPECTED_CLOSURES = {
    "EconCSLib": (54, 173),
    f"{EFG_PREFIX}Interface.StructuralCore": (5, 5),
    f"{EFG_PREFIX}Interface.Core": (17, 23),
    f"{EFG_PREFIX}Interface.Objective": (33, 45),
    f"{EFG_PREFIX}Interface.Winning": (36, 48),
    f"{EFG_PREFIX}Interface.Winning.Stochastic": (67, 79),
    f"{EFG_PREFIX}Interface.Execution.Finite": (50, 62),
    f"{EFG_PREFIX}Interface.Execution.Infinite": (55, 67),
    f"{EFG_PREFIX}Interface.Execution.Analytic": (82, 96),
    f"{EFG_PREFIX}Interface.Relations.Discrete": (55, 67),
    f"{EFG_PREFIX}Interface.Preservation": (22, 34),
    f"{EFG_PREFIX}Interface.Equilibrium.Discrete": (85, 103),
    f"{EFG_PREFIX}Interface.Equilibrium.Analytic": (125, 148),
    f"{EFG_PREFIX}Interface.Restart": (134, 157),
    f"{EFG_PREFIX}Interface.Compilation.Discrete": (106, 126),
}

GOVERNANCE_CLOSURE_LABELS = {
    entry: entry.removeprefix(EFG_PREFIX)
    for entry in EXPECTED_CLOSURES
}

STRUCTURAL_CORE = f"{EFG_PREFIX}Interface.StructuralCore"
EXPECTED_STRUCTURAL_CORE_EFG_CLOSURE = {
    f"{EFG_PREFIX}Structural.Basic",
    f"{EFG_PREFIX}Structural.Reachability",
    f"{EFG_PREFIX}Structural.History",
    f"{EFG_PREFIX}Execution.CompletePlay",
    f"{EFG_PREFIX}Observed.Controlled",
}

# No minimal carrier currently carries a source-level compatibility freeze.
# Keep the generic fingerprint machinery below so a later, explicit freeze
# decision can add reviewed contracts without redesigning the checker.
FROZEN_MINIMAL_CORE_STRUCTURES = {}

CONTROLLED_OBSERVED_MODULE = f"{EFG_PREFIX}Observed.Controlled"
CONTROLLED_DECISION_START = (
    r"^structure ControlledDecisionGame \(N : Type uN\) where\s*$"
)
CONTROLLED_DECISION_END = (
    r"^structure ControlledObservedGame \(N : Type uN\)\s*$"
)
CONTROLLED_OBSERVED_START = (
    r"^structure ControlledObservedGame \(N : Type uN\)\s*$"
)
CONTROLLED_OBSERVED_EXTENDS = (
    r"^\s*extends\s+"
    r"ControlledDecisionGame\.\{\s*uN\s*,\s*uA\s*,\s*uS\s*,\s*uI\s*\}"
    r"\s+N\s+where\s*$"
)

CONTROLLED_INFRASTRUCTURE_RECALL = (
    f"{EFG_PREFIX}Observed.Controlled.Infrastructure.Recall"
)
CONTROLLED_INFRASTRUCTURE_WELL_FORMED = (
    f"{EFG_PREFIX}Observed.Controlled.Infrastructure.WellFormed"
)
CONTROLLED_MORPHISM_CORE = f"{EFG_PREFIX}Observed.Controlled.Morphism.Core"
CONTROLLED_MORPHISM_SUBGAME = f"{EFG_PREFIX}Observed.Controlled.Morphism.Subgame"
CONTROLLED_MORPHISM_RECALL = f"{EFG_PREFIX}Observed.Controlled.Morphism.Recall"
CONTROLLED_MORPHISM_OBJECTIVE = (
    f"{EFG_PREFIX}Observed.Controlled.Morphism.Objective"
)

EXPECTED_EXACT_EFG_CLOSURES = {
    CONTROLLED_INFRASTRUCTURE_RECALL: {
        f"{EFG_PREFIX}Structural.Basic",
        f"{EFG_PREFIX}Structural.Reachability",
        f"{EFG_PREFIX}Structural.History",
        f"{EFG_PREFIX}Execution.CompletePlay",
        f"{EFG_PREFIX}Observed.Controlled",
        CONTROLLED_INFRASTRUCTURE_WELL_FORMED,
    },
    CONTROLLED_INFRASTRUCTURE_WELL_FORMED: {
        f"{EFG_PREFIX}Structural.Basic",
        f"{EFG_PREFIX}Structural.Reachability",
        f"{EFG_PREFIX}Structural.History",
        f"{EFG_PREFIX}Execution.CompletePlay",
        f"{EFG_PREFIX}Observed.Controlled",
    },
    CONTROLLED_MORPHISM_CORE: {
        f"{EFG_PREFIX}Basic",
        f"{EFG_PREFIX}Structural.Basic",
        f"{EFG_PREFIX}Structural.Reachability",
        f"{EFG_PREFIX}Structural.History",
        f"{EFG_PREFIX}Execution.CompletePlay",
        f"{EFG_PREFIX}Execution.StoppedExecution",
        f"{EFG_PREFIX}Relations.Discrete.Morphism",
        f"{EFG_PREFIX}Observed.Controlled",
    },
    CONTROLLED_MORPHISM_SUBGAME: {
        f"{EFG_PREFIX}Basic",
        f"{EFG_PREFIX}Structural.Basic",
        f"{EFG_PREFIX}Structural.Reachability",
        f"{EFG_PREFIX}Structural.History",
        f"{EFG_PREFIX}Execution.CompletePlay",
        f"{EFG_PREFIX}Execution.StoppedExecution",
        f"{EFG_PREFIX}Relations.Discrete.Morphism",
        f"{EFG_PREFIX}Observed.Controlled",
        f"{EFG_PREFIX}Observed.Controlled.Infrastructure.Subgame",
        CONTROLLED_MORPHISM_CORE,
    },
    CONTROLLED_MORPHISM_RECALL: {
        f"{EFG_PREFIX}Basic",
        f"{EFG_PREFIX}Structural.Basic",
        f"{EFG_PREFIX}Structural.Reachability",
        f"{EFG_PREFIX}Structural.History",
        f"{EFG_PREFIX}Execution.CompletePlay",
        f"{EFG_PREFIX}Execution.StoppedExecution",
        f"{EFG_PREFIX}Relations.Discrete.Morphism",
        f"{EFG_PREFIX}Observed.Controlled",
        CONTROLLED_INFRASTRUCTURE_WELL_FORMED,
        CONTROLLED_INFRASTRUCTURE_RECALL,
        CONTROLLED_MORPHISM_CORE,
    },
}

EXPECTED_CONTROLLED_AGGREGATE_IMPORTS = {
    f"{EFG_PREFIX}Observed.Controlled.Infrastructure": {
        f"{EFG_PREFIX}Observed.Controlled.Infrastructure.Core",
        CONTROLLED_INFRASTRUCTURE_WELL_FORMED,
        f"{EFG_PREFIX}Observed.Controlled.Infrastructure.Subgame",
        f"{EFG_PREFIX}Observed.Controlled.Infrastructure.Finite",
        f"{EFG_PREFIX}Observed.Controlled.Infrastructure.Quasi",
        f"{EFG_PREFIX}Observed.Controlled.Infrastructure.Recall",
        f"{EFG_PREFIX}Winning.Basic",
    },
    f"{EFG_PREFIX}Observed.Controlled.Morphism": {
        CONTROLLED_MORPHISM_CORE,
        CONTROLLED_MORPHISM_SUBGAME,
        CONTROLLED_MORPHISM_RECALL,
        CONTROLLED_MORPHISM_OBJECTIVE,
    },
}

EXPECTED_EFFECTIVE_AGGREGATE_IMPORTS = {
    "EconCSLib.Math.Probability.Effective": {
        "EconCSLib.Math.Probability.Effective.Enclosure",
        "EconCSLib.Math.Probability.Effective.Core",
        "EconCSLib.Math.Probability.Effective.Uniform",
    },
    "EconCSLib.Math.Probability.Effective.Analytic": {
        "EconCSLib.Math.Probability.Effective",
        "EconCSLib.Math.Probability.Effective.Semantics",
        "EconCSLib.Math.Probability.Effective.UniformSemantics",
    },
}

CONTROLLED_MODULE_ROLES = {
    f"{EFG_PREFIX}Observed.Controlled": "carrier",
    f"{EFG_PREFIX}Observed.Controlled.Semantics": "canonical-semantic-owner",
    f"{EFG_PREFIX}Observed.Controlled.Law": "canonical-semantic-owner",
    f"{EFG_PREFIX}Observed.Controlled.Law.Discrete": "canonical-semantic-owner",
    f"{EFG_PREFIX}Observed.Controlled.Law.DiscretePath": "canonical-semantic-owner",
    f"{EFG_PREFIX}Observed.Controlled.Law.Analytic": "canonical-semantic-owner",
    f"{EFG_PREFIX}Observed.Controlled.Infrastructure": "aggregate-facade",
    f"{EFG_PREFIX}Observed.Controlled.Infrastructure.Core":
        "canonical-responsibility-owner",
    f"{EFG_PREFIX}Observed.Controlled.Infrastructure.WellFormed":
        "canonical-responsibility-owner",
    f"{EFG_PREFIX}Observed.Controlled.Infrastructure.Subgame":
        "canonical-responsibility-owner",
    f"{EFG_PREFIX}Observed.Controlled.Infrastructure.Finite":
        "canonical-responsibility-owner",
    f"{EFG_PREFIX}Observed.Controlled.Infrastructure.Quasi":
        "canonical-responsibility-owner",
    f"{EFG_PREFIX}Observed.Controlled.Infrastructure.Recall":
        "canonical-responsibility-owner",
    f"{EFG_PREFIX}Observed.Controlled.Morphism": "aggregate-facade",
    f"{EFG_PREFIX}Observed.Controlled.Morphism.Core":
        "canonical-responsibility-owner",
    f"{EFG_PREFIX}Observed.Controlled.Morphism.Subgame":
        "canonical-responsibility-owner",
    f"{EFG_PREFIX}Observed.Controlled.Morphism.Recall":
        "canonical-responsibility-owner",
    CONTROLLED_MORPHISM_OBJECTIVE:
        "canonical-responsibility-owner",
    f"{EFG_PREFIX}Observed.Controlled.Compat.DiscreteLaw":
        "payoff-aware-adapter",
    f"{EFG_PREFIX}Observed.Controlled.Compat.Infrastructure":
        "payoff-aware-adapter",
    f"{EFG_PREFIX}Observed.Controlled.Compat.Morphism":
        "payoff-aware-adapter",
}

EXPECTED_PAYOFF_AWARE_ADAPTER_IMPORTS = {
    f"{EFG_PREFIX}Observed.Controlled.Compat.DiscreteLaw": {
        f"{EFG_PREFIX}Observed.Chance",
        f"{EFG_PREFIX}Observed.Controlled.Law.Discrete",
    },
    f"{EFG_PREFIX}Observed.Controlled.Compat.Infrastructure": {
        CONTROLLED_INFRASTRUCTURE_RECALL,
        f"{EFG_PREFIX}Observed.Quasi",
        f"{EFG_PREFIX}Observed.SignalRecall",
    },
    f"{EFG_PREFIX}Observed.Controlled.Compat.Morphism": {
        CONTROLLED_MORPHISM_CORE,
        f"{EFG_PREFIX}Observed.Morphism.Inverse",
    },
}

EXPECTED_PAYOFF_AWARE_ADAPTER_NAMESPACES = {
    f"{EFG_PREFIX}Observed.Controlled.Compat.DiscreteLaw":
        "ExtensiveGame.ObservedChanceGame",
    f"{EFG_PREFIX}Observed.Controlled.Compat.Infrastructure":
        "ExtensiveGame.ObservedGame",
    f"{EFG_PREFIX}Observed.Controlled.Compat.Morphism":
        "ExtensiveGame.ObservedGame",
}

CONTROLLED_CANONICAL_OWNERS = {
    module
    for module, role in CONTROLLED_MODULE_ROLES.items()
    if role != "payoff-aware-adapter"
}

CORE_FORBIDDEN_CLOSURE_MODULES = {
    f"{EFG_PREFIX}Execution.Objective",
    f"{EFG_PREFIX}Winning.Basic",
}

CORE_FORBIDDEN_CLOSURE_PREFIXES = (
    f"{EFG_PREFIX}Winning.",
)

EXPECTED_ROOT_EFG_IMPORTS = {
    f"{EFG_PREFIX}Interface.Execution.Finite",
    f"{EFG_PREFIX}GameTree",
    f"{EFG_PREFIX}BackwardInduction",
    f"{EFG_PREFIX}ZeroSumGameTreeWithChance",
}

FORBIDDEN_ROOT_MODULES = {
    f"{EFG_PREFIX}Execution.InfiniteTrajectory",
    f"{EFG_PREFIX}Observed.InfiniteExecution",
    f"{EFG_PREFIX}Interface.Execution.Infinite",
    f"{EFG_PREFIX}Interface.Execution.Discrete",
    f"{EFG_PREFIX}GameTreeSPE",
    f"{EFG_PREFIX}GameTreeNE",
    f"{EFG_PREFIX}GameTreeStrategicForm",
    f"{EFG_PREFIX}FiniteArenaExtraction",
    f"{EFG_PREFIX}Zermelo",
}

MOVED_PATHS = {
    f"{EFG_PREFIX}Simulation.KernelArena":
        f"{EFG_PREFIX}Execution.Discrete.KernelArena",
    f"{EFG_PREFIX}Simulation.KernelTrajectory":
        f"{EFG_PREFIX}Execution.Discrete.KernelTrajectory",
    f"{EFG_PREFIX}Simulation.Morphism":
        f"{EFG_PREFIX}Relations.Discrete.Morphism",
    f"{EFG_PREFIX}Simulation.KernelWeakSimulation":
        f"{EFG_PREFIX}Relations.Discrete.KernelWeakSimulation",
    f"{EFG_PREFIX}Simulation.DiscreteInfinitePathBridge":
        f"{EFG_PREFIX}Simulation.Kernel.DiscreteBridge",
    f"{EFG_PREFIX}Simulation.MeasurableKernelArena":
        f"{EFG_PREFIX}Simulation.Kernel.Arena",
    f"{EFG_PREFIX}Simulation.MeasurableKernelExecution":
        f"{EFG_PREFIX}Simulation.Kernel.Execution",
    f"{EFG_PREFIX}Simulation.MeasurableKernelEndpoint":
        f"{EFG_PREFIX}Simulation.Kernel.Endpoint",
    f"{EFG_PREFIX}Simulation.MeasurableKernelPath":
        f"{EFG_PREFIX}Simulation.Kernel.StatePath",
    f"{EFG_PREFIX}Simulation.MeasurableKernelHistoryPath":
        f"{EFG_PREFIX}Simulation.Kernel.HistoryPath",
    f"{EFG_PREFIX}Simulation.MeasurableKernelEventPath":
        f"{EFG_PREFIX}Simulation.Kernel.EventPath",
    f"{EFG_PREFIX}Simulation.MeasurableKernelObservedEvent":
        f"{EFG_PREFIX}Simulation.Kernel.ObservedEvent",
    f"{EFG_PREFIX}Simulation.MeasurableKernelRealizedInformation":
        f"{EFG_PREFIX}Simulation.Kernel.RealizedInformation",
    f"{EFG_PREFIX}Simulation.ObservedChanceKernelBridge":
        f"{EFG_PREFIX}Simulation.Presentation.Chance.KernelBridge",
    f"{EFG_PREFIX}Simulation.ObservedChanceRealizedPresentation":
        f"{EFG_PREFIX}Simulation.Presentation.Chance.Realized",
    f"{EFG_PREFIX}Simulation.ObservedChanceCountablePresentation":
        f"{EFG_PREFIX}Simulation.Presentation.Chance.Countable",
    f"{EFG_PREFIX}Simulation.ObservedChanceMeasurableHistory":
        f"{EFG_PREFIX}Simulation.Presentation.Chance.MeasurableHistory",
    f"{EFG_PREFIX}Simulation.ObservedChanceMeasurablePresentation":
        f"{EFG_PREFIX}Simulation.Presentation.Chance.Measurable",
    f"{EFG_PREFIX}Simulation.ObservedChanceMeasurableProfileAssembly":
        f"{EFG_PREFIX}Simulation.Presentation.Chance.ProfileAssembly",
    f"{EFG_PREFIX}Simulation.ObservedMeasurableKernelPresentation":
        f"{EFG_PREFIX}Simulation.Presentation.Kernel.Core",
    f"{EFG_PREFIX}Simulation.ObservedMeasurableKernelProfileAssembly":
        f"{EFG_PREFIX}Simulation.Presentation.Kernel.ProfileAssembly",
    f"{EFG_PREFIX}Simulation.ObservedMeasurableKernelOutcome":
        f"{EFG_PREFIX}Simulation.Equilibrium.Outcome",
    f"{EFG_PREFIX}Simulation.MeasurableKernelContinuationPath":
        f"{EFG_PREFIX}Simulation.Continuation.Path",
    f"{EFG_PREFIX}Simulation.MeasurableKernelContinuationConditioning":
        f"{EFG_PREFIX}Simulation.Continuation.Conditioning",
    f"{EFG_PREFIX}Simulation.ObservedMeasurableKernelContinuation":
        f"{EFG_PREFIX}Simulation.Continuation.Observed",
    f"{EFG_PREFIX}Simulation.ObservedMeasurableKernelContinuationConditioning":
        f"{EFG_PREFIX}Simulation.Continuation.ObservedConditioning",
    f"{EFG_PREFIX}Simulation.ObservedMeasurableKernelRestart.Core":
        f"{EFG_PREFIX}Simulation.Restart.Core",
    f"{EFG_PREFIX}Simulation.ObservedMeasurableKernelRestart.Trajectory":
        f"{EFG_PREFIX}Simulation.Restart.Trajectory",
    f"{EFG_PREFIX}Simulation.ObservedMeasurableKernelRestart.Certificates":
        f"{EFG_PREFIX}Simulation.Restart.Certificates",
    f"{EFG_PREFIX}Simulation.ObservedMeasurableKernelRestart.Observed":
        f"{EFG_PREFIX}Simulation.Restart.Observed",
    f"{EFG_PREFIX}Simulation.ObservedMeasurableKernelRestart.Assembly":
        f"{EFG_PREFIX}Simulation.Restart.Assembly",
    f"{EFG_PREFIX}Simulation.ObservedMeasurableKernelRestart.Equilibrium":
        f"{EFG_PREFIX}Simulation.Restart.Equilibrium",
    f"{EFG_PREFIX}Simulation.ObservedMeasurableKernelRestartFactorization":
        f"{EFG_PREFIX}Simulation.Restart.Factorization",
}

HISTORICAL_IMPORT_ALLOWLIST = {
    (
        f"{EFG_PREFIX}Compiler.GameTreeOccurrenceObserved",
        f"{EFG_PREFIX}Compiler.GameTreeObserved",
    ): (
        "the occurrence-sensitive compiler proves exact refinement and "
        "strategy-lifting bridges to the retained endpoint compiler"
    ),
    (
        f"{EFG_PREFIX}FiniteArenaExtraction",
        f"{EFG_PREFIX}GameTreeNE",
    ): (
        "the extraction frontend preserves the historical endpoint-policy "
        "subgame-perfect-to-root-Nash theorem"
    ),
    (
        f"{EFG_PREFIX}Zermelo",
        f"{EFG_PREFIX}GameTreeNE",
    ): (
        "the specialized Zermelo frontend states retained endpoint-policy "
        "Kuhn and Nash corollaries"
    ),
}

FORBIDDEN_DIRECT_IMPORTS = {
    (
        f"{EFG_PREFIX}Structural.History",
        f"{EFG_PREFIX}Subgame",
    ): "canonical history infrastructure must depend only on reachability",
    (
        f"{EFG_PREFIX}StochasticGameTree",
        f"{EFG_PREFIX}GameTreeSPE",
    ): "stochastic tree syntax needs only the structural GameTree module",
    (
        "EconCSLib.Math.DependentFiber",
        f"{EFG_PREFIX}Relations.Discrete.Morphism",
    ): "game-independent dependent-fiber calculus cannot import EFG relations",
}

# These modules form the payoff-free dependency spine.  Their complete local
# import closures must not reach legacy payoff-aware observed games,
# compatibility adapters, equilibrium/simulation implementations, or the
# payoff-aware winning layer.
PAYOFF_FREE_CORE_BOUNDARIES = {
    f"{EFG_PREFIX}Relations.Discrete.StochasticNaturality",
    f"{EFG_PREFIX}Observed.Controlled",
    f"{EFG_PREFIX}Observed.Controlled.Infrastructure",
    f"{EFG_PREFIX}Observed.Controlled.Infrastructure.Core",
    CONTROLLED_INFRASTRUCTURE_WELL_FORMED,
    f"{EFG_PREFIX}Observed.Controlled.Infrastructure.Subgame",
    f"{EFG_PREFIX}Observed.Controlled.Infrastructure.Finite",
    f"{EFG_PREFIX}Observed.Controlled.Infrastructure.Quasi",
    f"{EFG_PREFIX}Observed.Controlled.Infrastructure.Recall",
    f"{EFG_PREFIX}Observed.Controlled.Morphism",
    CONTROLLED_MORPHISM_CORE,
    CONTROLLED_MORPHISM_SUBGAME,
    CONTROLLED_MORPHISM_RECALL,
    CONTROLLED_MORPHISM_OBJECTIVE,
    f"{EFG_PREFIX}Observed.Controlled.Semantics",
    f"{EFG_PREFIX}Observed.Controlled.Law.Discrete",
    f"{EFG_PREFIX}Observed.Controlled.Law",
    f"{EFG_PREFIX}Winning.Basic",
    f"{EFG_PREFIX}Winning.Determinacy",
    STRUCTURAL_CORE,
    f"{EFG_PREFIX}Interface.Core",
}

FORBIDDEN_PAYOFF_FREE_CLOSURE_MODULES = {
    f"{EFG_PREFIX}Observed.Game",
    f"{EFG_PREFIX}Observed.Semantics",
    f"{EFG_PREFIX}Observed.WellFormed",
    f"{EFG_PREFIX}Observed.Quasi",
    f"{EFG_PREFIX}Observed.PerfectRecall",
    f"{EFG_PREFIX}Observed.SignalRecall",
    f"{EFG_PREFIX}Observed.Chance",
    f"{EFG_PREFIX}Observed.Behavior",
    f"{EFG_PREFIX}Observed.InfiniteExecution",
    f"{EFG_PREFIX}Observed.Controlled.Compat.Infrastructure",
    f"{EFG_PREFIX}Observed.Controlled.Compat.Morphism",
    f"{EFG_PREFIX}Observed.Controlled.Compat.DiscreteLaw",
    f"{EFG_PREFIX}Winning.BasicCompat",
    f"{EFG_PREFIX}Winning.DeterminacyCompat",
}

FORBIDDEN_PAYOFF_FREE_CLOSURE_PREFIXES = (
    f"{EFG_PREFIX}Observed.Morphism.",
    f"{EFG_PREFIX}Observed.Equilibrium",
    f"{EFG_PREFIX}Simulation.",
    f"{EFG_PREFIX}Interface.Equilibrium",
)

MAXIMUM_PATH_LAW_MODULE = f"{EFG_PREFIX}Observed.Controlled.Law"
MAXIMUM_PATH_LAW_FORBIDDEN_NAMES = {
    "PMF",
    "Countable",
    "DiscreteControlledObservedChanceGame",
    "ObservedGame",
}

DISCRETE_PATH_LAW_ADAPTER = (
    f"{EFG_PREFIX}Observed.Controlled.Law.DiscretePath"
)
ANALYTIC_PATH_LAW_ADAPTER = (
    f"{EFG_PREFIX}Observed.Controlled.Law.Analytic"
)
MEASURABLE_KERNEL_ARENA = f"{EFG_PREFIX}Simulation.Kernel.Arena"

# The execution regimes share a maximum lawful path-law carrier, not one
# universal local executor. These route checks make that ownership boundary
# enforceable without pretending that imports prove semantic preservation.
SEMANTIC_REGIME_ROUTE_CONTRACTS = {
    f"{EFG_PREFIX}Interface.Execution.Finite": (
        set(),
        {
            MAXIMUM_PATH_LAW_MODULE,
            DISCRETE_PATH_LAW_ADAPTER,
            ANALYTIC_PATH_LAW_ADAPTER,
            MEASURABLE_KERNEL_ARENA,
        },
    ),
    f"{EFG_PREFIX}Interface.Execution.Infinite": (
        {MAXIMUM_PATH_LAW_MODULE, DISCRETE_PATH_LAW_ADAPTER},
        {ANALYTIC_PATH_LAW_ADAPTER, MEASURABLE_KERNEL_ARENA},
    ),
    f"{EFG_PREFIX}Interface.Execution.Analytic": (
        {
            MAXIMUM_PATH_LAW_MODULE,
            DISCRETE_PATH_LAW_ADAPTER,
            ANALYTIC_PATH_LAW_ADAPTER,
            MEASURABLE_KERNEL_ARENA,
        },
        set(),
    ),
    f"{EFG_PREFIX}Interface.Compilation.Discrete": (
        set(),
        {
            MAXIMUM_PATH_LAW_MODULE,
            DISCRETE_PATH_LAW_ADAPTER,
            ANALYTIC_PATH_LAW_ADAPTER,
            MEASURABLE_KERNEL_ARENA,
        },
    ),
    f"{EFG_PREFIX}FOSG.Sequentialization.Core": (
        set(),
        {
            MAXIMUM_PATH_LAW_MODULE,
            DISCRETE_PATH_LAW_ADAPTER,
            ANALYTIC_PATH_LAW_ADAPTER,
            MEASURABLE_KERNEL_ARENA,
        },
    ),
    f"{EFG_PREFIX}FOSG.Sequentialization.Equilibrium": (
        set(),
        {
            MAXIMUM_PATH_LAW_MODULE,
            DISCRETE_PATH_LAW_ADAPTER,
            ANALYTIC_PATH_LAW_ADAPTER,
            MEASURABLE_KERNEL_ARENA,
        },
    ),
}

# Executable definitions own values; analytic leaves own only their
# interpretation and compatibility proofs.  Each tuple contains the required
# executable owners and the smallest governed facade that exposes the bridge.
SEMANTIC_COMPATIBILITY_BRIDGES = {
    "EconCSLib.Math.Probability.Effective.Semantics": (
        {
            "EconCSLib.Math.Probability.Effective.Enclosure",
            "EconCSLib.Math.Probability.Effective.Core",
        },
        "EconCSLib.Math.Probability.Effective.Analytic",
    ),
    "EconCSLib.Math.Probability.Effective.UniformSemantics": (
        {"EconCSLib.Math.Probability.Effective.Uniform"},
        "EconCSLib.Math.Probability.Effective.Analytic",
    ),
    f"{EFG_PREFIX}Simulation.Kernel.FiniteExecution": (
        {
            f"{EFG_PREFIX}Execution.Discrete.HistoryKernel",
            f"{EFG_PREFIX}Execution.Discrete.FiniteObservation",
        },
        f"{EFG_PREFIX}Interface.Execution.Analytic",
    ),
    f"{EFG_PREFIX}Simulation.Kernel.EffectivePathLaw": (
        {f"{EFG_PREFIX}Execution.Discrete.EffectivePathLaw"},
        f"{EFG_PREFIX}Interface.Execution.Analytic",
    ),
    f"{EFG_PREFIX}Simulation.Kernel.CertifiedPathApproximation": (
        {f"{EFG_PREFIX}Execution.Discrete.CertifiedPathApproximation"},
        f"{EFG_PREFIX}Interface.Execution.Analytic",
    ),
    f"{EFG_PREFIX}Simulation.Kernel.FiniteRealizedInformation": (
        {f"{EFG_PREFIX}Execution.Discrete.RealizedInformation"},
        f"{EFG_PREFIX}Interface.Execution.Analytic",
    ),
    f"{EFG_PREFIX}Simulation.Kernel.FiniteCompleteEventPath": (
        {f"{EFG_PREFIX}Execution.Discrete.FiniteCompleteEventPath"},
        f"{EFG_PREFIX}Interface.Execution.Analytic",
    ),
    f"{EFG_PREFIX}Simulation.Presentation.Kernel.EffectiveBehavioralProfile": (
        {f"{EFG_PREFIX}Execution.Discrete.EffectiveKernelBehavioralProfile"},
        f"{EFG_PREFIX}Interface.Execution.Analytic",
    ),
    f"{EFG_PREFIX}Simulation.Continuation.FiniteConditioning": (
        {f"{EFG_PREFIX}Execution.Discrete.ConditionalContinuation"},
        f"{EFG_PREFIX}Interface.Equilibrium.Analytic",
    ),
    f"{EFG_PREFIX}Simulation.Equilibrium.FinitePayoff": (
        {f"{EFG_PREFIX}Execution.FinitePayoff"},
        f"{EFG_PREFIX}Interface.Equilibrium.Analytic",
    ),
    f"{EFG_PREFIX}Simulation.Equilibrium.EffectivePathUtility": (
        {"EconCSLib.Math.Probability.Effective.Core"},
        f"{EFG_PREFIX}Interface.Equilibrium.Analytic",
    ),
    f"{EFG_PREFIX}Simulation.Presentation.Chance.FiniteExecution": (
        {f"{EFG_PREFIX}Execution.Discrete.ObservedChance"},
        f"{EFG_PREFIX}Interface.Execution.Analytic",
    ),
    f"{EFG_PREFIX}Simulation.Restart.FiniteExecution": (
        {f"{EFG_PREFIX}Execution.Discrete.FiniteObservation"},
        f"{EFG_PREFIX}Interface.Restart",
    ),
}

# These modules are the current algorithm-first EFG owners. Their values must
# remain executable and reachable through the smallest documented facade,
# without importing an analytic bridge, supplied infinite law, or measure
# interpretation leaf.
ALGORITHM_FIRST_EXECUTABLE_OWNERS = {
    "EconCSLib.Math.Probability.Effective.Enclosure":
        "EconCSLib.Math.Probability.Effective",
    "EconCSLib.Math.Probability.Effective.Core":
        "EconCSLib.Math.Probability.Effective",
    "EconCSLib.Math.Probability.Effective.Uniform":
        "EconCSLib.Math.Probability.Effective",
    f"{EFG_PREFIX}Execution.Discrete.HistoryKernel":
        f"{EFG_PREFIX}Interface.Execution.Finite",
    f"{EFG_PREFIX}Execution.Discrete.FiniteObservation":
        f"{EFG_PREFIX}Interface.Execution.Finite",
    f"{EFG_PREFIX}Execution.Discrete.EffectivePathLaw":
        f"{EFG_PREFIX}Interface.Execution.Finite",
    f"{EFG_PREFIX}Execution.Discrete.EffectivePathUtility":
        f"{EFG_PREFIX}Interface.Execution.Finite",
    f"{EFG_PREFIX}Execution.Discrete.CertifiedPathApproximation":
        f"{EFG_PREFIX}Interface.Execution.Finite",
    f"{EFG_PREFIX}Execution.Discrete.DiscountedPathUtility":
        f"{EFG_PREFIX}Interface.Execution.Finite",
    f"{EFG_PREFIX}Execution.Discrete.FiniteCompleteEventPath":
        f"{EFG_PREFIX}Interface.Execution.Finite",
    f"{EFG_PREFIX}Execution.Discrete.RealizedInformation":
        f"{EFG_PREFIX}Interface.Execution.Finite",
    f"{EFG_PREFIX}Execution.Discrete.EffectiveKernelBehavioralProfile":
        f"{EFG_PREFIX}Interface.Execution.Finite",
    f"{EFG_PREFIX}Execution.Discrete.ConditionalContinuation":
        f"{EFG_PREFIX}Interface.Execution.Finite",
    f"{EFG_PREFIX}Execution.Discrete.ContinuationTruncation":
        f"{EFG_PREFIX}Interface.Execution.Finite",
    f"{EFG_PREFIX}Execution.Discrete.ObservedChance":
        f"{EFG_PREFIX}Interface.Execution.Finite",
    f"{EFG_PREFIX}Execution.FinitePayoff":
        f"{EFG_PREFIX}Interface.Execution.Finite",
    f"{EFG_PREFIX}Execution.FiniteCompletePath":
        f"{EFG_PREFIX}Interface.Execution.Finite",
    f"{EFG_PREFIX}Execution.Truncation":
        f"{EFG_PREFIX}Interface.Execution.Finite",
    f"{EFG_PREFIX}Observed.FinitePureNash":
        f"{EFG_PREFIX}Interface.Equilibrium.Discrete",
    f"{EFG_PREFIX}Observed.FiniteMeasureStrategy":
        f"{EFG_PREFIX}Interface.Equilibrium.Discrete",
}

ALGORITHM_FIRST_FORBIDDEN_LOCAL_MODULES = {
    f"{EFG_PREFIX}Execution.InfiniteTrajectory",
    "EconCSLib.Math.Probability.FiniteLaw.Measure",
    "EconCSLib.Math.Probability.Effective.Semantics",
    "EconCSLib.Math.Probability.Effective.UniformSemantics",
}

FORBIDDEN_LEGACY_ROOT_NAMES = {
    "IsDesignatedContinuationRoot",
    "legacyContinuationRootPresentation",
}

EMBEDDED_EXAMPLE_NAMESPACE_RE = re.compile(
    r"^namespace\s+Examples(?:\.|\s|$)",
    re.MULTILINE,
)

MOVED_EXAMPLE_DECLARATIONS = {
    f"{EFG_PREFIX}StochasticGameTree": {
        "fairCoinLaw",
        "fairCoinLaw_apply",
        "fairCoinLaw_total",
        "fairCoinGame",
        "fairCoin_expected_player0",
    },
}


@dataclass(frozen=True)
class StatusRow:
    module: str
    status: str
    responsibility: str
    recommended_import: str
    replacement: str
    may_grow: str
    action: str
    removal_policy: str


@dataclass(frozen=True)
class LeanLifecycle:
    zero_byte: set[str]
    comment_only: set[str]
    import_only: set[str]


def module_name(path: Path, root: Path) -> str | None:
    relative = path.relative_to(root)
    if relative == Path("EconCSLib.lean"):
        return "EconCSLib"
    if not relative.parts or relative.parts[0] != "EconCSLib":
        return None
    return ".".join(relative.with_suffix("").parts)


def module_path(module: str, root: Path) -> Path:
    if module == "EconCSLib":
        return root / "EconCSLib.lean"
    return root / Path(*module.split(".")).with_suffix(".lean")


def lean_lifecycle(root: Path) -> LeanLifecycle:
    """Classify source modules without treating module docstrings as code."""

    paths = [root / "EconCSLib.lean"]
    paths.extend((root / "EconCSLib").rglob("*.lean"))
    zero_byte: set[str] = set()
    comment_only: set[str] = set()
    import_only: set[str] = set()
    namespace_shell_re = re.compile(
        r"^\s*(?:namespace(?:\s+[A-Za-z0-9_.]+)?|"
        r"end(?:\s+[A-Za-z0-9_.]+)?)\s*$",
        re.MULTILINE,
    )
    for path in paths:
        if not path.is_file():
            continue
        module = module_name(path, root)
        if module is None:
            continue
        source = path.read_text(encoding="utf-8")
        if path.stat().st_size == 0:
            zero_byte.add(module)
        stripped = strip_lean_comments_and_strings(source)
        shell_residue = namespace_shell_re.sub("", stripped)
        if not shell_residue.strip():
            comment_only.add(module)
        imports = set(ANY_IMPORT_RE.findall(stripped))
        import_residue = ANY_IMPORT_RE.sub("", stripped)
        if imports and not import_residue.strip():
            import_only.add(module)
    return LeanLifecycle(zero_byte, comment_only, import_only)


def in_scope_modules(root: Path) -> set[str]:
    paths = list((root / "EconCSLib/GameTheory/ExtensiveGame").rglob("*.lean"))
    paths += [root / "EconCSLib/GameTheory/GameForm.lean"]
    paths += list((root / "EconCSLib/GameTheory/GameForm").rglob("*.lean"))
    paths += list((root / "EconCSLib/Math/Probability/PMF").rglob("*.lean"))
    paths += [root / "EconCSLib/Math/Probability/FiniteLaw.lean"]
    paths += list((root / "EconCSLib/Math/Probability/FiniteLaw").rglob("*.lean"))
    paths += [root / "EconCSLib/Math/Probability/Effective.lean"]
    paths += list((root / "EconCSLib/Math/Probability/Effective").rglob("*.lean"))
    paths += [root / "EconCSLib/Math/Probability/FiniteMarkovChain.lean"]
    paths += list(
        (root / "EconCSLib/Math/Probability/FiniteMarkovChain").rglob("*.lean")
    )
    paths += [root / "EconCSLib/Math/Probability/RationalIntervalUnion.lean"]
    paths += list(
        (root / "EconCSLib/Math/Probability/RationalIntervalUnion").rglob("*.lean")
    )
    return {
        name
        for path in paths
        if path.is_file() and (name := module_name(path, root)) is not None
    }


def read_status_rows(path: Path) -> tuple[dict[str, StatusRow], list[str]]:
    rows: dict[str, StatusRow] = {}
    errors: list[str] = []
    for line_no, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
        if not MODULE_ROW_RE.match(line):
            continue
        cells = [cell.strip() for cell in line.strip().strip("|").split("|")]
        if len(cells) != 8:
            errors.append(
                f"{path}:{line_no}: expected 8 module-table cells, found {len(cells)}"
            )
            continue
        module = cells[0].strip("`")
        if module in rows:
            errors.append(f"{path}:{line_no}: duplicate module row for {module}")
            continue
        rows[module] = StatusRow(module, *cells[1:])
    return rows, errors


def strip_lean_comments_and_strings(text: str) -> str:
    """Replace nested comments, line comments, strings, and chars with spaces."""

    output: list[str] = []
    index = 0
    block_depth = 0
    in_line_comment = False
    in_string = False
    in_char = False
    while index < len(text):
        char = text[index]
        next_char = text[index + 1] if index + 1 < len(text) else ""
        if in_line_comment:
            if char == "\n":
                in_line_comment = False
                output.append(char)
            else:
                output.append(" ")
            index += 1
        elif block_depth:
            if char == "/" and next_char == "-":
                block_depth += 1
                output.extend("  ")
                index += 2
            elif char == "-" and next_char == "/":
                block_depth -= 1
                output.extend("  ")
                index += 2
            else:
                output.append("\n" if char == "\n" else " ")
                index += 1
        elif in_string or in_char:
            delimiter = '"' if in_string else "'"
            if char == "\\" and next_char:
                output.extend("  ")
                index += 2
            elif char == delimiter:
                in_string = False
                in_char = False
                output.append(" ")
                index += 1
            else:
                output.append("\n" if char == "\n" else " ")
                index += 1
        elif char == "-" and next_char == "-":
            in_line_comment = True
            output.extend("  ")
            index += 2
        elif char == "/" and next_char == "-":
            block_depth = 1
            output.extend("  ")
            index += 2
        elif char == '"':
            in_string = True
            output.append(" ")
            index += 1
        elif char == "'":
            in_char = True
            output.append(" ")
            index += 1
        else:
            output.append(char)
            index += 1
    return "".join(output)


def semantic_compatibility_source_is_valid(source: str) -> bool:
    """A bridge proves an equality/representation certificate and owns no result data."""

    stripped = strip_lean_comments_and_strings(source)
    return (
        NONCOMPUTABLE_DATA_DECL_RE.search(stripped) is None
        and SEMANTIC_CERTIFICATE_THEOREM_RE.search(stripped) is not None
    )


def frozen_structure_digest(
    source: str, start_pattern: str, end_pattern: str
) -> str | None:
    """Hash one normalized top-level structure declaration.

    The end anchor is the namespace that immediately follows the declaration
    in its owner module. Returning `None` makes missing, renamed, duplicated,
    or relocated declarations an explicit governance failure.
    """

    stripped = strip_lean_comments_and_strings(source)
    start_matches = list(re.finditer(start_pattern, stripped, re.MULTILINE))
    if len(start_matches) != 1:
        return None
    start = start_matches[0]
    end_matches = list(
        re.finditer(end_pattern, stripped[start.end():], re.MULTILINE)
    )
    if not end_matches:
        return None
    declaration = stripped[
        start.start():start.end() + end_matches[0].start()
    ]
    normalized = " ".join(declaration.split())
    return hashlib.sha256(normalized.encode("utf-8")).hexdigest()


def controlled_carrier_universe_mapping_is_valid(source: str) -> bool:
    """Check both carrier universe mappings without freezing either record.

    `ControlledGame` exposes universes in player/action/state order.  The
    information-action family must therefore share `uA` with the base action
    fiber in `ControlledDecisionGame`, while the base state remains
    independently universe-polymorphic in `uS`. `ControlledObservedGame`
    must extend that decision carrier without permuting its universes.
    """

    stripped = strip_lean_comments_and_strings(source)
    starts = list(
        re.finditer(CONTROLLED_DECISION_START, stripped, re.MULTILINE)
    )
    if len(starts) != 1:
        return False
    start = starts[0]
    ends = list(
        re.finditer(
            CONTROLLED_DECISION_END,
            stripped[start.end():],
            re.MULTILINE,
        )
    )
    if not ends:
        return False
    declaration = stripped[
        start.start():start.end() + ends[0].start()
    ]
    base_mapping = re.findall(
        r"\bbase\s*:\s*ControlledGame\.\{\s*uN\s*,\s*uA\s*,\s*uS\s*\}\s*N\b",
        declaration,
    )
    info_action_mapping = re.findall(
        r"\bInfoAction\s*:\s*"
        r"\(i\s*:\s*N\)\s*→\s*InfoState\s+i\s*→\s*Type\s+uA\b",
        declaration,
    )
    observed_starts = list(
        re.finditer(CONTROLLED_OBSERVED_START, stripped, re.MULTILINE)
    )
    observed_extends = list(
        re.finditer(CONTROLLED_OBSERVED_EXTENDS, stripped, re.MULTILINE)
    )
    return (
        len(base_mapping) == 1
        and len(info_action_mapping) == 1
        and len(observed_starts) == 1
        and len(observed_extends) == 1
        and observed_extends[0].start() >= observed_starts[0].end()
    )


def local_import_graph(root: Path) -> tuple[dict[str, set[str]], list[str]]:
    graph: dict[str, set[str]] = {}
    errors: list[str] = []
    # Traverse only repository-owned Lean sources. Filtering `.lake` after a
    # repository-wide `rglob` is too late: the glob has already descended into
    # Mathlib and every cached dependency before the filter sees each path.
    paths = [root / "EconCSLib.lean"]
    paths.extend((root / "EconCSLib").rglob("*.lean"))
    for path in paths:
        if not path.is_file():
            continue
        module = module_name(path, root)
        if module is None:
            continue
        imports = set(IMPORT_RE.findall(path.read_text(encoding="utf-8")))
        graph[module] = imports
    for importer, imports in graph.items():
        for imported in imports:
            if imported.startswith("EconCSLib") and imported not in graph:
                errors.append(
                    f"{module_path(importer, root)}: unresolved local import {imported}"
                )
    return graph, errors


def closure(graph: dict[str, set[str]], entry: str) -> set[str]:
    visited: set[str] = set()
    pending = list(graph[entry])
    while pending:
        module = pending.pop()
        if module in visited or module not in graph:
            continue
        visited.add(module)
        pending.extend(graph[module])
    return visited


def import_cycle(
    graph: dict[str, set[str]], modules: set[str]
) -> list[str] | None:
    """Return one in-scope import cycle, including the repeated endpoint."""

    state: dict[str, int] = {}
    path: list[str] = []

    def visit(module: str) -> list[str] | None:
        state[module] = 1
        path.append(module)
        for imported in sorted(graph.get(module, set())):
            if imported not in modules:
                continue
            if state.get(imported, 0) == 1:
                start = path.index(imported)
                return path[start:] + [imported]
            if state.get(imported, 0) == 0:
                found = visit(imported)
                if found is not None:
                    return found
        path.pop()
        state[module] = 2
        return None

    for module in sorted(modules):
        if state.get(module, 0) == 0:
            found = visit(module)
            if found is not None:
                return found
    return None


def compatibility_import_allowed(importer: str, rows: dict[str, StatusRow]) -> bool:
    if (
        rows.get(importer, StatusRow("", "", "", "", "", "", "", "")).status
        == "Compatibility"
    ):
        return True
    return (
        importer.startswith("EconCSLib.Examples.ExtensiveGame.")
        and importer.endswith("ImportBoundary")
    )


def efg_documentation_paths(root: Path) -> list[Path]:
    """Return the documentation set governed by the EFG authority inventory."""

    design = root / "docs/design"
    paths = [
        root / "docs/design.md",
        design / "README.md",
        design / "extensive_game.md",
    ]
    paths.extend(design.glob("efg-*.md"))
    return sorted({path for path in paths if path.is_file()})


def documentation_link_errors(paths: list[Path]) -> list[str]:
    """Check repository-local Markdown link targets in the governed docs."""

    errors: list[str] = []
    for path in paths:
        source = path.read_text(encoding="utf-8")
        for raw_target in MARKDOWN_LINK_RE.findall(source):
            target = raw_target.strip()
            if target.startswith("<") and target.endswith(">"):
                target = target[1:-1]
            if (
                not target
                or target.startswith("#")
                or re.match(r"^[A-Za-z][A-Za-z0-9+.-]*:", target)
            ):
                continue
            target = unquote(target.split("#", 1)[0].split("?", 1)[0])
            resolved = (
                Path(target)
                if Path(target).is_absolute()
                else path.parent / target
            )
            if not resolved.exists():
                errors.append(f"{path}: unresolved local Markdown link {raw_target}")
    return errors


def large_efg_line_band(line_count: int) -> str:
    """Return the stable maintenance band for an audited large EFG module."""

    if line_count >= 1200:
        return "1200+"
    if line_count >= 1000:
        return "1000-1199"
    if line_count >= LARGE_EFG_LINE_THRESHOLD:
        return "800-999"
    raise ValueError(f"line count {line_count} is below the audit threshold")


def current_large_efg_modules(root: Path) -> dict[str, str]:
    """Return every EFG source at or above the governed line threshold."""

    result: dict[str, str] = {}
    efg_root = root / "EconCSLib/GameTheory/ExtensiveGame"
    for path in efg_root.rglob("*.lean"):
        line_count = len(path.read_text(encoding="utf-8").splitlines())
        if line_count < LARGE_EFG_LINE_THRESHOLD:
            continue
        module = module_name(path, root)
        if module is not None:
            result[module] = large_efg_line_band(line_count)
    return result


def documented_large_efg_modules(
    source: str,
) -> tuple[dict[str, str], set[str]]:
    """Read machine-audited module/band rows and report duplicate modules."""

    result: dict[str, str] = {}
    duplicates: set[str] = set()
    for module, band in LARGE_MODULE_ROW_RE.findall(source):
        if module in result:
            duplicates.add(module)
        result[module] = band
    return result, duplicates


def run(root: Path) -> list[str]:
    errors: list[str] = []
    status_path = root / "docs/design/efg-module-status.md"
    governance_path = root / "docs/design/efg-governance.md"
    governance_source = governance_path.read_text(encoding="utf-8")
    rows, row_errors = read_status_rows(status_path)
    errors.extend(row_errors)

    scoped = in_scope_modules(root)
    registered = set(rows)
    for module in sorted(scoped - registered):
        errors.append(f"{status_path}: missing module row for {module}")
    for module in sorted(registered - scoped):
        errors.append(f"{status_path}: row has no in-scope source module: {module}")

    status_source = status_path.read_text(encoding="utf-8")
    actual_status_counts = {
        status: sum(row.status == status for row in rows.values())
        for status in {
            "Canonical",
            "Frontend",
            "Historical",
            "Compatibility",
            "Experimental",
            "Internal",
        }
    }
    documented_status_counts = {
        status: int(count)
        for status, count in STATUS_SUMMARY_ROW_RE.findall(status_source)
    }
    if documented_status_counts != actual_status_counts:
        errors.append(
            f"{status_path}: lifecycle summary differs from module rows; "
            f"documented={documented_status_counts}, "
            f"actual={actual_status_counts}"
        )
    if f"contains {len(rows)} modules" not in status_source:
        errors.append(
            f"{status_path}: census prose must contain the checked total "
            f"`contains {len(rows)} modules`"
        )
    if f"| **Total** | **{len(rows)}** |" not in status_source:
        errors.append(
            f"{status_path}: lifecycle summary must contain checked total "
            f"{len(rows)}"
        )

    graph, graph_errors = local_import_graph(root)
    errors.extend(graph_errors)
    documentation_paths = efg_documentation_paths(root)
    errors.extend(documentation_link_errors(documentation_paths))
    for path in documentation_paths:
        source = path.read_text(encoding="utf-8")
        for referenced in FULL_MODULE_REFERENCE_RE.findall(source):
            normalized = (
                referenced.removesuffix(".lean")
                if referenced.endswith(".lean")
                else referenced
            )
            if (
                normalized not in graph
                and not any(
                    module.startswith(f"{normalized}.") for module in graph
                )
            ):
                errors.append(
                    f"{path}: recorded full module name does not resolve: "
                    f"{referenced}"
                )

    actual_large_modules = current_large_efg_modules(root)
    audited_large_modules, duplicate_large_modules = (
        documented_large_efg_modules(governance_source)
    )
    if duplicate_large_modules or audited_large_modules != actual_large_modules:
        missing = sorted(actual_large_modules.keys() - audited_large_modules.keys())
        stale = sorted(audited_large_modules.keys() - actual_large_modules.keys())
        wrong_band = {
            module: (audited_large_modules[module], actual_large_modules[module])
            for module in sorted(
                actual_large_modules.keys() & audited_large_modules.keys()
            )
            if audited_large_modules[module] != actual_large_modules[module]
        }
        errors.append(
            f"{governance_path}: large-file audit differs from the current "
            f">={LARGE_EFG_LINE_THRESHOLD}-line inventory; missing={missing}, "
            f"stale={stale}, duplicates={sorted(duplicate_large_modules)}, "
            f"wrong_band={wrong_band}"
        )
    cycle = import_cycle(graph, scoped)
    if cycle is not None:
        errors.append("local import graph contains a cycle: " + " -> ".join(cycle))

    for name, contract in FROZEN_MINIMAL_CORE_STRUCTURES.items():
        module, start_pattern, end_pattern, expected_digest = contract
        path = module_path(module, root)
        if not path.is_file():
            errors.append(
                f"{path}: frozen minimal-core owner for {name} is missing"
            )
            continue
        actual_digest = frozen_structure_digest(
            path.read_text(encoding="utf-8"),
            start_pattern,
            end_pattern,
        )
        if actual_digest is None:
            errors.append(
                f"{path}: frozen minimal-core structure {name} is missing, "
                "duplicated, renamed, or moved from its governed declaration "
                "boundary"
            )
        elif actual_digest != expected_digest:
            errors.append(
                f"{path}: frozen minimal-core structure {name} changed "
                f"(expected {expected_digest}, found {actual_digest}); "
                "represent new semantics with an external certificate, "
                "adapter, relation, or compiler, or explicitly revise the "
                "freeze contract in architectural review"
            )

    controlled_observed_path = module_path(
        CONTROLLED_OBSERVED_MODULE, root
    )
    if (
        not controlled_observed_path.is_file()
        or not controlled_carrier_universe_mapping_is_valid(
            controlled_observed_path.read_text(encoding="utf-8")
        )
    ):
        errors.append(
            f"{controlled_observed_path}: ControlledDecisionGame must map "
            "ControlledGame universes as player/action/state "
            "`.{uN, uA, uS}`, keep `InfoAction` in `Type uA`, and "
            "ControlledObservedGame must extend it as "
            "`.{uN, uA, uS, uI}`; this narrow regression guard does not "
            "freeze either carrier"
        )

    lifecycle = lean_lifecycle(root)
    for module in sorted(lifecycle.zero_byte):
        errors.append(
            f"{module_path(module, root)}: zero-byte Lean modules are forbidden"
        )
    for module in sorted(lifecycle.comment_only - lifecycle.zero_byte):
        errors.append(
            f"{module_path(module, root)}: comment/namespace-only Lean module "
            "has no registered lifecycle role"
        )

    expected_import_only = (
        CANONICAL_IMPORT_ONLY_MODULES
        | TEMPORARY_COMPATIBILITY_IMPORT_ONLY_MODULES
    )
    for module in sorted(lifecycle.import_only - expected_import_only):
        errors.append(
            f"{module_path(module, root)}: import-only Lean module is not "
            "registered as a canonical facade or temporary compatibility path"
        )
    for module in sorted(expected_import_only - lifecycle.import_only):
        errors.append(
            f"{module_path(module, root)}: registered import-only module is "
            "missing or contains non-import source"
        )
    for module in sorted(CANONICAL_IMPORT_ONLY_MODULES):
        row = rows.get(module)
        if row is not None and row.status != "Canonical":
            errors.append(
                f"{status_path}: canonical import-only facade {module} must "
                f"be registered Canonical, found {row.status}"
            )

    for removed in sorted(REMOVED_MODULE_PATHS):
        if removed in graph or module_path(removed, root).exists():
            errors.append(f"removed module path was recreated: {removed}")
        for importer, imports in graph.items():
            if removed in imports:
                errors.append(
                    f"{module_path(importer, root)}: imports removed module "
                    f"path {removed}"
                )

    for pair, reason in HISTORICAL_IMPORT_ALLOWLIST.items():
        importer, imported = pair
        if not reason.strip():
            errors.append(
                "historical import allowlist entry must include a reason: "
                f"{importer} -> {imported}"
            )
        if imported not in graph.get(importer, set()):
            errors.append(
                "stale historical import allowlist entry: "
                f"{importer} -> {imported}"
            )
        if rows.get(imported) is None or rows[imported].status != "Historical":
            errors.append(
                "historical import allowlist target is not registered Historical: "
                f"{imported}"
            )

    protected_importers = {"Canonical", "Frontend", "Internal"}
    for importer, imports in graph.items():
        importer_row = rows.get(importer)
        if importer_row is None or importer_row.status not in protected_importers:
            continue
        for imported in sorted(imports):
            imported_row = rows.get(imported)
            if (
                imported_row is not None
                and imported_row.status == "Historical"
                and (importer, imported) not in HISTORICAL_IMPORT_ALLOWLIST
            ):
                errors.append(
                    f"{module_path(importer, root)}: {importer_row.status} module "
                    f"imports Historical module {imported} without an exact "
                    "allowlist entry"
                )

    for (importer, imported), reason in FORBIDDEN_DIRECT_IMPORTS.items():
        if imported in graph.get(importer, set()):
            errors.append(
                f"{module_path(importer, root)}: forbidden direct import "
                f"{imported} ({reason})"
            )

    execution_prefix = f"{EFG_PREFIX}Execution."
    relations_prefix = f"{EFG_PREFIX}Relations."
    for importer, imports in graph.items():
        if not importer.startswith(execution_prefix):
            continue
        for imported in sorted(imports):
            if imported.startswith(relations_prefix):
                errors.append(
                    f"{module_path(importer, root)}: neutral execution module "
                    f"must not import relation owner {imported}; place "
                    "naturality/preservation theorems on the relation side"
                )

    for entry in sorted(PAYOFF_FREE_CORE_BOUNDARIES):
        if entry not in graph:
            errors.append(f"missing payoff-free boundary module: {entry}")
            continue
        imported = closure(graph, entry)
        for module in sorted(imported):
            if (
                module in FORBIDDEN_PAYOFF_FREE_CLOSURE_MODULES
                or module.startswith(FORBIDDEN_PAYOFF_FREE_CLOSURE_PREFIXES)
            ):
                errors.append(
                    f"{module_path(entry, root)}: payoff-free closure reaches "
                    f"forbidden downstream module {module}"
                )

    maximum_law_path = module_path(MAXIMUM_PATH_LAW_MODULE, root)
    maximum_law_source = strip_lean_comments_and_strings(
        maximum_law_path.read_text(encoding="utf-8")
    )
    for name in sorted(MAXIMUM_PATH_LAW_FORBIDDEN_NAMES):
        if re.search(rf"\b{re.escape(name)}\b", maximum_law_source):
            errors.append(
                f"{maximum_law_path}: maximum path-law interface contains "
                f"forbidden discrete/payoff-aware name {name}"
            )
    for required in ("pathLaw_isProbability", "pathLaw_ae_legal"):
        if not re.search(rf"\b{required}\b", maximum_law_source):
            errors.append(
                f"{maximum_law_path}: lawful probability carrier is missing "
                f"required field {required}"
            )

    maximum_law_closure = closure(graph, MAXIMUM_PATH_LAW_MODULE)
    leaked_path_law_producers = maximum_law_closure & {
        DISCRETE_PATH_LAW_ADAPTER,
        ANALYTIC_PATH_LAW_ADAPTER,
    }
    if leaked_path_law_producers:
        errors.append(
            f"{maximum_law_path}: common path-law carrier depends on concrete "
            "producer adapter(s): "
            + ", ".join(sorted(leaked_path_law_producers))
        )

    for entry, (required, forbidden) in SEMANTIC_REGIME_ROUTE_CONTRACTS.items():
        if entry not in graph:
            errors.append(f"missing semantic-regime route module: {entry}")
            continue
        imported = closure(graph, entry)
        missing = sorted(required - imported)
        leaked = sorted(forbidden & imported)
        if missing or leaked:
            errors.append(
                f"{module_path(entry, root)}: semantic-regime route differs; "
                f"missing={missing}, forbidden={leaked}"
            )

    for bridge, (executable_owners, facade) in (
        SEMANTIC_COMPATIBILITY_BRIDGES.items()
    ):
        if bridge not in graph:
            errors.append(f"missing semantic-compatibility bridge: {bridge}")
            continue
        bridge_closure = closure(graph, bridge)
        missing_owners = sorted(executable_owners - bridge_closure)
        if missing_owners:
            errors.append(
                f"{module_path(bridge, root)}: semantic-compatibility bridge "
                f"does not reach executable owner(s): {missing_owners}"
            )
        if facade not in graph or bridge not in closure(graph, facade):
            errors.append(
                f"{module_path(bridge, root)}: semantic-compatibility bridge "
                f"is not exposed by {facade}"
            )
        for owner in sorted(executable_owners):
            if owner not in graph:
                errors.append(
                    f"missing semantic-compatibility executable owner: {owner}"
                )
            elif bridge in closure(graph, owner):
                errors.append(
                    f"{module_path(owner, root)}: executable owner depends on "
                    f"semantic-compatibility bridge {bridge}"
                )
        bridge_source = module_path(bridge, root).read_text(encoding="utf-8")
        if not semantic_compatibility_source_is_valid(bridge_source):
            errors.append(
                f"{module_path(bridge, root)}: semantic-compatibility bridge "
                "must contain an `_eq_` or `_represents` certificate theorem "
                "and no noncomputable data declaration"
            )

    for owner, facade in ALGORITHM_FIRST_EXECUTABLE_OWNERS.items():
        if owner not in graph:
            errors.append(f"missing algorithm-first executable owner: {owner}")
            continue
        owner_closure = closure(graph, owner)
        leaked = sorted(
            module
            for module in owner_closure
            if module in ALGORITHM_FIRST_FORBIDDEN_LOCAL_MODULES
            or module.startswith(f"{EFG_PREFIX}Simulation.")
        )
        if leaked:
            errors.append(
                f"{module_path(owner, root)}: algorithm-first owner reaches "
                f"analytic module(s): {leaked}"
            )
        if facade not in graph or owner not in closure(graph, facade):
            errors.append(
                f"{module_path(owner, root)}: algorithm-first owner is not "
                f"exposed by {facade}"
            )
        owner_source = module_path(owner, root).read_text(encoding="utf-8")
        owner_stripped = strip_lean_comments_and_strings(owner_source)
        if NONCOMPUTABLE_DATA_DECL_RE.search(owner_stripped):
            errors.append(
                f"{module_path(owner, root)}: algorithm-first owner contains "
                "a noncomputable data declaration"
            )
        direct_imports = set(ANY_IMPORT_RE.findall(owner_source))
        measure_imports = sorted(
            imported
            for imported in direct_imports
            if imported.startswith("Mathlib.MeasureTheory")
        )
        if measure_imports:
            errors.append(
                f"{module_path(owner, root)}: algorithm-first owner directly "
                f"imports measure theory: {measure_imports}"
            )

    for module in sorted(scoped):
        path = module_path(module, root)
        stripped = strip_lean_comments_and_strings(
            path.read_text(encoding="utf-8")
        )
        if EMBEDDED_EXAMPLE_NAMESPACE_RE.search(stripped):
            errors.append(
                f"{path}: reusable library modules must not declare under "
                "the Examples namespace; move the regression to "
                "EconCSLib/Examples"
            )
        for name in sorted(FORBIDDEN_LEGACY_ROOT_NAMES):
            if re.search(rf"\b{re.escape(name)}\b", stripped):
                errors.append(
                    f"{path}: forbidden legacy continuation-root API {name}; "
                    "pass RootPresentation or a lawful subgame system explicitly"
                )
        for name in sorted(MOVED_EXAMPLE_DECLARATIONS.get(module, set())):
            if re.search(rf"\b{re.escape(name)}\b", stripped):
                errors.append(
                    f"{path}: example-only declaration {name} must remain "
                    "under EconCSLib/Examples"
                )

    compatibility = {
        module for module, row in rows.items() if row.status == "Compatibility"
    }
    if compatibility != TEMPORARY_COMPATIBILITY_IMPORT_ONLY_MODULES:
        errors.append(
            f"{status_path}: temporary compatibility registry differs; "
            f"status={sorted(compatibility)}, "
            "governance="
            f"{sorted(TEMPORARY_COMPATIBILITY_IMPORT_ONLY_MODULES)}"
        )
    for module in sorted(compatibility):
        path = module_path(module, root)
        source = path.read_text(encoding="utf-8")
        stripped = strip_lean_comments_and_strings(source)
        if DECLARATION_RE.search(stripped):
            errors.append(f"{path}: compatibility module defines a declaration")
        residue = ANY_IMPORT_RE.sub("", stripped)
        if residue.strip():
            errors.append(f"{path}: compatibility module must contain only imports")
        row = rows[module]
        if row.action != "Thin wrapper":
            errors.append(f"{status_path}: {module} action must be Thin wrapper")
        if not row.replacement or row.replacement == "—":
            errors.append(f"{status_path}: {module} must name a replacement")

    for importer, imports in graph.items():
        imported_compatibility = imports & compatibility
        if imported_compatibility and not compatibility_import_allowed(importer, rows):
            joined = ", ".join(sorted(imported_compatibility))
            errors.append(
                f"{module_path(importer, root)}: implementation imports "
                f"compatibility aggregate(s): {joined}"
            )

    for entry, expected in EXPECTED_CLOSURES.items():
        if entry not in graph:
            errors.append(f"missing facade or aggregate module: {entry}")
            continue
        imported = closure(graph, entry)
        actual = (
            sum(module.startswith(EFG_PREFIX) for module in imported),
            len(imported),
        )
        if actual != expected:
            errors.append(
                f"{module_path(entry, root)}: closure is {actual[0]} EFG / "
                f"{actual[1]} local; expected {expected[0]} / {expected[1]}"
            )
        label = GOVERNANCE_CLOSURE_LABELS[entry]
        documented_row = f"| `{label}` | {expected[0]} / {expected[1]} |"
        if documented_row not in governance_source:
            errors.append(
                f"{governance_path}: missing exact governed closure row "
                f"{documented_row}"
            )

    for entry, expected in EXPECTED_EXACT_EFG_CLOSURES.items():
        if entry not in graph:
            errors.append(f"missing exact-closure boundary module: {entry}")
            continue
        actual = {
            module
            for module in closure(graph, entry)
            if module.startswith(EFG_PREFIX)
        }
        if actual != expected:
            missing = sorted(expected - actual)
            extra = sorted(actual - expected)
            errors.append(
                f"{module_path(entry, root)}: exact EFG closure differs; "
                f"missing={missing}, extra={extra}"
            )

    for aggregate, expected_imports in EXPECTED_CONTROLLED_AGGREGATE_IMPORTS.items():
        actual_imports = graph.get(aggregate)
        if actual_imports is None:
            errors.append(f"missing controlled aggregate facade: {aggregate}")
        elif actual_imports != expected_imports:
            errors.append(
                f"{module_path(aggregate, root)}: direct imports differ from "
                f"the aggregate contract; expected={sorted(expected_imports)}, "
                f"actual={sorted(actual_imports)}"
            )
        source = module_path(aggregate, root).read_text(encoding="utf-8")
        if (
            "canonical aggregate facade" not in source
            or "owns no declarations" not in source
        ):
            errors.append(
                f"{module_path(aggregate, root)}: controlled aggregate "
                "module docstring must identify a canonical aggregate facade "
                "that owns no declarations"
            )

    for aggregate, expected_imports in EXPECTED_EFFECTIVE_AGGREGATE_IMPORTS.items():
        actual_imports = graph.get(aggregate)
        if actual_imports is None:
            errors.append(f"missing effective-probability aggregate: {aggregate}")
        elif actual_imports != expected_imports:
            errors.append(
                f"{module_path(aggregate, root)}: direct imports differ from "
                "the effective-probability aggregate contract; "
                f"expected={sorted(expected_imports)}, "
                f"actual={sorted(actual_imports)}"
            )

    controlled_root = f"{EFG_PREFIX}Observed.Controlled"
    actual_controlled_modules = {
        module
        for module in scoped
        if module == controlled_root or module.startswith(f"{controlled_root}.")
    }
    expected_controlled_modules = set(CONTROLLED_MODULE_ROLES)
    if actual_controlled_modules != expected_controlled_modules:
        missing = sorted(expected_controlled_modules - actual_controlled_modules)
        extra = sorted(actual_controlled_modules - expected_controlled_modules)
        errors.append(
            "Observed.Controlled hierarchy differs from its governed role map; "
            f"missing={missing}, extra={extra}"
        )

    unexpected_flat_controlled_siblings = {
        module
        for module in scoped
        if module.startswith(controlled_root)
        and module != controlled_root
        and not module.startswith(f"{controlled_root}.")
    }
    if unexpected_flat_controlled_siblings:
        errors.append(
            "legacy flat Observed.Controlled* sibling modules are forbidden; "
            "move them under Observed.Controlled: "
            + ", ".join(sorted(unexpected_flat_controlled_siblings))
        )

    expected_status_for_controlled_role = {
        "carrier": "Canonical",
        "canonical-semantic-owner": "Canonical",
        "canonical-responsibility-owner": "Canonical",
        "aggregate-facade": "Canonical",
        "payoff-aware-adapter": "Internal",
    }
    for module, role in sorted(CONTROLLED_MODULE_ROLES.items()):
        row = rows.get(module)
        expected_status = expected_status_for_controlled_role[role]
        if row is None:
            errors.append(f"{status_path}: missing controlled role row for {module}")
        elif row.status != expected_status:
            errors.append(
                f"{status_path}: {module} has role {role} and must be "
                f"registered {expected_status}, found {row.status}"
            )

    payoff_aware_adapters = set(EXPECTED_PAYOFF_AWARE_ADAPTER_IMPORTS)
    for adapter, expected_imports in EXPECTED_PAYOFF_AWARE_ADAPTER_IMPORTS.items():
        actual_imports = graph.get(adapter)
        if actual_imports is None:
            errors.append(f"missing controlled payoff-aware adapter: {adapter}")
            continue
        if actual_imports != expected_imports:
            errors.append(
                f"{module_path(adapter, root)}: direct imports differ from "
                f"the payoff-aware adapter contract; "
                f"expected={sorted(expected_imports)}, "
                f"actual={sorted(actual_imports)}"
            )
        source = strip_lean_comments_and_strings(
            module_path(adapter, root).read_text(encoding="utf-8")
        )
        namespace = EXPECTED_PAYOFF_AWARE_ADAPTER_NAMESPACES[adapter]
        if not re.search(
            rf"^namespace\s+{re.escape(namespace)}\s*$",
            source,
            re.MULTILINE,
        ):
            errors.append(
                f"{module_path(adapter, root)}: payoff-aware adapter must "
                f"declare only under namespace {namespace}"
            )
        if re.search(
            r"^namespace\s+ExtensiveGame\.(?:ControlledObservedGame|"
            r"DiscreteControlledObservedChanceGame)\b",
            source,
            re.MULTILINE,
        ):
            errors.append(
                f"{module_path(adapter, root)}: payoff-aware adapter reopens "
                "a payoff-free controlled owner namespace"
            )
        if not DECLARATION_RE.search(source):
            errors.append(
                f"{module_path(adapter, root)}: payoff-aware adapter contains "
                "no adapter declaration"
            )

    for owner in sorted(CONTROLLED_CANONICAL_OWNERS):
        if owner not in graph:
            errors.append(f"missing controlled canonical owner: {owner}")
            continue
        leaked_adapters = closure(graph, owner) & payoff_aware_adapters
        if leaked_adapters:
            errors.append(
                f"{module_path(owner, root)}: controlled canonical owner "
                "depends on downstream payoff-aware adapter(s): "
                + ", ".join(sorted(leaked_adapters))
            )

    structural_core_closure = closure(graph, STRUCTURAL_CORE)
    structural_core_efg_closure = {
        module
        for module in structural_core_closure
        if module.startswith(EFG_PREFIX)
    }
    if structural_core_efg_closure != EXPECTED_STRUCTURAL_CORE_EFG_CLOSURE:
        missing = sorted(
            EXPECTED_STRUCTURAL_CORE_EFG_CLOSURE - structural_core_efg_closure
        )
        extra = sorted(
            structural_core_efg_closure - EXPECTED_STRUCTURAL_CORE_EFG_CLOSURE
        )
        errors.append(
            f"{module_path(STRUCTURAL_CORE, root)}: structural EFG closure "
            f"differs from the exact five-module boundary; missing={missing}, "
            f"extra={extra}"
        )

    core_module = f"{EFG_PREFIX}Interface.Core"
    core_closure = closure(graph, core_module)
    for module in sorted(core_closure):
        if (
            module in CORE_FORBIDDEN_CLOSURE_MODULES
            or module.startswith(CORE_FORBIDDEN_CLOSURE_PREFIXES)
        ):
            errors.append(
                f"{module_path(core_module, root)}: Foundation Facade closure "
                f"reaches forbidden objective/winning module {module}"
            )

    root_imports = graph.get("EconCSLib", set())
    actual_root_efg_imports = {
        module for module in root_imports if module.startswith(EFG_PREFIX)
    }
    if actual_root_efg_imports != EXPECTED_ROOT_EFG_IMPORTS:
        errors.append(
            "EconCSLib.lean: direct EFG imports differ from the governed "
            f"finite root: {sorted(actual_root_efg_imports)}"
        )

    root_closure = closure(graph, "EconCSLib")
    for module in sorted(root_closure):
        row = rows.get(module)
        if row is not None and row.status in {"Historical", "Compatibility"}:
            errors.append(
                f"EconCSLib.lean: root closure contains {row.status} module {module}"
            )
    for module in sorted(root_closure & FORBIDDEN_ROOT_MODULES):
        errors.append(f"EconCSLib.lean: forbidden root dependency {module}")
    for module in sorted(root_closure):
        if module.startswith(
            (
                f"{EFG_PREFIX}Compiler.",
                f"{EFG_PREFIX}FOSG.",
                f"{EFG_PREFIX}Simulation.",
            )
        ):
            errors.append(f"EconCSLib.lean: forbidden root dependency {module}")

    restart = closure(graph, f"{EFG_PREFIX}Interface.Restart")
    compilation = closure(graph, f"{EFG_PREFIX}Interface.Compilation.Discrete")
    if any(module.startswith(f"{EFG_PREFIX}Interface.Compilation") for module in restart):
        errors.append("Interface.Restart must not depend on Compilation")
    if any(module == f"{EFG_PREFIX}Interface.Restart" for module in compilation):
        errors.append("Interface.Compilation.Discrete must not depend on Restart")

    probability_modules = {
        module
        for module in graph
        if module == "EconCSLib.Math.Probability.FiniteLaw"
        or module.startswith("EconCSLib.Math.Probability.FiniteLaw.")
        or module == "EconCSLib.Math.Probability.Effective"
        or module.startswith("EconCSLib.Math.Probability.Effective.")
        or module == "EconCSLib.Math.Probability.FiniteMarkovChain"
        or module.startswith("EconCSLib.Math.Probability.FiniteMarkovChain.")
        or module == "EconCSLib.Math.Probability.RationalIntervalUnion"
        or module.startswith("EconCSLib.Math.Probability.RationalIntervalUnion.")
        or module == "EconCSLib.Math.Probability.PMF"
        or module.startswith("EconCSLib.Math.Probability.PMF.")
    }
    for module in sorted(probability_modules):
        for imported in sorted(graph[module]):
            if imported.startswith("EconCSLib.GameTheory."):
                errors.append(
                    f"{module_path(module, root)}: reusable probability layer "
                    f"imports {imported}"
                )

    for importer, imports in graph.items():
        if (
            importer in {"EconCSLib.Examples", "EconCSLib.OpenProblem"}
            or importer.startswith(
                ("EconCSLib.Examples.", "EconCSLib.OpenProblem.")
            )
        ):
            continue
        for imported in imports:
            if imported.startswith(
                ("EconCSLib.Examples.", "EconCSLib.OpenProblem.")
            ):
                errors.append(
                    f"{module_path(importer, root)}: stable source imports {imported}"
                )

    for old, new in MOVED_PATHS.items():
        if old in graph or module_path(old, root).exists():
            errors.append(f"obsolete internal module path still exists: {old}")
        if new not in graph:
            errors.append(f"moved internal module is missing: {new}")

    for module in sorted(scoped):
        source = module_path(module, root).read_text(encoding="utf-8")
        for name in DEPRECATED_RE.findall(source):
            errors.append(
                f"{module_path(module, root)}: deprecated EFG declaration "
                f"{name} is forbidden during pre-stability; hard-migrate "
                "zero-consumer aliases or revise the stability policy"
            )

    simulation_count = sum(
        module.startswith(f"{EFG_PREFIX}Simulation.") for module in scoped
    )
    if simulation_count != 40:
        errors.append(
            f"Simulation module count is {simulation_count}; expected governed count 40"
        )

    return errors


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--root",
        type=Path,
        default=Path(__file__).resolve().parent.parent,
        help="repository root (defaults to the script's parent repository)",
    )
    args = parser.parse_args()
    root = args.root.resolve()
    errors = run(root)
    if errors:
        for error in errors:
            print(f"EFG governance error: {error}", file=sys.stderr)
        return 1

    rows, _ = read_status_rows(root / "docs/design/efg-module-status.md")
    graph, _ = local_import_graph(root)
    root_imported = closure(graph, "EconCSLib")
    root_counts = (
        sum(module.startswith(EFG_PREFIX) for module in root_imported),
        len(root_imported),
    )
    compatibility_count = sum(
        row.status == "Compatibility" for row in rows.values()
    )
    simulation_count = sum(
        module.startswith(f"{EFG_PREFIX}Simulation.") for module in rows
    )
    controlled_role_counts = {
        role: sum(
            registered_role == role
            for registered_role in CONTROLLED_MODULE_ROLES.values()
        )
        for role in {
            "carrier",
            "canonical-semantic-owner",
            "canonical-responsibility-owner",
            "aggregate-facade",
            "payoff-aware-adapter",
        }
    }
    large_module_count = len(current_large_efg_modules(root))
    print(
        f"EFG governance checks passed: {len(rows)} registered modules, "
        f"{compatibility_count} temporary compatibility paths, "
        f"root {root_counts[0]}/{root_counts[1]}, "
        f"Simulation {simulation_count}, Controlled hierarchy "
        f"{len(CONTROLLED_MODULE_ROLES)}="
        f"{controlled_role_counts['carrier']} carrier/"
        f"{controlled_role_counts['canonical-semantic-owner']} semantic owners/"
        f"{controlled_role_counts['canonical-responsibility-owner']} "
        "responsibility owners/"
        f"{controlled_role_counts['aggregate-facade']} facades/"
        f"{controlled_role_counts['payoff-aware-adapter']} adapters, "
        "minimal-core compatibility freeze deferred, "
        "1 carrier-universe regression guard, "
        f"{len(SEMANTIC_REGIME_ROUTE_CONTRACTS)} semantic-regime route guards, "
        f"{len(SEMANTIC_COMPATIBILITY_BRIDGES)} semantic-compatibility bridges, "
        f"{len(ALGORITHM_FIRST_EXECUTABLE_OWNERS)} algorithm-first owners, "
        f"{large_module_count} large-module audit rows."
    )
    lifecycle = lean_lifecycle(root)
    canonical_import_only = (
        lifecycle.import_only & CANONICAL_IMPORT_ONLY_MODULES
    )
    temporary_import_only = (
        lifecycle.import_only
        & TEMPORARY_COMPATIBILITY_IMPORT_ONLY_MODULES
    )

    def names(modules: set[str]) -> str:
        return ", ".join(sorted(modules)) if modules else "(none)"

    print(
        f"Zero-byte Lean modules ({len(lifecycle.zero_byte)}): "
        f"{names(lifecycle.zero_byte)}"
    )
    print(
        f"Comment/namespace-only Lean modules "
        f"({len(lifecycle.comment_only)}): "
        f"{names(lifecycle.comment_only)}"
    )
    print(
        f"Canonical import-only modules ({len(canonical_import_only)}): "
        f"{names(canonical_import_only)}"
    )
    print(
        f"Temporary compatibility import-only modules "
        f"({len(temporary_import_only)}): "
        f"{names(temporary_import_only)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
