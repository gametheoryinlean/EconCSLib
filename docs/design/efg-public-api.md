# EFG Canonical Facades and Reuse Policy

This note defines the supported import surface for the simulation-oriented
extensive-game framework. It complements
[`extensive_game.md`](extensive_game.md); the Lean source remains
authoritative.

New readers should first use the conceptual route and finite worked-example
route in `extensive_game.md`. This file is the second step: choose the smallest
facade only after identifying the semantic branch the model needs.

Lifecycle and placement decisions are governed by
[`efg-governance.md`](efg-governance.md).  The status, responsibility,
recommended import, growth permission, and removal policy for every in-scope
module are registered in
[`efg-module-status.md`](efg-module-status.md).

## Pre-stability import classes

The EFG surface has two support classes:

- **Canonical pre-stability facade**: `Interface.StructuralCore`,
  `Interface.Core`,
  `Interface.Objective`,
  `Interface.Winning`, `Interface.Winning.Stochastic`,
  `Interface.Execution.{Finite,Infinite,Analytic}`,
  `Interface.Relations.Discrete`, `Interface.Preservation`,
  `Interface.Equilibrium.{Discrete,Analytic}`, `Interface.Restart`, and
  `Interface.Compilation.Discrete`. Their import paths, stated
  responsibilities, and documented canonical declarations are recommended
  and machine-governed, but have no current external source-compatibility
  guarantee.
- **Experimental/implementation path**: files below `Execution/`,
  `Simulation/`, `Observed/`, `FOSG/`, and `Compiler/`, except for declarations
  explicitly documented as canonical. These files are build-checked and
  placeholder-free, but their individual import paths and proof helpers are
  not frozen.

There is currently no narrower carrier compatibility exception: the freeze
decision for `Arena`, `ControlledGame`, `ControlledDecisionGame`,
`ControlledObservedGame`, and the five-module `Interface.StructuralCore`
boundary is deferred by
[`efg-minimal-core-freeze.md`](efg-minimal-core-freeze.md). The exact facade
closure remains a pre-stability import regression that may be deliberately
revised with its architecture evidence.

Canonical and Frontend API growth is nevertheless frozen. CI snapshots their
registered module paths and explicit public declarations, so new public
endpoints, new supported frontends, and new canonical facades are rejected.
The 2026-09-04 A19 decision is the recorded narrow exception: it adds only the
zero-declaration pure `Effective` and opt-in `Effective.Analytic` aggregate
paths, while retaining the existing declaration ceiling.
This limits surface area while the existing carrier and usability review
converges; it does not yet promise source compatibility for existing
declarations.

Lean visibility is broader than this policy: importing a facade makes every
declaration in its transitive imports name-resolvable. That does not promote
those declarations to a governed facade contract.

During pre-stability, an evidence-backed correction or hard migration of the
existing surface is allowed. It must
synchronize internal consumers, positive/negative import regressions,
lifecycle rows, design documentation, and the audit. Compatibility wrappers
are not retained for hypothetical users. A migration window, deprecation
period, and major-release-only removal policy begin only if EFG API stability
is formally announced later.

## Canonical pre-stability facades

Downstream code should import the smallest row that provides the semantics it
uses. Pre-release broad compatibility aggregates were deleted after internal
consumers migrated; the final column names the adjacent granular facade when a
client needs a larger semantic tier.

| Need | Recommended import | Governed responsibility | Adjacent granular facade |
|---|---|---|---|
| Structural core | `EconCSLib.GameTheory.ExtensiveGame.Interface.StructuralCore` | exact narrow closure for `Arena`, `ControlledGame`, reachability, typed histories, measure-free complete plays, payoff-free `ControlledDecisionGame` and optional `ControlledObservedGame`, external root presentations, and pure strategies/profiles | same |
| Foundation | `EconCSLib.GameTheory.ExtensiveGame.Interface.Core` | the broader governed Foundation Facade: StructuralCore semantics plus structural length/well-foundedness, bounded deterministic/PMF execution, lawful subgame systems, represented-information/finite-EFG certificates, quasistrategies, and recall | same |
| Objectives | `EconCSLib.GameTheory.ExtensiveGame.Interface.Objective` | history-sensitive terminal/path outcomes, winning conditions, prefix topology/measurability, signal/public recall, and information-consistent quasistrategies without probability or equilibrium | same |
| Logical winning | `EconCSLib.GameTheory.ExtensiveGame.Interface.Winning` | robust pure/quasi winning strategies, determinacy predicates, and explicit finite/well-founded hypothesis packages; no arbitrary-set determinacy claim | same |
| Stochastic logical winning | `EconCSLib.GameTheory.ExtensiveGame.Interface.Winning.Stochastic` | arbitrary-measure `AEWinningUnder` and probability-certified almost-sure winning under a supplied legal infinite history law, separate from pathwise/profile-based winning | same |
| Finite execution | `EconCSLib.GameTheory.ExtensiveGame.Interface.Execution.Finite` | bounded deterministic and `FiniteLaw`-valued execution, complete state/event-history policies with an absolute clock, exact coordinate/tail queries, separate absolute-clock and time-zero restart prefixes, finite occurrence-sensitive unfolding from `FiniteEFGHypotheses`, observed behavioral specialization, and discrete `KernelArena`, without path measures | `Interface.Execution.Infinite` additionally accepts supplied measure-valued infinite paths |
| Infinite discrete execution | `EconCSLib.GameTheory.ExtensiveGame.Interface.Execution.Infinite` | executable `FiniteLaw` path marginals and bounded observables, partial terminal search, and supplied probability path/terminal laws with explicit marginal and legality certificates | same |
| Analytic execution | `EconCSLib.GameTheory.ExtensiveGame.Interface.Execution.Analytic` | non-atomic measurable-kernel execution, state/history/event/information policies, realization, observed profile assembly, and exact finite-execution semantic compatibility | same |
| Structural/PMF relations | `EconCSLib.GameTheory.ExtensiveGame.Interface.Relations.Discrete` | strict morphisms/isomorphisms, information refinements, PMF trajectory relations, and weak/stuttering simulations | combine with `Interface.Execution.Analytic` when analytic execution is also needed |
| Preservation contracts | `EconCSLib.GameTheory.ExtensiveGame.Interface.Preservation` | strict structural iso, directional information refinement, weak simulation, bounded/path-law realization, probability coupling, and strict/weak compiler packages, with their strengths kept distinct | combine with `Interface.Execution.Analytic` only for the non-atomic executor |
| Discrete equilibrium | `EconCSLib.GameTheory.ExtensiveGame.Interface.Equilibrium.Discrete` | pure, behavioral, mixed, and countably supported general-strategy semantics; finite-fuel equilibrium, bounded complete-history-law realization, event-clock perfect recall, finite Kuhn, and uniform strategy bridges | `Interface.Equilibrium.Analytic` also imports discrete equilibrium |
| Analytic equilibrium | `EconCSLib.GameTheory.ExtensiveGame.Interface.Equilibrium.Analytic` | measurable path utility/Nash, absolute-prefix and conditional continuation, exact finite-payoff/conditioning bridges, and A19 coded-event profile pushforward/simple-observable utility representation theorems | same |
| Restart | `EconCSLib.GameTheory.ExtensiveGame.Interface.Restart` | deviation-complete fresh-clock/absolute-prefix compatibility, equilibrium transfer, and exact finite restart-prefix semantic compatibility | same |
| Discrete compilation | `EconCSLib.GameTheory.ExtensiveGame.Interface.Compilation.Discrete` | PMF FOSG serialization; `GameTree`, `StochasticGameTree`, and chance-certified `FiniteImperfectGame` reference observed-EFG compilers | combine explicitly with `Interface.Equilibrium.Analytic` or `Interface.Restart` when required |

### Two-track execution and semantic compatibility

The shared structural EFG layer branches into an executable track and an
analytic track. There is no separate broad semantic-compatibility facade. Effective clients
compute through `Interface.Execution.Finite` (or the finite equilibrium
facade); a client imports the adjacent
analytic branch only when it needs a theorem interpreting that result:

```text
Interface.Execution.Finite
        |
        +-- Interface.Execution.Analytic   finite prefix/kernel equalities
        +-- Interface.Equilibrium.Analytic finite payoff/conditioning equalities
        `-- Interface.Restart              finite restart equalities
```

Reusable probability queries follow the same split:

```text
EconCSLib.Math.Probability.Effective          pure executable aggregate
        `-- Effective.Analytic                opt-in Measure/Kernel/integral certificates
```

The executable definition owns the returned value. The analytic branch owns
the general `Measure`, `Kernel`, path-law, or integral semantics. Their
relationship is a named equality, certified bound, or almost-everywhere
theorem under explicit hypotheses. General analytic declarations are not
called legacy when an algorithm covers only a finite or otherwise effective
subdomain. The complete ownership and migration rules are in
[`efg-semantic-compatibility.md`](efg-semantic-compatibility.md).

This is a generality-preserving algorithm-first policy: an effective consumer
must not obtain an answer by constructing a path measure and then projecting or
integrating it when the exact `FiniteLaw`, rational-sum, conditioning, search,
or checker API already computes that answer. General analytic consumers retain
their original domains and use the analytic facade directly; no effective
representation is imposed on the universal EFG carriers.

The two tracks do not duplicate structural histories, information, strategies,
objectives, or representation-neutral theorems. They split only where
probability laws, path execution, conditioning, or numerical evaluation need
different data representations.

### Governed transitive dependencies

Exact root/facade EFG and local closure budgets have one current home:
[`efg-governance.md`](efg-governance.md#root-aggregate-lifecycle). The
governance checker recomputes every row from the source import graph, excluding
the entry module itself. Historical before/after import graphs are intentionally
not retained as a second budget table; completed path changes are recorded only
where downstream migration still needs them in
[`efg-api-migration.md`](efg-api-migration.md).

The checker also enforces StructuralCore's exact five-module EFG
closure, rejects Objective/Winning in the Foundation Core closure, checks the
exact Recall and controlled-morphism leaf closures, and verifies that every
payoff-free infrastructure leaf, finite execution, and discrete relations
cannot reach payoff-aware or analytic implementation through a reverse edge.
Positive and negative compilation guards additionally verify the intended
public name boundaries.

`Execution.Finite` is the shallow finite/PMF boundary;
`Execution.Infinite` is the distinct path-measure boundary. The old combined
`Execution.Discrete` path and the broad Relations, Equilibrium, and
Compilation paths were removed rather than retained as redirects.

The root `EconCSLib.lean` aggregate imports `Interface.Execution.Finite`.
It retains the standalone finite `GameTree`/backward-induction track and the
exact zero-sum chance-tree solver. Infinite path laws, historical endpoint
equilibrium, Arena extraction, Zermelo, analytic kernels, representation
transfer, equilibrium, restart compatibility, FOSG serialization, and
reference compilers require the corresponding explicit module or granular
facade.
Existing code that formerly relied on transitive root imports can migrate by
importing `Interface.Objective`,
`Interface.Execution.{Finite,Infinite,Analytic}`,
`Interface.Relations.Discrete`, `Interface.Preservation`,
`Interface.Equilibrium.{Discrete,Analytic}`, `Interface.Restart` or
`Interface.Compilation.Discrete` directly.

The current root boundary and its machine-checked closure budget are recorded
in [`efg-governance.md`](efg-governance.md#root-aggregate-lifecycle). It
contains the finite facade and its implementation, `GameTree`,
`BackwardInduction`, and
`ZeroSumGameTreeWithChance`. It contains no `InfiniteTrajectory`,
endpoint-policy equilibrium, `FiniteArenaExtraction`, `Zermelo`, non-atomic
`MeasurableKernelArena`, continuation-equilibrium, restart, FOSG, or compiler
module.

The granular facade paths and declarations explicitly described as canonical
in their module documentation are the intended future public surface.
Proof-local helpers and implementation subdirectory paths are not individual
pre-stability contracts. Neither category currently creates an external
source-compatibility guarantee.

`Interface.Core` also exposes the canonical, reducible observed-presentation
constructors `ExtensiveGame.ofArena`,
`ObservedGame.historyInformation`,
`ObservedGame.decisionHistoryInformation`,
`ObservedGame.completeInformation`,
`ContinuationRootPresentation.initialOnly`/`allHistories`, and
`SubgameSystem.initialOnly`. `ObservedChanceGame.withChanceKernel` and its
complete-information composition first appear at `Interface.Execution.Finite`.
Their choices and limitations are audited in
[`observed-game-constructors.md`](observed-game-constructors.md).
The finite compiler declarations and their exact preservation boundaries are
audited in
[`efg-representation-compilation.md`](efg-representation-compilation.md).

Root predicates use names that expose their proof status:

- representation-neutral continuation forms use `IsDeclaredRoot`,
  `map_declaredRoot`, `DeclaredRootSurjective`, and
  `DeclaredRootReflecting`;
- an observed game receives an external `RootPresentation` whose `IsRoot`
  predicate selects presentation-visible analysis roots;
- the former embedded designated-root predicate has no compatibility value;
  root-sensitive APIs require an explicit presentation, so no migration can
  silently widen a custom root set to all histories;
- `IsLawfulSubgameRoot` states the representation-independent information-set
  conditions at one history; its canonical owner is
  `ControlledObservedGame`, while the `ObservedGame` spelling is a reducible
  payoff-aware compatibility name;
- `SubgameSystem` selects a nonempty lawful system independently of
  presentation metadata and may be conservative;
- `SubgameSystem.IsVisibleIn roots` is the additional property that all
  selected roots are visible in one explicitly supplied presentation;
- predicates ending in `SubgamePerfectOn` quantify exactly the supplied
  lawful system;
- complete standard EFG subgame perfection requires
  `ControlledObservedGame.CompleteSubgameSystem`, whose coverage law includes
  every structurally lawful root; the canonical complete system exists for
  every controlled observed game, and the `ObservedGame` spelling delegates
  definitionally through `toControlledObservedGame`.

Pure execution uses `ControlledGame.NoChanceOnHistories`, which quantifies
only over legal histories from the initial state. Ambient
`ControlledGame.NoChance` remains available for theorems that truly inspect
every state and implies the reachable certificate. The
`ReachableNoChance` regression compiles a game with an unreachable,
nonterminal nature state: global no-chance is false, reachable no-chance is
true, and pure history execution plus the total continuation game form remain
available.

Discrete probability semantics distinguish raw data from execution claims.
`BoundedHistoryLawFamily` can hold any history-valued PMF family.
`CertifiedBehavioralExecutionLaw` additionally proves normalization,
reachable legality, terminal absorption, and equality with
`behavioralHistoryLaw`; execution-facing unfolding preservation consumes its
certified projection. At the maximum measure-valued layer,
`CompletePathLawSemantics` supplies lawful per-root path marginals, not
automatically one common causal process. `RealizesExecution` or
`ExecutionCoherent` is required for operational claims. The general
`HistoryTransformLawEquivalentAt` accepts arbitrary history transforms;
`TerminalHistoryLawEquivalentAt` instead has codomain
`Arena.TerminalHistoryFrom`.

Signal/public recall names expose their clock convention.
`HasEventClockSignalPerfectRecall` and
`HasEventClockPublicPerfectRecall` append a signal on every transition.
`SignalTraceBuilder` is the optional external asynchronous layer: its
`eventSignal` returns `Option Signal`, so `none` represents a silent event.
The always-emitting builder recovers the event-clock signal trace; no theorem
identifies event-clock recall with arbitrary silent-event recall.

The removed pre-release spellings and the record-field migration are
documented in [`efg-api-migration.md`](efg-api-migration.md). Record field
labels cannot be preserved by ordinary declaration aliases: an alias can make
an old projection name resolve, but it cannot make an old label valid inside a
named record literal.

## Import-only lifecycle and implementation modules

The complete `Observed/Controlled/` hierarchy has an explicit role map:
canonical carrier, semantic owner, responsibility owner, declaration-free
aggregate facade, or downstream payoff-aware adapter. See
[`efg-controlled-api.md`](efg-controlled-api.md). Governance rejects flat
`Observed.ControlledFoo` siblings and prevents canonical controlled modules
from depending on anything under `Controlled.Compat`.

The hard migration deleted all 19 import-only paths formerly registered
Compatibility:

- `ExtensiveGame.Play`, `ExtensiveGame.BehaviorStrategy`, and
  `FOSG.FOSGSequentialization`;
- `Observed.{Morphism,Refinement,BehaviorRefinement,DeferredSampling,KuhnConditioning}`;
- `Interface.Execution.Discrete`,
  `Interface.{Relations,Equilibrium,Compilation}`, and
  `Interface.SimulationFramework`;
- `Simulation.ObservedMeasurableKernelRestartCompatibility`;
- `ExtensiveGame.Probability.{ConditionalSampling,ConditionalProduct,DeferredSampling,FiniteProductCoupling}`;
- `GameForm.Continuation`.

The declaration-free `Observed.Morphism.Fiber` forwarding import was also
removed; its game-independent dependent-fiber calculus now lives in
`EconCSLib.Math.DependentFiber`. The unrelated comment-only
`Foundation.Player` shell was removed from the root aggregate. No redirect
stubs remain.

Their implementations are split by semantic concept:

```text
GameForm/Continuation/
  Core → Simulation → Iso

Observed/Morphism/
  Math.DependentFiber + Relations.Discrete.Morphism
    → Structural → Inverse → Operational → Continuation

Observed/Refinement/
  Structural → Core → Termination

Observed/BehaviorRefinement/
  Structural → Execution

Observed/DeferredSampling/
  Core → Execution → Realization

Observed/KuhnConditioning/
  Posterior → Core → Execution → Realization

Observed/Controlled/Infrastructure/
  Core    WellFormed    Subgame    Finite    Quasi    Recall

Observed/Controlled/Morphism/
  Core → Subgame
  Core → Recall
  Core + Semantics → Objective

FOSG/Sequentialization/
  Core → Policy → MacroLaw → Trajectory → Witness → Equilibrium

Simulation/Restart/
  Core → Trajectory → Certificates → Observed → Assembly → Equilibrium
```

The FOSG serializer keeps game construction and continuation-root selection
orthogonal. `FOSG.Sequentialization.observedChanceGameCore` is the canonical
root-free compiled game, while `rootPresentation` attaches a caller-selected
source-root predicate. The root-parameterized
`observedChanceGame` spelling is a definitionally equal compatibility
wrapper.

Downstream users should normally import a granular facade.
`Controlled.Infrastructure` and `Controlled.Morphism` are retained canonical
aggregate facades over their narrow responsibility leaves because they have
an explicit navigation role and exact governed imports. The root `EconCSLib`,
`EconCSLib.Examples`, `EconCSLib.OpenProblem`, `GameForm`, `FiniteLaw`, the pure
`Effective` aggregate, its opt-in `Effective.Analytic` aggregate, and the
granular `Interface.*` facades are the other registered import-only navigation
modules. There are zero temporary compatibility wrappers.

## Visibility audit and enforceable boundaries

| Import boundary | Transitive exposure found by the audit | Disposition |
|---|---|---|
| `EconCSLib` | The occurrence compiler previously pulled `Observed.SPE`, pure/behavioral refinement, perfect recall, and continuation transfer into the root aggregate. | Removed the compiler import. Add `Interface.Compilation.Discrete` downstream. |
| StructuralCore | Its exact EFG/local closure is `Structural.Basic`, `Structural.Reachability`, `Structural.History`, `Execution.CompletePlay`, and `Observed.Controlled`; the payoff-aware compatibility modules `Basic` and `Execution.{Reachability,History}` are absent, as are termination, objective, probability, relation, equilibrium, simulation, and compiler modules. | Enforced by exact source-graph comparison and `StructuralCoreImportBoundary`. |
| Core | The Foundation Facade reaches structural/finite/recall/subgame leaves and bounded deterministic/PMF execution, but neither `Execution.Objective` nor `Winning.*` nor a payoff-aware observed game. | Enforced by source-graph governance and `CoreImportBoundary`. |
| Controlled recall leaf | `Controlled.Infrastructure.Recall` reaches general represented-information witnesses through `WellFormed`, but no finite hypothesis, length bound, or controlled executor. | Exact six-module closure plus `RecallImportBoundary`. |
| Controlled morphism core | `Controlled.Morphism.Core` exposes structural Hom/Iso, information refinement, strategy transport, and Iso algebra without subgame, recall, finite, or length declarations. | Exact 9 / 9 closure plus `ControlledMorphismCoreImportBoundary`; the aggregate facade has a separate import regression. |
| Objective | Complete plays, structural termination certificates, and terminal/path outcomes are reachable, but chance execution, path probability laws, equilibrium, and analytic kernels are absent. | Enforced by `ObjectiveImportBoundary`. |
| Finite execution | Structural `Arena` and observed isomorphism prerequisites are reachable through chance execution; complete-history and state/event-prefix rational expectations and stopped payoffs are executable, but no `ProbabilityTheory.Kernel`, `MeasurableKernelArena`, or infinite `Arena.pathLaw` is available. | Shallow finite-law boundary, enforced by `FiniteExecutionImportBoundary`. |
| Infinite discrete execution | `Execution.InfiniteTrajectory` exposes supplied probability measures together with executable finite prefixes, but no longer exposes Mathlib kernels or a hidden hitting-time/path-law constructor. | Enforced separately from non-atomic kernels by `InfiniteExecutionImportBoundary`. |
| Analytic execution | Discrete finite-law execution and coupling declarations are reachable through exact discrete recovery; executable history laws also have exact state/event one-step and arbitrary finite-prefix kernel correspondence under an explicit local measurable realization. | Kept as implementation dependencies; arbitrary history functions are not assumed measurable, supplied prefixes retain their absolute clock, and equilibrium declarations remain absent. |
| Discrete relations | Strict structure, PMF couplings, and weak simulation share one non-analytic closure. Preservation aliases and measure-valued law contracts remain outside it. | Enforced by `DiscreteRelationsImportBoundary`; no empty `Relations.Analytic` symmetry module was added. |
| Preservation | The independent preservation vocabulary spans strict/refinement/weak relation strengths and measure-valued path-law realization/coupling without importing the non-atomic executor. | Enforced by `PreservationImportBoundary`, which resolves the canonical declarations and rejects analytic-executor and equilibrium sentinels. |
| Discrete equilibrium | Split Kuhn/PMF conditioning helpers are reachable, but route regressions are private and the path-measure and measurable-kernel layers are absent. | Enforced by `DiscreteEquilibriumImportBoundary`; helpers remain implementation details unless documented as canonical. |
| Analytic equilibrium | Measurable outcome, continuation, and regular-conditioning implementation helpers are reachable. | `Equilibrium.Analytic` is the explicit analytic entry; Restart and compiler sentinels remain absent. |
| Restart | Splicing, finite-prefix, partial-step, and certificate-specific proof declarations are reachable. | Name-resolvable implementation surface; only the canonical semantics and recommended constructors described below form the governed contract. |
| Discrete compilation | Compiler proof helpers, FOSG sequentialization internals, finite `GameTree`/`StochasticGameTree` infrastructure, and legacy `ImperfectInformation` are reachable without measurable-kernel execution. | Canonical finite compilers/serializers form the governed contract; enforced by `DiscreteCompilationImportBoundary`. |

`StructuralCore` also exposes
`ControlledObservedGame.relabelPlayers`. Thus strict Hom/Iso APIs may retain
one chosen player carrier without making names semantically rigid: any
bijective renaming is normalized first, and pure profiles are transported by
`relabelPureProfileEquiv`. The payoff-aware `ObservedGame` adapter reindexes
the payoff vector along the same equivalence. Non-bijective addition,
deletion, or merging of players remains compiler-specific.

The boundary examples under `Examples/ExtensiveGame/*ImportBoundary.lean`
compile positive sentinels and `#guard_msgs` negative sentinels for granular
facades, both higher branches, and the root aggregate. They catch accidental
reintroduction of selected higher-layer declarations.

Lean's module mechanism cannot enforce a declaration whitelist. In
particular, it cannot:

- hide an implementation declaration once a facade imports the module that
  defines it;
- stop a downstream user from importing an experimental leaf module directly;
- encode “canonical”, “experimental”, or “compatibility-only” as visibility
  modifiers; or
- prove that a finite set of negative sentinels covers every future
  declaration.

Those boundaries remain documentation/review conventions. The import graph
can enforce only whole-module absence, and the negative regressions make the
most important whole-module boundaries executable.

CI also runs:

```bash
python3 scripts/report_efg_declaration_usage.py \
  --check --output /tmp/efg-declaration-usage.md
```

The generated artifact separates internal source indegree from source
docstrings, documentation, ordinary examples, positive facade-contract
checks, tests, lifecycle, `[simp]` attributes, and privacy evidence. Names
occurring only in negative `#guard_msgs` checks are not positive facade
evidence. It classifies zero-indegree declarations as intentional endpoints,
source-documented endpoints, normalization API, facade contracts, compiler
preservation endpoints, proof helpers, historical-only declarations, or a
residual unclassified-public review bucket. Zero indegree is a triage signal,
not a deletion rule: endpoint theorems are often intended leaves. The
residual ceiling is not a claim that every queued theorem is dead or already
reviewed, and it never authorizes automatic deletion.

## Fresh-restart compatibility

The governed `Interface.Restart` surface is divided into three levels:

1. Canonical semantics:
   `KernelBehavioralProfile.IsFreshRestartStateCompatibleAt`,
   `ProfileAssembly.FreshRestartDeviationCompatibleAt`/`On`, and the three
   root scopes for `_of_compatible` transfer: rootwise Nash, Nash on
   presentation-designated continuations, and subgame perfection on an
   explicit lawful `SubgameSystem`. A fourth complete-system theorem exposes
   standard SPE over every structurally lawful root.
2. Recommended constructors: generated-law almost-everywhere step
   compatibility, rooted behavioral action-kernel compatibility, and
   statistic factorization or time-varying information rebase.
3. Implementation tools: marker normalization, measurable splicing, finite/full
   trajectory laws, executable fresh/absolute/spliced finite prefixes with
   all-horizon analytic equalities, partial-step recurrence, rooted prefix/path
   steps, and pointwise global strengthenings.

The first two levels are the recommended pre-stability contract. The third is
necessarily
name-resolvable through Lean's transitive imports, but declarations below
`Simulation/Restart/` are proof implementation and are
not individually governed. Ordinary equilibrium clients do not import the
restart proof stack transitively.

Choose an entry from the fact the model exposes:

```text
I already have state-law compatibility
  → use the canonical compatibility transfer

I can prove generated-law a.e. step equality
  → convert to partial-step/state compatibility

My strategy is a structural rooted action policy
  → use the rooted action certificate

My strategy is built through a statistic or time-varying information
  → use the factorization/rebase constructor
```

Certificate-specific equilibrium wrappers are private route regressions.
Consumers convert the available certificate to
`FreshRestartDeviationCompatibleAt`/`On` and invoke a canonical
`_of_compatible` theorem. This prevents every certificate route from becoming
a parallel governed equilibrium contract.
The compatibility layer does not claim that fresh restart equals absolute
continuation automatically, that continuation fixes a conditional version at
null histories, that transition equality implies action equality, that every
compatible policy factors through a chosen statistic, that rebase existence
implies policy naturality, or that initial-root Nash implies SPE.

## Uniform strategy bridge

`Observed.StrategyBridge` packages the common consumer operation in
`BoundedDesignatedNashBridge`:

1. map a source profile to a target strategy representation;
2. preserve and reflect the corresponding bounded Nash predicate on
   presentation-designated continuations.

The constructors

- `ObservedStrategyBridge.pure`,
- `ObservedStrategyBridge.behavioral`,
- `ObservedStrategyBridge.mixed`, and
- `ObservedStrategyBridge.kuhn`

have different mathematically necessary hypotheses, but expose the same
`mapProfile` and `isNash_iff` fields. They are a navigation facade, not a claim
that pure, behavioral, and mixed strategies are the same type.

The shortest relation-local theorems remain valid direct entry points when a
caller already has the relevant relation:

- `ObservedGame.Iso.isPureNashOnRootsAtFuel_iff`;
- `ObservedChanceGame.Iso.isBehavioralNashOnRootsAtFuel_iff`;
- `ObservedChanceGame.Iso.isMixedNashOnRootsAtFuel_iff`.

Equivalent derivations through continuation families and information
refinements are private route regressions. They are deliberately absent from
the supported declaration surface.

## Horizon- and law-parametric semantics

`IndexedContinuationGameForm` adds one arbitrary semantic index to
`ContinuationGameForm`. Its `Horizon` is not fixed to `Nat`, and its `Outcome`
is not fixed to `PMF`. Fixing an index with `atIndex` recovers the existing
continuation abstraction, so Nash-on-declared-roots transfer is inherited from
one generic theorem layer. That representation-neutral layer cannot inspect
histories or information sets and therefore does not itself certify standard
subgames.

`ControlledObservedGame.ContinuationSemantics` is the canonical payoff-free
observed-EFG adapter. A client supplies only strategy spaces, the index and
outcome types, and an evaluator on complete histories.
`ObservedGame.ContinuationSemantics` is a payoff-aware abbreviation through
`toControlledObservedGame`; it does not inspect or store the state-payoff
field. Conversely, `ObservedGame.ofControlledObservedGame` attaches an
arbitrary state-payoff interpretation to a controlled observed carrier, and
the erase-after-attach and reattach-existing-payoff round trips are proved
definitionally. `toIndexedGameFormOn` reuses the explicitly supplied root
predicate and therefore supports `IsNashOnPresentationAt roots`;
`toIndexedGameFormOn system.IsRoot` and
`IsEvaluatorContinuationEquilibriumOnAt ... system` expose equilibrium
relative to the supplied evaluator on an explicit lawful system.
`IsEvaluatorContinuationEquilibriumAt ... completeSystem` additionally
requires coverage of every structurally lawful root, but that coverage does
not turn an arbitrary evaluator into operational EFG execution.

`isEvaluatorContinuationEquilibriumAt_iff_of_surjective` is the abstract
game-form transfer theorem. It preserves and reflects evaluator-relative
equilibrium under complete lawful systems, utility compatibility,
strategy/deviation surjectivity, and declared-root surjectivity. A weak
serializer or declared-root map alone does not establish standard SPE.

The evaluator-relative transfer layer is payoff-free, so a logical or
path-objective application does not need to invent a dummy state-payoff type.
The payoff-aware `ObservedGame` adapters permit source and target state-payoff
types to differ.

There is intentionally no generic standard-EFG-SPE API for an arbitrary
`ContinuationSemantics`. A future operational abstraction is deferred until
at least two concrete modes expose the same canonical interface. It must:

- derive continuation-local strategies from decision information reachable
  after the lawful root;
- lift every legal local unilateral deviation to a global strategy and prove
  the restriction/update square;
- evaluate through canonical complete plays or certified complete-path laws;
- prove root locality from that concrete execution; and
- recover the existing concrete standard-SPE definition for each instance.

Pure terminating standard SPE remains in `Observed.SPE`; behavioral and
analytic standard-equilibrium claims remain with their certified execution
layers. No placeholder declaration reserves the future generic API.

The index can represent:

- a natural-number execution bound;
- `Unit` for a termination-certified total evaluator;
- `WithTop Nat` for finite indices plus a distinguished `⊤` evaluator; or
- an application-specific approximation or discount parameter.

The outcome can be deterministic, a PMF, a measure, or another semantic
object. `Examples.ExtensiveGame.ReusableSemantics` constructs a
`WithTop Nat`-indexed, `Measure ℝ`-valued evaluator together with an explicit
evaluator-locality regression. Its utility is constant and its morphism is the
identity; there is no finite-index-to-`⊤` convergence
claim.

The abstract indexed interface itself does not assert convergence. Concrete
bounded discrete event-time execution is provided separately by
`Execution.InfiniteTrajectory`: `Arena.pathMarginal` computes exact
`FiniteLaw` prefixes, `noneMass` and `stoppedPayoffLaw` are executable bounded
observables, and `terminalTime`/`terminalPayoff` use fuel and return `Option`.
`Arena.pathLaw` projects a caller-supplied complete-path
`ProbabilityMeasure`; its finite-coordinate and almost-sure legality theorems
require explicit certificates. `Observed.InfiniteExecution` specializes this
supplied-law boundary through behavioral profiles and chance laws.

The analytic tier records the stronger coherence statement
`Arena.pathLaw_eq_historyKernelArena_toMeasurable_pathMeasure`: after lifting
complete histories to the canonical history-state kernel arena, a supplied
discrete path probability measure equals the analytic path measure when the
caller supplies that realization certificate. Agreement is then available
for every measurable path event and functional, not only for individual
coordinates.

None of these modules constructs a continuous-time kernel or a
càdlàg/Skorokhod path law. The resolved reuse issue is that concrete evaluators
do not require a new root encoding, game form, morphism, or
equilibrium-transfer architecture.

`Simulation.Kernel.Arena` is a distinct analytic one-step transition
boundary. Its kernel domain is the measurable dependent state/action bundle,
and its transition is a genuine normalized Mathlib `Kernel`; hence non-atomic
laws are allowed. The existing `KernelArena` embeds into it through
`PMF.toMeasure`. `Simulation.Kernel.Execution` adds a measurable
legal-action policy kernel, zero action mass at terminal states, and a
normalized terminal-absorbing state-step kernel. Discrete policies embed with
exact equality to `KernelArena.stepLaw`, while the continuous regression
remains non-atomic after policy-controlled execution.
`Simulation.Kernel.Endpoint` iterates the stopped step kernel,
proves its finite Chapman--Kolmogorov and Markov laws, and exactly recovers
`KernelArena.stateLawFrom`; every positive finite endpoint in the continuous
regression remains non-atomic. `Simulation.Kernel.StatePath` constructs
the corresponding Ionescu--Tulcea probability law on infinite
natural-number-indexed state paths and proves that every coordinate marginal
is exactly the finite endpoint measure. Terminal starts produce constant
paths almost surely when state singletons are measurable, and discrete policy
coordinates recover the existing discrete PMF executor exactly. The public API still does
not claim continuous-time path semantics. `Simulation.Kernel.StatePath` by itself
does not compile observed behavioral strategies; the later presentation
modules in the same Analytic facade provide that separate adapter.

`Simulation.Kernel.HistoryPath` removes the stationary state-Markov
restriction: a measurable action kernel may depend on time and the complete
finite state prefix. Its next-coordinate equation integrates against the
joint prefix law, and `ActionPolicy.toHistoryActionPolicy_pathMeasure` proves
that the old stationary executor is preserved exactly.

`Simulation.Kernel.EventPath` retains the selected action occurrence
beside every sampled successor state, using `Unit ⊕ ActionBundle` as a
measurable optional coordinate. `EventHistoryActionPolicy` may inspect the
complete finite event prefix. Its terminal-absorbing Ionescu--Tulcea law is a
probability measure, and
`HistoryActionPolicy.toEventHistoryActionPolicy_statePathMeasure` proves that
forgetting recorded actions from an embedded state-history executor recovers
the complete original infinite state-path measure. This remains a raw
operational history API: it does not impose observation or information-set
consistency.

`Simulation.Kernel.ObservedEvent` fixes a measurable
time-indexed information statistic on finite event prefixes and indexes action
kernels only by its values. Equal information therefore forces exactly equal
compiled action measures. Fine-to-coarse `EventInformation.Hom` maps support
contravariant policy pullback; the compiled raw event policy, stopped steps,
and complete event-path probability law are preserved exactly. Full event,
state-prefix, and latest-state information specialize exactly to the existing
event-history, state-history, and stationary executors. Because those kernel
values are measures on concrete `ActionBundle`, equal information at
nonterminal prefixes also forces equal latest states; the interface therefore
does not directly encode a player information set spanning distinct
complete-history states.

`Simulation.Kernel.RealizedInformation` separates those two roles.
`ActionRealization` fixes a measurable, possibly stochastic interpretation of
time-indexed abstract actions at each concrete event prefix.
`RealizedActionPolicy` varies only the information-indexed abstract kernel.
Its compiler binds the shared abstract law through the local realization,
proves the resulting raw event policy normalized and legal, and preserves the
whole event-path law under information-factor pullback. Equal information
therefore means equal abstract laws; equality of concrete compiled laws
requires an additional almost-everywhere equality of the relevant realization
sections. The absent-minded example proves this interface is inhabited on a
fixed terminal-tagged information structure where the direct
`ActionBundle`-valued interface is not.

`Simulation.Presentation.Chance.KernelBridge` lifts every Arena history policy to a
stationary policy on complete-history states. For an `ObservedChanceGame`,
player histories use the existing information-indexed behavioral law, chance
histories use the declared chance kernel, and each finite analytic endpoint
measure is exactly the measure of the existing stopped-history PMF. This is
the supported finite execution bridge. It intentionally retains complete
history as the analytic policy state. Connecting original
`ObservedGame.InfoState` across different history states requires an explicit
abstract-action realization presentation because the observed-game carriers
do not themselves carry the needed measurable spaces.

`Simulation.Presentation.Chance.Realized` defines that explicit
certificate boundary. The information statistic and realization remain fixed
across profiles; player histories factor through `ObservedGame.InfoState`;
and exact raw-policy compilation yields exact player/chance bundle laws,
complete joint event/state paths, and finite stopped-history measures. The
absent-minded example constructs such a certificate. The public API does not
claim unconditional existence: original observed-game carriers still lack
measurable structures.

`Simulation.Presentation.Chance.Countable` owns executable tagged-information
and action selectors. Terminal classification requires the explicit
state-indexed terminal decision. Information lookup requires an executable
reachability decision and returns `Option`; action realization requires
executable tag equality and returns `none` on mismatch. No fallback action or
information value is selected. Countable models supply actual `Encodable`
data; a bare countability proof no longer manufactures an encoding, measurable
space, kernel, or analytic presentation. The two countable regressions build
concrete encoders/partial decoders and run the selectors natively. Analytic
consumers supply the existing `AnalyticPresentation` or
`MeasurableKernelPresentation` and use their canonical compatibility theorems
directly. Unreachable real-valued player identifiers and information/action
fibers remain outside the effective enumeration.

`Simulation.Presentation.Chance.MeasurableHistory` and
`Simulation.Presentation.Chance.Measurable` are the explicit
uncountable-reachable extension. The model author supplies measurable spaces
on complete histories and dependent legal bundles, measurable projection,
append, terminal set, and singletons, plus the exact deterministic transition
kernel. The presentation author supplies measurable information,
profile-independent realization, and exact local player/chance bundle laws.
The reusable executor then supplies complete joint-event and state-path
measures. `AnalyticPresentation.toMeasurablePresentation` proves that the old
top-measurable supplied-presentation API is an exact specialization. There is
no separate countability-based analytic constructor.

`ObservedChanceMeasurableUncountableBoundary` verifies a real root-action game
whose reachable histories and legal bundle are both non-countable and
measurably coded by `Unit ⊕ ℝ` and Borel `ℝ`.

`Simulation.Presentation.Kernel.Core` is the non-atomic observed
policy layer. Its structural parameter is an `ObservedGame`; player and chance
randomization are no longer stored as PMFs. A fixed concrete chance-action
kernel belongs to the presentation, while each `KernelBehavioralProfile`
supplies measurable abstract action kernels indexed by the common information
statistic. Exact chance consistency is checked after realization, and
unilateral deviations preserve other players' abstract kernels.

`MeasurablePresentation.toKernelBehavioralProfile` embeds every admitted old
PMF profile without changing its realized policy or compiled executor.
`ObservedNonAtomicKernelBoundary` uses unit-interval volume and proves both a
player-controlled and a genuinely chance-controlled compiled bundle kernel
are not representable by any PMF. The API still does not infer measurability
of arbitrary strategies on an uncountable information space.

## Import and dependency rules

- Reusable modules under `Math/Probability/FiniteLaw`, `Effective`,
  `FiniteMarkovChain`, `RationalIntervalUnion`, and the remaining internal
  `PMF` family must not import EFG or other game-theory modules.
- Concrete compilers and FOSG serializers depend on semantic interfaces, not
  conversely.
- `Examples` may import every facade tier; library modules must not
  import `Examples`.
- Finiteness, decidable equality, termination, and recall assumptions remain
  local to the declarations that use them.

These checks provide machine-checked evidence for source elaboration, the
axiom surface, placeholder policy, module boundaries, and the listed formal
semantic properties. They are not a metamathematically complete certification
of every intended model meaning.
