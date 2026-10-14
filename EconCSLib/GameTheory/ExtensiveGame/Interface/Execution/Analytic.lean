/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Interface.Execution.Infinite
import EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Law.Analytic
import EconCSLib.GameTheory.ExtensiveGame.Simulation.Kernel.Arena
import EconCSLib.GameTheory.ExtensiveGame.Simulation.Kernel.Execution
import EconCSLib.GameTheory.ExtensiveGame.Simulation.Kernel.Endpoint
import EconCSLib.GameTheory.ExtensiveGame.Simulation.Kernel.StatePath
import EconCSLib.GameTheory.ExtensiveGame.Simulation.Kernel.DiscreteBridge
import EconCSLib.GameTheory.ExtensiveGame.Simulation.Kernel.HistoryPath
import EconCSLib.GameTheory.ExtensiveGame.Simulation.Kernel.EventPath
import EconCSLib.GameTheory.ExtensiveGame.Simulation.Kernel.FiniteExecution
import EconCSLib.GameTheory.ExtensiveGame.Simulation.Kernel.EffectivePathLaw
import EconCSLib.GameTheory.ExtensiveGame.Simulation.Kernel.CertifiedPathApproximation
import EconCSLib.GameTheory.ExtensiveGame.Simulation.Kernel.FiniteRealizedInformation
import EconCSLib.GameTheory.ExtensiveGame.Simulation.Kernel.FiniteCompleteEventPath
import EconCSLib.GameTheory.ExtensiveGame.Simulation.Presentation.Chance.FiniteExecution
import EconCSLib.GameTheory.ExtensiveGame.Simulation.Kernel.ObservedEvent
import EconCSLib.GameTheory.ExtensiveGame.Simulation.Kernel.RealizedInformation
import EconCSLib.GameTheory.ExtensiveGame.Simulation.Presentation.Chance.KernelBridge
import EconCSLib.GameTheory.ExtensiveGame.Simulation.Presentation.Chance.Realized
import EconCSLib.GameTheory.ExtensiveGame.Simulation.Presentation.Chance.MeasurableHistory
import EconCSLib.GameTheory.ExtensiveGame.Simulation.Presentation.Kernel.Core
import EconCSLib.GameTheory.ExtensiveGame.Simulation.Presentation.Kernel.ProfileAssembly
import EconCSLib.GameTheory.ExtensiveGame.Simulation.Presentation.Kernel.EffectiveBehavioralProfile
import EconCSLib.GameTheory.ExtensiveGame.Simulation.Presentation.Chance.Measurable
import EconCSLib.GameTheory.ExtensiveGame.Simulation.Presentation.Chance.ProfileAssembly
import EconCSLib.GameTheory.ExtensiveGame.Simulation.Presentation.Chance.Countable

/-!
# Analytic measurable-kernel EFG execution

Recommended pre-stability import for normalized non-atomic measurable-kernel
dynamics, terminal-aware execution, finite endpoint and infinite event-time
path laws, state/history/event/information-dependent action policies,
abstract-action realization, and observed profile assembly.

This is the analytic track over the shared structural EFG layer. It retains
arbitrary measurable-kernel and path-law semantics when no faithful executable
representation is available, and exposes named compatibility theorems for
effective subdomains.

`Controlled.Law.Analytic` packages a measurable-kernel profile assembly into
the same lawful `ControlledObservedGame.CompletePathLawSemantics` used by the
discrete behavioral constructor; canonical deterministic-history legality is
an explicit adapter premise.

`Arena.pathLaw_eq_historyKernelArena_toMeasurable_pathMeasure` identifies the
complete discrete history-path law with the analytic path measure after the
canonical history-state lift. Thus the discrete embedding has a proved
whole-path coherence theorem, rather than merely single-coordinate
agreement. This does not assert a path-law equivalence for every non-atomic
presentation; those presentations enter the common carrier through their
own explicit adapter evidence.

`Simulation.Kernel.FiniteExecution` supplies the local finite/analytic seam:
when a measurable history-action kernel exactly realizes an executable
`FiniteLaw` policy at every prefix, its state and action-recording one-step
kernels and all finite-prefix marginals are exactly the finite laws interpreted
as measures. The correspondence accepts any supplied initial prefix and
preserves its absolute clock. Arbitrary history functions are not silently
assumed measurable.
This is semantic compatibility: executable definitions continue to own the
computed finite laws, while the general kernel declarations remain their
analytic interpretation.

`Simulation.Kernel.EffectivePathLaw` proves that every horizon in the coherent
executable path-law family is exactly the corresponding analytic
`Kernel.partialTraj` marginal. The running interface remains a finite query
family and does not acquire an arbitrary measurable-event oracle.

`Simulation.Kernel.CertifiedPathApproximation` turns an A15 scheme interval
into a real semantic guarantee when an external measurable, integrable state
path utility has a pointwise uniform prefix-approximation bound by the
scheme's radius.  It first identifies the lifted prefix integral with the
exact rational center, then proves interval enclosure and searched-tolerance
error.  The analytic utility and integral occur only in these theorems and
are not inputs to the executable search.

`Simulation.Kernel.FiniteRealizedInformation` relates finite abstract-action
selection and realization to the existing analytic `realizedKernel`. The
analytic policy, measurable equivalence, and local representation equations
are explicit proof inputs; the executable compiler remains measure-free.

`Simulation.Presentation.Kernel.EffectiveBehavioralProfile` applies that seam
to an effective kernel-valued profile: local weighted-Dirac representation
certificates identify its compiled raw policy and every bounded event-prefix
law with the existing high-level analytic executor.

`Simulation.Kernel.FiniteCompleteEventPath` proves that every finite prefix
and coordinate of a bounded terminal replay has the original analytic partial
trajectory marginal, including queries after the certified terminal bound.

Legality is stated as genuine almost-sure membership in dependent action
fibers. Numerical measure-one lemmas require local measurability assumptions.
This tier supplies execution and presentation semantics only. The discrete
`KernelTrajectory` implementation is transitively visible because exact
discrete recovery uses its policy and finite-law infrastructure, but supported
representation relations, information refinements, equilibrium predicates,
continuation conditioning, and fresh restart belong to later tiers.
-/
