/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Interface.Core
import EconCSLib.GameTheory.ExtensiveGame.Observed.Behavior
import EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Law.Discrete
import EconCSLib.GameTheory.ExtensiveGame.Observed.FiniteUnfolding
import EconCSLib.GameTheory.ExtensiveGame.Execution.Discrete.KernelArena
import EconCSLib.GameTheory.ExtensiveGame.Execution.Discrete.HistoryKernel
import EconCSLib.GameTheory.ExtensiveGame.Execution.Discrete.FiniteObservation
import EconCSLib.GameTheory.ExtensiveGame.Execution.Discrete.EffectivePathLaw
import EconCSLib.GameTheory.ExtensiveGame.Execution.Discrete.EffectivePathUtility
import EconCSLib.GameTheory.ExtensiveGame.Execution.Discrete.CertifiedPathApproximation
import EconCSLib.GameTheory.ExtensiveGame.Execution.Discrete.DiscountedPathUtility
import EconCSLib.GameTheory.ExtensiveGame.Execution.Discrete.FiniteCompleteEventPath
import EconCSLib.GameTheory.ExtensiveGame.Execution.Discrete.RealizedInformation
import EconCSLib.GameTheory.ExtensiveGame.Execution.Discrete.EffectiveKernelBehavioralProfile
import EconCSLib.GameTheory.ExtensiveGame.Execution.Discrete.ConditionalContinuation
import EconCSLib.GameTheory.ExtensiveGame.Execution.Discrete.ContinuationTruncation
import EconCSLib.GameTheory.ExtensiveGame.Execution.Discrete.ObservedChance
import EconCSLib.GameTheory.ExtensiveGame.Execution.FiniteCompletePath
import EconCSLib.GameTheory.ExtensiveGame.Execution.FinitePayoff
import EconCSLib.GameTheory.ExtensiveGame.Execution.Truncation

/-!
# Finite-horizon discrete EFG execution

Recommended pre-stability import for deterministic execution and exact finite-law execution
with finite fuel.

This is the executable track over the shared structural EFG layer. Models that
require arbitrary kernels or full analytic path laws use the separate analytic
track; structural histories and strategies are not duplicated.

This tier adds observed behavioral/chance execution and the discrete
`KernelArena` together with state/action-recording finite-history execution,
without importing infinite path measures, Mathlib Markov
kernels, non-atomic measurable-kernel execution, equilibrium transfer, or
concrete compilers. It is the recommended execution entry for finite games
and for clients whose stochastic semantics remain finite-law-valued.
`ObservedChanceGame.withChanceKernel` attaches an explicit normalized chance
law, while `completeInformation` composes that law with the core
complete-history presentation and an explicit root selection.
`FiniteEFGHypotheses.toFiniteHistoryGame` extracts a finite,
occurrence-sensitive reachable-history carrier without requiring
`Fintype State`. The payoff-free discrete chance layer exposes exact bounded
complete-history finite laws while keeping full infinite path measures out of this
facade. `KernelArena.StateHistoryPolicy` and `EventHistoryPolicy` retain
complete prefixes and absolute time; their bounded executors return exact
`FiniteLaw` values and remain independent of the analytic kernel stack.
`Execution.Discrete.FiniteObservation` adds exact coordinate, tail, fresh-clock
restart, and prefix-splicing queries while retaining event history until state
projection.
`Execution.Discrete.EffectivePathLaw` packages all requested horizons as a
coherent query family: each answer is an exact `FiniteLaw`, and truncating a
later answer preserves every executable Boolean cylinder mass at the earlier
horizon.
`Execution.Discrete.EffectivePathUtility` evaluates exact rational prefix
observables on those coherent families and proves that a cylinder observable's
expectation is unchanged by asking for a longer horizon.
`Execution.Discrete.CertifiedPathApproximation` computes exact rational centers
and declared scheme intervals for state/event prefix approximations, including
bounded and proof-terminating least-horizon searches.  An analytic target still
requires a separate approximation certificate.
`Execution.Discrete.DiscountedPathUtility` specializes that interface to
absolute-time rational rewards with `0 ≤ γ < 1`: horizon `H` sums offsets
`0,...,H-1`, uses the geometric radius `B * γ^H / (1-γ)`, and proves that the
radius reaches every positive rational tolerance.
`Execution.Discrete.FiniteCompleteEventPath` maps a bounded event-prefix law
to a finite law of on-demand terminal-absorbing complete event paths; its
positive-support certificate proves legality without entering the runtime
construction.
`Execution.Discrete.RealizedInformation` compiles a finite abstract-action law
and a prefix-dependent finite realization law by `FiniteLaw.bind`; its
dependent result type keeps every realized action in the current state fiber.
`Execution.Discrete.EffectiveKernelBehavioralProfile` combines those finite
abstract and realization laws with executable terminal and chance data, then
exposes the compiled event policy and coherent all-horizon prefix queries.
`Execution.FinitePayoff` evaluates exact rational observables and stopped
terminal payoffs directly on complete Arena histories or state/event prefixes;
route-dependent values are therefore not collapsed to endpoint states.
`Execution.FiniteCompletePath` replays a bounded law as a finite law of
on-demand absorbing paths when positive-support termination at the supplied
horizon is certified.
`Execution.Discrete.ConditionalContinuation` computes finite Bayes
continuations on complete Arena histories and state/action-recording prefixes;
impossible observations remain explicit as `none`.
`Execution.Discrete.ContinuationTruncation` computes exact stopped centers,
unfinished masses, error radii, and bounded or proof-guarded least-horizon
searches from any complete prefix while preserving its absolute clock.
`Execution.Discrete.ObservedChance` compiles the original behavioral and chance
`FiniteLaw` values directly to action-recording event execution; terminal
detection remains an explicit algorithm input.
`Execution.Truncation` supplies exact stopped-payoff centers, unfinished-mass
radii, budgeted horizon search, and least-horizon search under an explicit
existence proof.

Measure-valued infinite discrete paths are available from
`Interface.Execution.Infinite`; the former combined
`Interface.Execution.Discrete` path was deleted during pre-stability.
-/
