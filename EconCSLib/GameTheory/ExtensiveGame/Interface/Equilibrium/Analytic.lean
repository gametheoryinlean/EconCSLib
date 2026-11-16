/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Interface.Equilibrium.Discrete
import EconCSLib.GameTheory.ExtensiveGame.Interface.Execution.Analytic
import EconCSLib.GameTheory.ExtensiveGame.Simulation.Equilibrium.FinitePayoff
import EconCSLib.GameTheory.ExtensiveGame.Simulation.Equilibrium.EffectivePathUtility
import EconCSLib.GameTheory.ExtensiveGame.Simulation.Equilibrium.Outcome
import EconCSLib.GameTheory.ExtensiveGame.Simulation.Continuation.Observed
import EconCSLib.GameTheory.ExtensiveGame.Simulation.Continuation.FiniteConditioning
import EconCSLib.GameTheory.ExtensiveGame.Simulation.Continuation.ObservedConditioning

/-!
# Analytic EFG equilibrium

Recommended pre-stability import for measurable-kernel path utility, constructive equilibrium, absolute-prefix
continuation, and conditional continuation semantics. Exact finite Bayes
continuations are linked to analytic partial trajectories and to finite
marginals of constructive absolute-path continuations without choosing a
regular conditional distribution at null prefixes.
Exact rational finite-history and state/event-prefix payoffs are likewise
identified with the corresponding finite Dirac, supplied-path coordinate,
and partial-trajectory integrals; numerical definitions remain in the finite
execution tier.
These finite conditioning and payoff results are semantic compatibility
theorems; they do not deprecate the more general analytic definitions.
Finite rational simple observables receive a correctness bridge to
`PathUtility.expectedUtility`. These interfaces require explicit observable
representations; they do not enumerate arbitrary integrable functions.

This layer reuses the complete finite-fuel pure/finite-law equilibrium surface from
`Interface.Equilibrium.Discrete` and the analytic execution surface from
`Interface.Execution.Analytic`. Fresh-clock restart and concrete compilation
remain independent higher branches.
-/
