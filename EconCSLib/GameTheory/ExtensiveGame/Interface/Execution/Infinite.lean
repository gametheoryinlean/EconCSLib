/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Interface.Execution.Finite
import EconCSLib.GameTheory.ExtensiveGame.Execution.InfiniteTrajectory
import EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Law.DiscretePath
import EconCSLib.GameTheory.ExtensiveGame.Observed.InfiniteExecution

/-!
# Infinite discrete event-time EFG execution

Recommended pre-stability import for executable finite prefixes and supplied
terminal-absorbing probability laws on infinite natural-number-indexed
histories indexed by discrete `FiniteLaw` policies.

It extends `Interface.Execution.Finite` with the representation-independent
lawful probability carrier, its supplied discrete behavioral adapter,
coordinate-marginal certificates, almost-sure termination predicates, exact
bounded unfinished mass, and partial terminal search/payoff operations.
MeasureTheory is intrinsic to the supplied infinite-path surface even though
every local action law and bounded path marginal is a `FiniteLaw`. Non-atomic
`MeasurableKernelArena` execution remains in `Interface.Execution.Analytic`.
-/
