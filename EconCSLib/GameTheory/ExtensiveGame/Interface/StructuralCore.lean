/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Structural.Basic
import EconCSLib.GameTheory.ExtensiveGame.Structural.Reachability
import EconCSLib.GameTheory.ExtensiveGame.Structural.History
import EconCSLib.GameTheory.ExtensiveGame.Execution.CompletePlay
import EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled

/-!
# Structural core facade

The narrow canonical pre-stability import for the payoff-free structural
semantics of extensive games. It exposes only the Arena dynamics, controlled
dynamics, finite reachability, typed histories, measure-free complete plays,
and the payoff-free controlled information/strategy carrier.

Structural termination, bounded execution, finite-law or measurable execution,
objectives, winning predicates, lawful-subgame and recall certificates,
payoff-aware compatibility types, relations, equilibrium, simulation, and
compilers are deliberately outside this facade.

In particular, this facade does not transitively import the payoff-aware
`ExtensiveGame` structure from `ExtensiveGame.Basic`.

`Interface.Core` remains the broader governed Foundation Facade for clients
that also need finite/recall/subgame certificates and bounded
deterministic/finite-law execution.
-/
