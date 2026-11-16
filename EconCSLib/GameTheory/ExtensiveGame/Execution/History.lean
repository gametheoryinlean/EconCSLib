/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Basic
import EconCSLib.GameTheory.ExtensiveGame.Execution.Reachability
import EconCSLib.GameTheory.ExtensiveGame.Structural.History

/-!
# EconCSLib.GameTheory.ExtensiveGame.Execution.History

Payoff-aware compatibility for history unfolding.

## Main definitions

* `ExtensiveGame.unfold` — the corresponding unfolding of a game, preserving
  movers and payoffs at history endpoints.

The payoff-free Arena and `ControlledGame` history APIs live in
`Structural.History`; this module retains the historical payoff-aware adapter.
-/

namespace ExtensiveGame

variable {N U : Type*}

/-- Unroll an extensive game into its history tree.

Movers and payoffs are read from the endpoint world state.  Observation and
information-state layers may instead distinguish histories with the same
endpoint. -/
def unfold (G : ExtensiveGame N U) : ExtensiveGame N U where
  State := G.toArena.HistoryFrom G.init
  Action := fun h => G.Action h.1
  next := fun h a => ⟨G.next h.1 a, h.2.snoc a⟩
  init := Arena.HistoryFrom.nil G.toArena G.init
  mover := fun h => G.mover h.1
  payoff := fun h i => G.payoff h.1 i

@[simp]
theorem unfold_init (G : ExtensiveGame N U) :
    G.unfold.init = Arena.HistoryFrom.nil G.toArena G.init := rfl

@[simp]
theorem unfold_next (G : ExtensiveGame N U)
    (h : G.toArena.HistoryFrom G.init) (a : G.Action h.1) :
    G.unfold.next h a = ⟨G.next h.1 a, h.2.snoc a⟩ := rfl

@[simp]
theorem unfold_mover (G : ExtensiveGame N U)
    (h : G.toArena.HistoryFrom G.init) :
    G.unfold.mover h = G.mover h.1 := rfl

@[simp]
theorem unfold_payoff (G : ExtensiveGame N U)
    (h : G.toArena.HistoryFrom G.init) (i : N) :
    G.unfold.payoff h i = G.payoff h.1 i := rfl

@[simp]
theorem unfold_isTerminal_iff (G : ExtensiveGame N U)
    (h : G.toArena.HistoryFrom G.init) :
    G.unfold.isTerminal h ↔ G.isTerminal h.1 := Iff.rfl

/-- History unfolding preserves the absence of chance nodes. -/
theorem unfold_noChance (G : ExtensiveGame N U) (h : G.NoChance) :
    G.unfold.NoChance := by
  intro s hs
  exact h s.1 hs

/-- Every history-state is reachable from the initial empty history in the
unfolded game. -/
theorem unfold_isReachable (G : ExtensiveGame N U)
    (h : G.toArena.HistoryFrom G.init) :
    G.unfold.IsReachable h :=
  h.2.reachableInUnfolding G.toArena G.init

end ExtensiveGame
