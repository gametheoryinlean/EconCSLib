/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Execution.Reachability

/-!
# EconCSLib.GameTheory.ExtensiveGame.Subgame

Subgames in the Arena framework.

In a state-space game, a subgame starting at state `s` is simply the
same game with `init := s`. The arena (dynamics) doesn't change — only
the starting point.

## Main definitions

* `ExtensiveGame.reachableSubgameAt` — the subtype subgame restricted to states
  reachable from a root.
* `ExtensiveGame.subgameAt` — the subgame starting at state `s`

The underlying reachability relation lives in the canonical
`Execution.Reachability` module.

## References

* [MSZ] Definition 3.11, Definition 7.2
-/

namespace ExtensiveGame

variable {N : Type*} {U : Type*}

/-- The subgame starting at state `s`: same arena, different starting point. -/
def subgameAt (G : ExtensiveGame N U) (s : G.State) : ExtensiveGame N U :=
  { G with init := s }

/-- The arena of a subgame is the same arena. -/
theorem subgameAt_arena (G : ExtensiveGame N U) (s : G.State) :
    (G.subgameAt s).toArena = G.toArena := rfl

/-- The subgame whose state space is restricted to states reachable from
`root`.

The older `subgameAt` view changes only the initial state. This subtype version
is useful when a proof needs to express that deviations are local to the subtree
below `root`. -/
def reachableSubgameAt (G : ExtensiveGame iota U) (root : G.State) :
    ExtensiveGame iota U where
  State := {s : G.State // Arena.Reachable G.toArena root s}
  Action := fun s => G.Action s.1
  next := fun s a => ⟨G.next s.1 a, s.2.step' a⟩
  init := ⟨root, Arena.Reachable.refl _⟩
  mover := fun s => G.mover s.1
  payoff := fun s i => G.payoff s.1 i

@[simp]
theorem reachableSubgameAt_init (G : ExtensiveGame iota U) (root : G.State) :
    (G.reachableSubgameAt root).init = ⟨root, Arena.Reachable.refl _⟩ := rfl

@[simp]
theorem reachableSubgameAt_mover (G : ExtensiveGame iota U) (root : G.State)
    (s : (G.reachableSubgameAt root).State) :
    (G.reachableSubgameAt root).mover s = G.mover s.1 := rfl

@[simp]
theorem reachableSubgameAt_payoff (G : ExtensiveGame iota U) (root : G.State)
    (s : (G.reachableSubgameAt root).State) (i : iota) :
    (G.reachableSubgameAt root).payoff s i = G.payoff s.1 i := rfl

@[simp]
theorem reachableSubgameAt_next (G : ExtensiveGame iota U) (root : G.State)
    (s : (G.reachableSubgameAt root).State)
    (a : (G.reachableSubgameAt root).Action s) :
    (G.reachableSubgameAt root).next s a = ⟨G.next s.1 a, s.2.step' a⟩ := rfl

end ExtensiveGame
