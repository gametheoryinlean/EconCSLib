/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Strategy

/-!
# EconCSLib.GameTheory.ExtensiveGame.Play

Playing a game: given strategies, compute the path and outcome.

## Main definitions

* `Arena.play` — compute the path of states from a starting state (with fuel)
* `Arena.terminalState` — the terminal state reached (with fuel)

## Design note

Since Arena supports infinite games, `play` uses fuel (max steps) to ensure
termination. For finite games, sufficient fuel always reaches a terminal state.
-/

namespace Arena

variable (A : Arena)

/-- Play the game for at most `fuel` steps, using `choose` to pick actions.
    Returns the sequence of states visited. -/
def play (choose : (s : A.State) → A.Action s)
    (start : A.State) : (fuel : ℕ) → List A.State
  | 0 => [start]
  | n + 1 => start :: play choose (A.next start (choose start)) n

/-- The final state after at most `fuel` steps. -/
def finalState (choose : (s : A.State) → A.Action s)
    (start : A.State) : (fuel : ℕ) → A.State
  | 0 => start
  | n + 1 => finalState choose (A.next start (choose start)) n

theorem finalState_zero (choose : (s : A.State) → A.Action s) (s : A.State) :
    A.finalState choose s 0 = s := rfl

theorem finalState_succ (choose : (s : A.State) → A.Action s) (s : A.State) (n : ℕ) :
    A.finalState choose s (n + 1) = A.finalState choose (A.next s (choose s)) n := rfl

end Arena

namespace ExtensiveGame

variable {N : Type*} {U : Type*} (G : ExtensiveGame N U)

/-- Play the game from `init` for at most `fuel` steps.
    Requires a default action chooser for all states (including chance). -/
def play (choose : (s : G.State) → G.Action s) (fuel : ℕ) : List G.State :=
  G.toArena.play choose G.init fuel

/-- The final state reached from `init` after at most `fuel` steps. -/
def finalState (choose : (s : G.State) → G.Action s) (fuel : ℕ) : G.State :=
  G.toArena.finalState choose G.init fuel

/-- Payoff at the final state for player `i`. -/
def finalPayoff (choose : (s : G.State) → G.Action s) (fuel : ℕ) (i : N) : U :=
  G.payoff (G.finalState choose fuel) i

end ExtensiveGame
