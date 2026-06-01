/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.GameTreeNE
import Mathlib.Algebra.Order.Ring.Rat

/-!
# EconCSLib.Examples.CandidateChoice

A three-player candidate-choice game in the `GameTree` framework.

The game has three players, Eric, Larry, and Sergey. They sequentially vote for
one of three candidates: Lee, Rebecca, or John. If at least two players vote for
the same candidate, that candidate is accepted; if all three votes are distinct,
the outcome is rejected.

The file gives a compact finite perfect-information example and verifies that
the general `GameTree` equilibrium theorems apply to it.
-/

namespace Examples.CandidateChoice

open GameTree

/-! ### Players, candidates, and outcomes -/

/-- The three voters in the candidate-choice game. -/
inductive Player
  | Eric
  | Larry
  | Sergey
  deriving DecidableEq, Repr

/-- The candidates that can be chosen by each voter. -/
inductive Candidate
  | Lee
  | Rebecca
  | John
  deriving DecidableEq, Repr

/-- The final result of the voting process. -/
inductive Outcome
  | Accepted (c : Candidate)
  | Rejected
  deriving DecidableEq, Repr

open Player Candidate Outcome

/-! ### Payoffs -/

/-- Player utilities over final outcomes.

The preferences are intentionally asymmetric:

* Eric prefers Lee, then Rebecca, then John.
* Larry prefers Rebecca, then John, then Lee.
* Sergey prefers John, then Lee, then Rebecca.
* All players rank rejection lowest.
-/
def utility : Player → Outcome → ℚ
  | Eric, Accepted Lee => 3
  | Eric, Accepted Rebecca => 2
  | Eric, Accepted John => 1
  | Eric, Rejected => 0
  | Larry, Accepted Rebecca => 3
  | Larry, Accepted John => 2
  | Larry, Accepted Lee => 1
  | Larry, Rejected => 0
  | Sergey, Accepted John => 3
  | Sergey, Accepted Lee => 2
  | Sergey, Accepted Rebecca => 1
  | Sergey, Rejected => 0

/-- Convert an outcome into the payoff vector required by `GameTree`. -/
def payoff (o : Outcome) : Player → ℚ :=
  fun p => utility p o

/-- Terminal tree for a final outcome. -/
def terminal (o : Outcome) : GameTree Player ℚ :=
  Leaf (payoff o)

/-! ### Voting rule -/

/-- Majority rule for the three sequential votes.

If two or more votes agree, the agreed candidate is accepted. If all three votes
are different, the outcome is rejected. -/
def majorityOutcome (a b c : Candidate) : Outcome :=
  match a, b, c with
  | Lee, Lee, _ => Accepted Lee
  | Lee, _, Lee => Accepted Lee
  | _, Lee, Lee => Accepted Lee
  | Rebecca, Rebecca, _ => Accepted Rebecca
  | Rebecca, _, Rebecca => Accepted Rebecca
  | _, Rebecca, Rebecca => Accepted Rebecca
  | John, John, _ => Accepted John
  | John, _, John => Accepted John
  | _, John, John => Accepted John
  | _, _, _ => Rejected

/-! ### Voting-rule lemmas -/

/-- If the first two voters choose the same candidate, that candidate is accepted. -/
@[simp]
theorem majorityOutcome_first_second_same (a c : Candidate) :
    majorityOutcome a a c = Accepted a := by
  cases a <;> cases c <;> rfl

/-- If the first and third voters choose the same candidate, that candidate is accepted. -/
@[simp]
theorem majorityOutcome_first_third_same (a b : Candidate) :
    majorityOutcome a b a = Accepted a := by
  cases a <;> cases b <;> rfl

/-- If the last two voters choose the same candidate, that candidate is accepted. -/
@[simp]
theorem majorityOutcome_second_third_same (a b : Candidate) :
    majorityOutcome b a a = Accepted a := by
  cases a <;> cases b <;> rfl

/-- If all three voters choose pairwise distinct candidates, no candidate is accepted. -/
theorem majorityOutcome_pairwise_distinct {a b c : Candidate}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    majorityOutcome a b c = Rejected := by
  cases a <;> cases b <;> cases c <;> simp [majorityOutcome] at *

/-! ### Game tree -/

/-- Sergey's final choice after Eric and Larry have already voted.

Children are ordered as Sergey's vote for Lee, Rebecca, and John. -/
def sergeyChoice (ericVote larryVote : Candidate) : GameTree Player ℚ :=
  Node Sergey
    (terminal (majorityOutcome ericVote larryVote Lee))
    [ terminal (majorityOutcome ericVote larryVote Rebecca),
      terminal (majorityOutcome ericVote larryVote John) ]

/-- Larry's choice after Eric has voted.

Children are ordered as Larry's vote for Lee, Rebecca, and John. -/
def larryChoice (ericVote : Candidate) : GameTree Player ℚ :=
  Node Larry
    (sergeyChoice ericVote Lee)
    [ sergeyChoice ericVote Rebecca,
      sergeyChoice ericVote John ]

/-- The full candidate-choice game.

Children are ordered as Eric's vote for Lee, Rebecca, and John. -/
def candidateChoiceGame : GameTree Player ℚ :=
  Node Eric
    (larryChoice Lee)
    [ larryChoice Rebecca,
      larryChoice John ]

/-! ### Basic checks -/

example : utility Eric (Accepted Lee) = 3 := rfl

example : utility Larry (Accepted Rebecca) = 3 := rfl

example : utility Sergey (Accepted John) = 3 := rfl

example : majorityOutcome Lee Rebecca Lee = Accepted Lee := rfl

example : majorityOutcome Lee Rebecca Rebecca = Accepted Rebecca := rfl

example : majorityOutcome Lee Rebecca John = Rejected := by
  exact majorityOutcome_pairwise_distinct (by decide) (by decide) (by decide)

example :
    children (sergeyChoice Lee Rebecca) =
      [ terminal (Accepted Lee), terminal (Accepted Rebecca), terminal Rejected ] := rfl

example :
    children candidateChoiceGame =
      [larryChoice Lee, larryChoice Rebecca, larryChoice John] := rfl

example : larryChoice Rebecca ∈ children candidateChoiceGame := by
  simp [candidateChoiceGame, children]

example : Subtree (larryChoice John) candidateChoiceGame := by
  unfold candidateChoiceGame
  exact Subtree.tail_mem Eric (larryChoice Lee) [larryChoice Rebecca, larryChoice John]
    (by simp)

/-- A deeper Sergey subgame is also a subtree of the full game.

This uses `Subtree.trans`: the Sergey subgame is inside Larry's subgame, and
Larry's subgame is inside the full candidate-choice game. -/
theorem sergeyChoice_Lee_Rebecca_subtree_candidateChoiceGame :
    Subtree (sergeyChoice Lee Rebecca) candidateChoiceGame := by
  have h_sergey_larry : Subtree (sergeyChoice Lee Rebecca) (larryChoice Lee) := by
    unfold larryChoice
    exact Subtree.tail_mem Larry (sergeyChoice Lee Lee)
      [sergeyChoice Lee Rebecca, sergeyChoice Lee John] (by simp)
  have h_larry_game : Subtree (larryChoice Lee) candidateChoiceGame := by
    unfold candidateChoiceGame
    exact Subtree.head Eric (larryChoice Lee) [larryChoice Rebecca, larryChoice John]
  exact Subtree.trans h_sergey_larry h_larry_game

/-! ### Equilibrium existence via the library theorem -/

/-- The candidate-choice game has a subgame-perfect equilibrium by Kuhn's theorem. -/
theorem candidateChoice_has_spe : ∃ σ : Strategy Player ℚ, IsSubgamePerfect σ :=
  Kuhn_exists_SPE

/-- The candidate-choice game has a Nash equilibrium at the root. -/
theorem candidateChoice_has_ne :
    ∃ σ : Strategy Player ℚ, IsNashEquilibrium σ candidateChoiceGame :=
  Kuhn_exists_NE candidateChoiceGame

end Examples.CandidateChoice
