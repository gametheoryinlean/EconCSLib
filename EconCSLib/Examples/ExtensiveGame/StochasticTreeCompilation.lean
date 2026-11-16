/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Interface.Compilation.Discrete
import Mathlib.Tactic.NormNum

/-!
# Stochastic-tree compilation regression

This example checks the public discrete-compilation facade, the exact
constructor chance law at the root, and the bounded endpoint/payoff-law
preservation theorems for `StochasticGameTree`.

It also contains an opt-in finite-evaluation prototype: `requiredFuel`
enumerates every child to compute a sufficient horizon, and
`totalExpectedPayoff` evaluates by structural recursion while retaining the
complete occurrence path. `totalExpectedPayoff_eq_expectedPayoffWithFuel`
proves agreement with the existing evaluator at every sufficient horizon.
These declarations are experimental example code, not additions to the frozen
frontend API. Real payoffs remain supplied mathematical values; finite real
arithmetic is not an arbitrary-real numerical approximation algorithm.
-/

namespace Examples.ExtensiveGame.StochasticTreeCompilation

open StochasticGameTree

section FiniteEvaluation

variable {N : Type*}

/-- A sufficient horizon obtained by enumerating all children. A leaf needs
one unit because the bounded evaluator returns zero at fuel zero. -/
def requiredFuel : StochasticGameTree N → ℕ
  | .Leaf _ => 1
  | .Player _ _ child => (Finset.univ.sup fun choice => requiredFuel (child choice)) + 1
  | .Chance _ child _ => (Finset.univ.sup fun choice => requiredFuel (child choice)) + 1

/-- Every player-node child needs strictly less fuel than its parent. -/
theorem requiredFuel_child_lt_player (mover : N) (arity : ℕ)
    (child : Fin (arity + 1) → StochasticGameTree N) (choice : Fin (arity + 1)) :
    requiredFuel (child choice) < requiredFuel (.Player mover arity child) := by
  exact Nat.lt_succ_of_le
    (Finset.le_sup (f := fun choice => requiredFuel (child choice)) (Finset.mem_univ choice))

/-- Every chance-node child needs strictly less fuel, including zero-mass
children: the bound depends on the complete tree, not the law's support. -/
theorem requiredFuel_child_lt_chance (arity : ℕ)
    (child : Fin (arity + 1) → StochasticGameTree N)
    (law : FiniteLaw (Fin (arity + 1))) (choice : Fin (arity + 1)) :
    requiredFuel (child choice) < requiredFuel (.Chance arity child law) := by
  exact Nat.lt_succ_of_le
    (Finset.le_sup (f := fun choice => requiredFuel (child choice)) (Finset.mem_univ choice))

/-- Structural finite-tree evaluation with the original occurrence path and
exact rational chance weights. No external fuel or termination proof is needed. -/
def totalExpectedPayoff (policy : Policy N) (path : List ℕ)
    (tree : StochasticGameTree N) (i : N) : ℝ :=
  match tree with
  | .Leaf payoff => payoff i
  | .Player mover arity child =>
      let choice := policy path mover arity child
      totalExpectedPayoff policy (path ++ [choice.1]) (child choice) i
  | .Chance _arity child law =>
      (law.atoms.map fun atom =>
        (atom.2 : ℝ) *
          totalExpectedPayoff policy (path ++ [atom.1.1]) (child atom.1) i).sum

/-- The structurally computed bound suffices for every policy, initial path,
and player. Larger fuel gives the same total expectation. -/
theorem totalExpectedPayoff_eq_expectedPayoffWithFuel
    (tree : StochasticGameTree N) (policy : Policy N) (path : List ℕ)
    (i : N) (fuel : ℕ) (hfuel : requiredFuel tree ≤ fuel) :
    totalExpectedPayoff policy path tree i =
      expectedPayoffWithFuel fuel policy path tree i := by
  induction tree generalizing fuel path with
  | Leaf payoff =>
      cases fuel with
      | zero => simp [requiredFuel] at hfuel
      | succ fuel => rfl
  | Player mover arity child ih =>
      cases fuel with
      | zero => simp [requiredFuel] at hfuel
      | succ fuel =>
          apply ih (policy path mover arity child)
          have := requiredFuel_child_lt_player mover arity child (policy path mover arity child)
          omega
  | Chance arity child law ih =>
      cases fuel with
      | zero => simp [requiredFuel] at hfuel
      | succ fuel =>
          simp only [totalExpectedPayoff, expectedPayoffWithFuel]
          apply congrArg List.sum
          apply List.map_congr_left
          intro atom _
          rw [ih atom.1 (path := path ++ [atom.1.1]) (fuel := fuel) (by
            have := requiredFuel_child_lt_chance arity child law atom.1
            omega)]

end FiniteEvaluation

section TotalEvaluationRegression

/-- Nonuniform, nondegenerate rational weights for the three root occurrences. -/
def unevenLaw : FiniteLaw (Fin 3) where
  atoms := [(0, 1 / 2), (1, 1 / 3), (2, 1 / 6)]
  normalized := by norm_num

/-- The same decision subtree is visited at two different root paths. -/
def repeatedDecision : StochasticGameTree Unit :=
  .Player () 1 fun choice => .Leaf fun _ => if choice = 0 then 2 else -4

/-- Leaves occur at depths one, two, and three. The final two branches share
`repeatedDecision`, directly and through a one-child player node. -/
def unevenGame : StochasticGameTree Unit :=
  .Chance 2 (fun choice =>
    if choice.1 = 0 then .Leaf (fun _ => 5)
    else if choice.1 = 1 then repeatedDecision
    else .Player () 0 (fun _ => repeatedDecision)) unevenLaw

/-- Select the second child exactly at path `[2, 0]` when it is available;
select the first child elsewhere, including all one-child nodes. -/
def occurrencePolicy : Policy Unit :=
  fun path _mover arity _child =>
    if h : path = [2, 0] ∧ 0 < arity then ⟨1, by omega⟩
    else ⟨0, Nat.zero_lt_succ arity⟩

/-- The maximum is taken over all branches, not only the first child. -/
theorem unevenGame_requiredFuel : requiredFuel unevenGame = 4 := by decide

/-- A leaf is evaluated by the total evaluator immediately, but the existing
bounded interface still needs fuel one even for a nonzero leaf. -/
theorem leaf_fuel_boundary :
    totalExpectedPayoff headPolicy [] (.Leaf (fun _ : Unit => 7)) () = 7 ∧
    expectedPayoffWithFuel 0 headPolicy [] (.Leaf (fun _ : Unit => 7)) () = 0 ∧
    expectedPayoffWithFuel 1 headPolicy [] (.Leaf (fun _ : Unit => 7)) () = 7 := by
  exact ⟨rfl, rfl, rfl⟩

/-- Equal subtree values retain distinct choices at their two occurrences. -/
theorem repeatedDecision_occurrence_payoffs :
    totalExpectedPayoff occurrencePolicy [1] repeatedDecision () = 2 ∧
    totalExpectedPayoff occurrencePolicy [2, 0] repeatedDecision () = -4 := by
  norm_num [totalExpectedPayoff, repeatedDecision, occurrencePolicy]

/-- Exact weighted total evaluation preserves both the chance weights and
the different choices at the repeated subtree occurrences. -/
theorem unevenGame_total_payoff :
    totalExpectedPayoff occurrencePolicy [] unevenGame () = 5 / 2 := by
  dsimp [totalExpectedPayoff, unevenGame, unevenLaw, repeatedDecision, occurrencePolicy]
  norm_num

/-- An incoming path is retained rather than reset: prefixing `[7]` changes
the later occurrence choices and hence the total expectation. -/
theorem unevenGame_prefixed_payoff :
    totalExpectedPayoff occurrencePolicy [7] unevenGame () = 7 / 2 := by
  dsimp [totalExpectedPayoff, unevenGame, unevenLaw, repeatedDecision, occurrencePolicy]
  norm_num

/-- At fuel three the deepest negative payoff is still truncated to zero. -/
theorem unevenGame_insufficient_fuel :
    expectedPayoffWithFuel 3 occurrencePolicy [] unevenGame () = 19 / 6 := by
  dsimp [expectedPayoffWithFuel, unevenGame, unevenLaw, repeatedDecision, occurrencePolicy]
  norm_num

/-- The computed bound supplies the existing root interface's horizon. -/
theorem unevenGame_at_requiredFuel :
    expectedPayoffAtFuel (requiredFuel unevenGame) occurrencePolicy unevenGame () = 5 / 2 := by
  rw [expectedPayoffAtFuel,
    ← totalExpectedPayoff_eq_expectedPayoffWithFuel unevenGame occurrencePolicy [] ()
      (requiredFuel unevenGame) le_rfl]
  exact unevenGame_total_payoff

-- Execute the bound and the two occurrence decisions without inspecting real values.
/-- info: (1, 4, 0, 1) -/
#guard_msgs in
#eval (requiredFuel (.Leaf (fun _ : Unit => (7 : ℝ))), requiredFuel unevenGame,
  (occurrencePolicy [1] () 1 (fun _ => repeatedDecision)).1,
  (occurrencePolicy [2, 0] () 1 (fun _ => repeatedDecision)).1)

end TotalEvaluationRegression

/-- The normalized uniform law on the two fair-coin child occurrences. -/
def fairCoinLaw : FiniteLaw (Fin 2) where
  atoms := [(0, 1 / 2), (1, 1 / 2)]
  normalized := by norm_num

/-- Each occurrence has probability one half under `fairCoinLaw`. -/
theorem fairCoinLaw_apply (choice : Fin 2) :
    fairCoinLaw.mass choice = 1 / 2 := by
  fin_cases choice <;>
    norm_num [fairCoinLaw, FiniteLaw.mass, FiniteLaw.eventMass]

/-- The real-valued finite weights of `fairCoinLaw` sum to one. -/
theorem fairCoinLaw_total :
    ∑ choice : Fin 2, fairCoinLaw.mass choice = 1 := by
  rw [Fin.sum_univ_two]
  norm_num [fairCoinLaw_apply]

/-- A one-step fair coin game for examples and CI regression checks. -/
def fairCoinGame : StochasticGameTree (Fin 2) :=
  StochasticGameTree.Chance 1
    (fun choice =>
      if choice = 0 then
        StochasticGameTree.Leaf (fun i => if i = 0 then 1 else 0)
      else
        StochasticGameTree.Leaf (fun i => if i = 0 then 0 else 1))
    fairCoinLaw

/-- At fuel two, the fair-coin regression game gives player zero expected
payoff one half. -/
theorem fairCoin_expected_player0 :
    expectedPayoffAtFuel 2 (headPolicy : Policy (Fin 2))
      fairCoinGame 0 = 1 / 2 := by
  norm_num [expectedPayoffAtFuel, expectedPayoffWithFuel, fairCoinGame,
    fairCoinLaw]

/-- Empty complete history of the fair-coin source tree. -/
def initialHistory :
    (toExtensiveGame fairCoinGame).toArena.HistoryFrom fairCoinGame :=
  Arena.HistoryFrom.nil
    (toExtensiveGame fairCoinGame).toArena fairCoinGame

/-- The fair-coin root is a genuine nonterminal chance state. -/
theorem initialHistory_isChance :
    (toExtensiveGame fairCoinGame).isChanceState
      initialHistory.1 := by
  constructor
  · rfl
  · exact
      toExtensiveGame_not_isTerminal_chance
        fairCoinGame 1
        (fun choice =>
          if choice = 0 then
            .Leaf (fun i => if i = 0 then 1 else 0)
          else
            .Leaf (fun i => if i = 0 then 0 else 1))
        fairCoinLaw

/-- The compiler does not reconstruct or renormalize the source coin law. -/
theorem compiledChanceKernel_eq_fairCoinLaw :
    (toObservedChanceGame fairCoinGame).chanceKernel
        initialHistory initialHistory_isChance =
      fairCoinLaw := by
  rfl

/-- One bounded compiled step has exactly the recursively defined source
endpoint law after complete histories are forgotten. -/
theorem compiledEndpointLaw_one :
    ((toExtensiveGame fairCoinGame).toArena.stochasticHistoryLawFrom
        (ExtensiveGame.ObservedChanceGame.BehavioralProfile.toHistoryPolicy
          (toObservedChanceGame fairCoinGame)
          (policyToBehavioralProfile fairCoinGame headPolicy))
        initialHistory 1).map Sigma.fst =
      endpointLawWithFuel 1 headPolicy [] fairCoinGame := by
  simpa [initialHistory] using
    stochasticHistoryLawFrom_map_endpoint
      fairCoinGame headPolicy initialHistory 1

/-- The same execution also preserves the complete vector-valued payoff law. -/
theorem compiledPayoffLaw_one :
    ((toExtensiveGame fairCoinGame).toArena.stochasticHistoryLawFrom
        (ExtensiveGame.ObservedChanceGame.BehavioralProfile.toHistoryPolicy
          (toObservedChanceGame fairCoinGame)
          (policyToBehavioralProfile fairCoinGame headPolicy))
        initialHistory 1).map
          (fun history =>
            (toExtensiveGame fairCoinGame).payoff history.1) =
      (endpointLawWithFuel 1 headPolicy [] fairCoinGame).map
        statePayoff := by
  simpa [initialHistory] using
    stochasticHistoryLawFrom_map_payoff
      fairCoinGame headPolicy initialHistory 1

end Examples.ExtensiveGame.StochasticTreeCompilation
