/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.GameForm.LimitSPE
import Mathlib.Tactic

/-!
# Boundary regression for finite-to-infinite Nash on declared roots

A horizon-dependent, nonconstant finite payoff strictly selects one strategy
at every fuel, while an unrelated infinite payoff strictly selects the other.
This proves that convergence assumptions in finite-to-infinite transfer of
Nash optimality on declared roots cannot be omitted.
-/

namespace Examples.InfiniteSPEBoundary

/-- One-player family used to expose the missing-convergence boundary. -/
def boundaryForm : IndexedContinuationGameForm (Fin 1) where
  Strategy := fun _ => Bool
  Horizon := ℕ
  Root := Unit
  IsDeclaredRoot := fun _ => True
  Outcome := Bool
  outcome := fun _ _ profile => profile 0

/-- Every finite evaluator strictly favors `false`, with a horizon-dependent
margin. -/
def finitePayoff
    (n : ℕ) (_ : Unit) (profile : (i : Fin 1) → Bool)
    (_ : Fin 1) : ℝ :=
  if profile 0 = true then -((n : ℝ) + 1) else (n : ℝ) + 1

/-- The infinite evaluator reverses the preference and strictly favors
`true`. -/
def infinitePayoff
    (_ : Unit) (profile : (i : Fin 1) → Bool)
    (_ : Fin 1) : ℝ :=
  if profile 0 = true then 1 else 0

/-- Candidate profile selected by every finite evaluator. -/
def finiteWinner : (i : Fin 1) → Bool :=
  fun _ => false

/-- The candidate is Nash on every declared root for every finite evaluator. -/
theorem finiteWinner_isNashOnRoots_at_every_fuel :
    ∀ n,
      boundaryForm.IsNashOnRootsForPayoff
        (finitePayoff n) finiteWinner := by
  intro n root hroot i deviation
  have hi : i = 0 := Fin.eq_zero i
  subst i
  cases deviation
  · simp [finitePayoff, finiteWinner]
  · simp [finitePayoff, finiteWinner]
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith

/-- The same candidate is not Nash on the declared root for the unrelated
infinite evaluator. -/
theorem finiteWinner_not_infiniteNashOnRoots :
    ¬ boundaryForm.IsNashOnRootsForPayoff
        infinitePayoff finiteWinner := by
  intro h
  have hdeviation := h () trivial 0 true
  norm_num [infinitePayoff, finiteWinner] at hdeviation

/-- Finite-index Nash on every declared root does not imply its infinite-payoff
counterpart without a convergence hypothesis relating the payoff families. -/
theorem finiteNashOnRoots_does_not_imply_infiniteNashOnRoots :
    ¬ ((∀ n,
          boundaryForm.IsNashOnRootsForPayoff
            (finitePayoff n) finiteWinner) →
        boundaryForm.IsNashOnRootsForPayoff
          infinitePayoff finiteWinner) := by
  intro himp
  exact
    finiteWinner_not_infiniteNashOnRoots
      (himp finiteWinner_isNashOnRoots_at_every_fuel)

end Examples.InfiniteSPEBoundary
