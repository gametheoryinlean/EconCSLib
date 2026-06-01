/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.StrategicGame.Checker
import EconCSLib.GameTheory.StrategicGame.MixedStrategy

/-!
# EconCSLib.Examples.RockPaperScissors

Rock-Paper-Scissors: complete analysis of pure and mixed equilibria.

## Main results

* `rps_no_pure_nash` — no pure Nash equilibrium exists
* `rps_zero_sum` — the game is zero-sum
* `rps_mixed_nash` — uniform (1/3, 1/3, 1/3) is a mixed Nash equilibrium
* `rps_mixed_nash_unique` — uniform is the unique mixed Nash equilibrium

Core finite checks are verified by `native_decide` over `ℚ`.
-/

inductive RPSMove | Rock | Paper | Scissors
  deriving DecidableEq, Repr, Fintype

namespace RockPaperScissors

open RPSMove StrategicGame
open Finset BigOperators

private def rpsPayoff0 : RPSMove → RPSMove → ℚ
  | Rock,     Rock     =>  0
  | Rock,     Paper    => -1
  | Rock,     Scissors =>  1
  | Paper,    Rock     =>  1
  | Paper,    Paper    =>  0
  | Paper,    Scissors => -1
  | Scissors, Rock     => -1
  | Scissors, Paper    =>  1
  | Scissors, Scissors =>  0

@[reducible] def RPS : StrategicGame (Fin 2) ℚ where
  strategy := fun _ => RPSMove
  payoff σ i :=
    if i = 0 then rpsPayoff0 (σ 0) (σ 1)
    else -(rpsPayoff0 (σ 0) (σ 1))

private def profileEquiv : RPS.Profile ≃ RPSMove × RPSMove where
  toFun σ := (σ 0, σ 1)
  invFun x := fun i => if i = 0 then x.1 else x.2
  left_inv := by
    intro σ
    funext i
    fin_cases i <;> simp
  right_inv := by
    intro x
    cases x
    simp

private lemma sum_profile_eq (f : RPS.Profile → ℚ) :
    (∑ σ : RPS.Profile, f σ) =
      ∑ s0 : RPSMove, ∑ s1 : RPSMove, f (fun i => if i = 0 then s0 else s1) := by
  rw [Fintype.sum_equiv profileEquiv f
    (fun x : RPSMove × RPSMove => f (fun i => if i = 0 then x.1 else x.2))]
  · rw [Fintype.sum_prod_type]
  · intro σ
    congr 1
    funext i
    fin_cases i <;> simp [profileEquiv]

private lemma sum_rps (f : RPSMove → ℚ) :
    (∑ x : RPSMove, f x) = f Rock + f Paper + f Scissors := by
  rw [show (Finset.univ : Finset RPSMove) = {Rock, Paper, Scissors} by
    ext x
    fin_cases x <;> simp]
  simp
  ring

private lemma eu0_dev_rock (p : MixedProfile RPS) :
    expectedPayoff RPS (deviateMixed RPS p 0 Rock) 0 = p 1 Scissors - p 1 Paper := by
  unfold expectedPayoff
  rw [sum_profile_eq]
  simp [deviateMixed, pureToMixed, RPS]
  rw [sum_rps]
  simp [rpsPayoff0]
  change -((p 1) Paper) + (p 1) Scissors = (p 1) Scissors - (p 1) Paper
  ring_nf

private lemma eu0_dev_paper (p : MixedProfile RPS) :
    expectedPayoff RPS (deviateMixed RPS p 0 Paper) 0 = p 1 Rock - p 1 Scissors := by
  unfold expectedPayoff
  rw [sum_profile_eq]
  simp [deviateMixed, pureToMixed, RPS]
  rw [sum_rps]
  simp [rpsPayoff0]
  rw [sub_eq_add_neg]
  change (p 1).val Rock + -((p 1).val Scissors) =
    (p 1).val Rock + -((p 1).val Scissors)
  rfl

private lemma eu0_dev_scissors (p : MixedProfile RPS) :
    expectedPayoff RPS (deviateMixed RPS p 0 Scissors) 0 = p 1 Paper - p 1 Rock := by
  unfold expectedPayoff
  rw [sum_profile_eq]
  simp [deviateMixed, pureToMixed, RPS]
  rw [sum_rps]
  simp [rpsPayoff0]
  change -((p 1) Rock) + (p 1) Paper = (p 1) Paper - (p 1) Rock
  ring_nf

private lemma eu1_dev_rock (p : MixedProfile RPS) :
    expectedPayoff RPS (deviateMixed RPS p 1 Rock) 1 = p 0 Scissors - p 0 Paper := by
  unfold expectedPayoff
  rw [sum_profile_eq]
  simp [deviateMixed, pureToMixed, RPS]
  rw [sum_rps]
  simp [rpsPayoff0]
  rw [sub_eq_add_neg]
  change (p 0).val Scissors + -((p 0).val Paper) =
    (p 0).val Scissors + -((p 0).val Paper)
  rfl

private lemma eu1_dev_paper (p : MixedProfile RPS) :
    expectedPayoff RPS (deviateMixed RPS p 1 Paper) 1 = p 0 Rock - p 0 Scissors := by
  unfold expectedPayoff
  rw [sum_profile_eq]
  simp [deviateMixed, pureToMixed, RPS]
  rw [sum_rps]
  simp [rpsPayoff0]
  change -((p 0) Scissors) + (p 0) Rock = (p 0) Rock - (p 0) Scissors
  ring_nf

private lemma eu1_dev_scissors (p : MixedProfile RPS) :
    expectedPayoff RPS (deviateMixed RPS p 1 Scissors) 1 = p 0 Paper - p 0 Rock := by
  unfold expectedPayoff
  rw [sum_profile_eq]
  simp [deviateMixed, pureToMixed, RPS]
  rw [sum_rps]
  simp [rpsPayoff0]
  rw [sub_eq_add_neg]
  change (p 0).val Paper + -((p 0).val Rock) =
    (p 0).val Paper + -((p 0).val Rock)
  rfl

private lemma eu1_eq_neg_eu0 (p : MixedProfile RPS) :
    expectedPayoff RPS p 1 = - expectedPayoff RPS p 0 := by
  unfold expectedPayoff
  rw [sum_profile_eq, sum_profile_eq]
  simp [RPS, rpsPayoff0]

/-! ### Pure analysis -/

theorem rps_no_pure_nash : ¬ ∃ σ : RPS.Profile, IsNashEquilibrium RPS σ := by
  show ¬ ∃ (σ : Fin 2 → RPSMove),
    ∀ (i : Fin 2) (s' : RPSMove), RPS.payoff (deviate σ i s') i ≤ RPS.payoff σ i
  native_decide

theorem rps_zero_sum : ∀ σ : RPS.Profile,
    RPS.payoff σ 0 + RPS.payoff σ 1 = 0 := by
  show ∀ (σ : Fin 2 → RPSMove), RPS.payoff σ 0 + RPS.payoff σ 1 = 0
  native_decide

/-! ### Mixed analysis -/

/-- Uniform mixed strategy: each move with probability 1/3. -/
def uniform : MixedStrategy RPS (i := (0 : Fin 2)) where
  val _ := 1 / 3
  property := ⟨fun _ => by norm_num, by native_decide⟩

-- Both players use the same uniform strategy (RPS is symmetric in strategy type)
def uniformProfile : MixedProfile RPS := fun _ => uniform

/-- The uniform profile is completely mixed: every pure move has positive
    probability for each player. -/
theorem rps_uniform_completely_mixed : IsCompletelyMixedProfile RPS uniformProfile := by
  intro i s
  fin_cases s <;> norm_num [uniformProfile, uniform]

/-- Expected payoff under uniform profile is 0 for player 0. -/
theorem rps_eu_uniform_0 :
    expectedPayoff RPS uniformProfile 0 = 0 := by native_decide

/-- Expected payoff under uniform profile is 0 for player 1. -/
theorem rps_eu_uniform_1 :
    expectedPayoff RPS uniformProfile 1 = 0 := by native_decide

/-- EU when player 0 deviates to any pure strategy is 0. -/
theorem rps_dev0 (s₀ : RPSMove) :
    expectedPayoff RPS (deviateMixed RPS uniformProfile 0 s₀) 0 = 0 := by
  fin_cases s₀ <;> native_decide

/-- EU when player 1 deviates to any pure strategy is 0. -/
theorem rps_dev1 (s₁ : RPSMove) :
    expectedPayoff RPS (deviateMixed RPS uniformProfile 1 s₁) 1 = 0 := by
  fin_cases s₁ <;> native_decide

/-- **Uniform (1/3, 1/3, 1/3) is a mixed Nash equilibrium of RPS.**

    Uses the general n-player definition `IsMixedNashEq`. -/
theorem rps_mixed_nash : IsMixedNashEq RPS uniformProfile := by
  intro who s'
  fin_cases who <;> fin_cases s' <;> native_decide

/-- **Uniqueness**: uniform is the only mixed Nash equilibrium. -/
theorem rps_mixed_nash_unique
    (p : MixedProfile RPS)
    (hN : IsMixedNashEq RPS p) :
    p = uniformProfile := by
  have h0R : p 1 Scissors - p 1 Paper ≤ expectedPayoff RPS p 0 := by
    simpa [eu0_dev_rock] using hN 0 Rock
  have h0P : p 1 Rock - p 1 Scissors ≤ expectedPayoff RPS p 0 := by
    simpa [eu0_dev_paper] using hN 0 Paper
  have h0S : p 1 Paper - p 1 Rock ≤ expectedPayoff RPS p 0 := by
    simpa [eu0_dev_scissors] using hN 0 Scissors
  have h1R : expectedPayoff RPS p 0 ≤ p 0 Paper - p 0 Scissors := by
    have h := hN 1 Rock
    rw [eu1_dev_rock, eu1_eq_neg_eu0] at h
    linarith
  have h1P : expectedPayoff RPS p 0 ≤ p 0 Scissors - p 0 Rock := by
    have h := hN 1 Paper
    rw [eu1_dev_paper, eu1_eq_neg_eu0] at h
    linarith
  have h1S : expectedPayoff RPS p 0 ≤ p 0 Rock - p 0 Paper := by
    have h := hN 1 Scissors
    rw [eu1_dev_scissors, eu1_eq_neg_eu0] at h
    linarith
  have hU_nonneg : 0 ≤ expectedPayoff RPS p 0 := by linarith [h0R, h0P, h0S]
  have hU_nonpos : expectedPayoff RPS p 0 ≤ 0 := by linarith [h1R, h1P, h1S]
  have hU : expectedPayoff RPS p 0 = 0 := le_antisymm hU_nonpos hU_nonneg
  have hp1_sum : p 1 Rock + p 1 Paper + p 1 Scissors = 1 := by
    have h := stdSimplex.sum_eq_one (p 1)
    rw [sum_rps] at h
    exact h
  have hp0_sum : p 0 Rock + p 0 Paper + p 0 Scissors = 1 := by
    have h := stdSimplex.sum_eq_one (p 0)
    rw [sum_rps] at h
    exact h
  have hp1R : p 1 Rock = 1 / 3 := by linarith [h0R, h0P, h0S, hU, hp1_sum]
  have hp1P : p 1 Paper = 1 / 3 := by linarith [h0R, h0P, h0S, hU, hp1_sum]
  have hp1S : p 1 Scissors = 1 / 3 := by linarith [h0R, h0P, h0S, hU, hp1_sum]
  have hp0R : p 0 Rock = 1 / 3 := by linarith [h1R, h1P, h1S, hU, hp0_sum]
  have hp0P : p 0 Paper = 1 / 3 := by linarith [h1R, h1P, h1S, hU, hp0_sum]
  have hp0S : p 0 Scissors = 1 / 3 := by linarith [h1R, h1P, h1S, hU, hp0_sum]
  funext i
  apply stdSimplex.ext
  funext s
  fin_cases i
  · fin_cases s
    · change p 0 Rock = (1 / 3 : ℚ)
      exact hp0R
    · change p 0 Paper = (1 / 3 : ℚ)
      exact hp0P
    · change p 0 Scissors = (1 / 3 : ℚ)
      exact hp0S
  · fin_cases s
    · change p 1 Rock = (1 / 3 : ℚ)
      exact hp1R
    · change p 1 Paper = (1 / 3 : ℚ)
      exact hp1P
    · change p 1 Scissors = (1 / 3 : ℚ)
      exact hp1S

end RockPaperScissors
