/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.Math.Probability.FiniteMarkovChain
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.SumOverResidueClass
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# Semantics of the exact finite absorbing-chain solver

The automatically checked finite-step absorption bound gives summable powers.
First-hit probabilities are those of `Chain.run`, including their hit times.
The resulting countable law has total mass one and integrable reward and time.
Cramer's actual rational output is identified with these expectations. The
checker is proved equivalent to survival tending to zero on every supplied
transient state. Analytic expressions occur only in statements and proofs.
-/

namespace FiniteMarkovChain.Chain

open Matrix MeasureTheory
open scoped BigOperators NNReal ENNReal Matrix.Norms.Operator

variable {n m : ℕ} (C : Chain n m)

local notation "Qr" => C.Q.map (Rat.castHom ℝ)
local notation "Rr" => C.R.map (Rat.castHom ℝ)

private theorem norm_pow_bound {k : ℕ} {c : ℚ} (h : C.admissible k c = true) :
    ‖Qr ^ k‖ < 1 := by
  obtain ⟨_, hc, hc1, hrows⟩ := (C.admissible_iff k c).mp h
  have hnonneg (i j : Fin n) : 0 ≤ (Qr ^ k) i j := by
    rw [← Matrix.map_pow]
    change 0 ≤ ((C.Q ^ k) i j : ℝ)
    exact_mod_cast C.pow_nonneg k i j
  have hbound : ‖Qr ^ k‖₊ ≤ (⟨(c : ℝ), by exact_mod_cast hc⟩ : ℝ≥0) := by
    rw [Matrix.linfty_opNNNorm_def, Finset.sup_le_iff]
    intro i _
    apply NNReal.coe_le_coe.mp
    simp only [NNReal.coe_sum, coe_nnnorm, Real.norm_eq_abs,
      abs_of_nonneg (hnonneg i _)]
    rw [← Matrix.map_pow]
    change (∑ j, ((C.Q ^ k) i j : ℝ)) ≤ (c : ℝ)
    exact_mod_cast hrows i
  exact lt_of_le_of_lt (show ‖Qr ^ k‖ ≤ (c : ℝ) from hbound) (by exact_mod_cast hc1)

private theorem summable_powers_of_block {A : Matrix (Fin n) (Fin n) ℝ}
    {k : ℕ} (hk : 0 < k) (hA : ‖A ^ k‖ < 1) : Summable (fun r : ℕ => A ^ r) := by
  letI : NeZero k := ⟨Nat.ne_of_gt hk⟩
  rw [Finset.sum_indicator_mod k (fun r : ℕ => A ^ r)]
  change Summable (fun r => (∑ a : ZMod k, {n : ℕ | (n : ZMod k) = a}.indicator _) r)
  simp only [Finset.sum_apply]
  apply summable_sum
  intro a _
  rw [← ZMod.natCast_zmod_val a, summable_indicator_mod_iff_summable]
  simpa only [pow_add, pow_mul] using
    (summable_geometric_of_norm_lt_one hA).mul_right (A ^ a.val)

/-- Absorption checked on a finite block makes the entire transient series summable. -/
theorem summable_powers {k : ℕ} {c : ℚ} (h : C.admissible k c = true) :
    Summable (fun r : ℕ => Qr ^ r) :=
  summable_powers_of_block ((C.admissible_iff k c).mp h).1 (C.norm_pow_bound h)

/-- The absorption check proves nonsingularity; it is not a supplied inverse. -/
theorem det_ne_zero {k : ℕ} {c : ℚ} (h : C.admissible k c = true) :
    (1 - C.Q).det ≠ 0 := by
  have hs := C.summable_powers h
  have hu : IsUnit (1 - Qr) :=
    isUnit_iff_exists_inv.mpr ⟨∑' r : ℕ, Qr ^ r, hs.one_sub_mul_tsum_pow⟩
  have hd := isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hu)
  have heq : ((1 - C.Q).det : ℝ) = (1 - Qr).det := by
    rw [Rat.cast_det]
    congr 1
    simpa using (Rat.castHom ℝ).mapMatrix.map_sub 1 C.Q
  intro hz
  apply hd
  rw [← heq, hz, Rat.cast_zero]

private theorem summable_weighted_powers_of_block {A : Matrix (Fin n) (Fin n) ℝ}
    {k : ℕ} (hk : 0 < k) (hA : ‖A ^ k‖ < 1) :
    Summable (fun r : ℕ => (r + 1) • A ^ r) := by
  letI : NeZero k := ⟨Nat.ne_of_gt hk⟩
  rw [Finset.sum_indicator_mod k (fun r : ℕ => (r + 1) • A ^ r)]
  change Summable (fun r => (∑ a : ZMod k, {n : ℕ | (n : ZMod k) = a}.indicator _) r)
  simp only [Finset.sum_apply]
  apply summable_sum
  intro a _
  rw [← ZMod.natCast_zmod_val a, summable_indicator_mod_iff_summable]
  have hs := summable_geometric_of_norm_lt_one hA
  have hw := summable_pow_mul_geometric_of_norm_lt_one 1 hA
  simp only [pow_one] at hw
  convert ((hw.mul_right (A ^ a.val)).const_smul k).add
    ((hs.mul_right (A ^ a.val)).const_smul (a.val + 1)) using 1
  funext r
  simp only [nsmul_eq_mul, Nat.cast_add, Nat.cast_mul, Nat.cast_one,
    pow_add, pow_mul, add_mul, mul_assoc, add_assoc, one_mul]

/-- First-hit time has a finite first moment, even when absorption needs several steps. -/
theorem summable_weighted_powers {k : ℕ} {c : ℚ} (h : C.admissible k c = true) :
    Summable (fun r : ℕ => (r + 1) • Qr ^ r) :=
  summable_weighted_powers_of_block ((C.admissible_iff k c).mp h).1 (C.norm_pow_bound h)

private theorem weighted_series_identity {A : Matrix (Fin n) (Fin n) ℝ}
    (hp : Summable (fun r : ℕ => A ^ r))
    (hw : Summable (fun r : ℕ => (r + 1) • A ^ r)) :
    (∑' r : ℕ, (r + 1) • A ^ r) * (1 - A) = ∑' r : ℕ, A ^ r := by
  have hshift : HasSum (fun r : ℕ => r • A ^ r)
      ((∑' r : ℕ, (r + 1) • A ^ r) * A) := by
    rw [← hasSum_nat_add_iff' 1]
    simpa [pow_succ, mul_assoc] using hw.hasSum.mul_right A
  have hd := hw.hasSum.sub hshift
  have heq (r : ℕ) : (r + 1) • A ^ r - r • A ^ r = A ^ r := by
    simp [add_mul]
  simp_rw [heq] at hd
  simpa [mul_sub] using hd.unique hp.hasSum

private theorem hasSum_mulVec {f : ℕ → Matrix (Fin n) (Fin m) ℝ}
    {A : Matrix (Fin n) (Fin m) ℝ} (hf : HasSum f A) (b : Fin m → ℝ) :
    HasSum (fun r => f r *ᵥ b) (A *ᵥ b) := by
  apply Pi.hasSum.mpr
  intro i
  exact hasSum_sum (s := Finset.univ) fun j _ => ((Pi.hasSum.mp (Pi.hasSum.mp hf i) j).mul_right (b j))

private theorem hasSum_mul {f : ℕ → Matrix (Fin n) (Fin n) ℝ}
    {A : Matrix (Fin n) (Fin n) ℝ} (hf : HasSum f A) (B : Matrix (Fin n) (Fin m) ℝ) :
    HasSum (fun r => f r * B) (A * B) := by
  apply Pi.hasSum.mpr
  intro i
  apply Pi.hasSum.mpr
  intro a
  exact hasSum_sum (s := Finset.univ) fun j _ => ((Pi.hasSum.mp (Pi.hasSum.mp hf i) j).mul_right (B j a))

private theorem cast_hit (r : ℕ) : (C.hit r).map (Rat.castHom ℝ) = Qr ^ r * Rr := by
  simp only [hit, Matrix.map_mul, Matrix.map_pow]

private theorem real_row_sum : (1 - Qr) *ᵥ (fun _ => (1 : ℝ)) = Rr *ᵥ (fun _ => 1) := by
  rw [Matrix.sub_mulVec, Matrix.one_mulVec]
  funext i
  simp only [Pi.sub_apply, Matrix.mulVec, dotProduct, mul_one]
  change 1 - (∑ j, (C.Q i j : ℝ)) = (∑ a, (C.R i a : ℝ))
  have h := C.row_sum i
  have hr : (∑ j, (C.Q i j : ℝ)) + (∑ a, (C.R i a : ℝ)) = 1 := by exact_mod_cast h
  linarith

private theorem hasSum_hits {k : ℕ} {c : ℚ} (h : C.admissible k c = true) :
    HasSum (fun r => (C.hit r).map (Rat.castHom ℝ))
      ((∑' r : ℕ, Qr ^ r) * Rr) := by
  simpa only [C.cast_hit] using hasSum_mul (C.summable_powers h).hasSum Rr

private theorem real_hit_nonneg (r : ℕ) (i : Fin n) (a : Fin m) :
    0 ≤ (C.hit r i a : ℝ) := by exact_mod_cast C.hit_nonneg r i a

/-- The eventual first-hit coefficients sum to one. No nontermination mass is discarded. -/
theorem hasSum_firstHit {k : ℕ} {c : ℚ} (h : C.admissible k c = true) (i : Fin n) :
    HasSum (fun r => ∑ a, (C.hit r i a : ℝ)) 1 := by
  have hs := hasSum_mulVec (C.hasSum_hits h) (fun _ => 1)
  have heq : ((∑' r : ℕ, Qr ^ r) * Rr) *ᵥ (fun _ => (1 : ℝ)) = (fun _ => 1) := by
    rw [← Matrix.mulVec_mulVec, ← C.real_row_sum, Matrix.mulVec_mulVec,
      (C.summable_powers h).tsum_pow_mul_one_sub, Matrix.one_mulVec]
  rw [heq] at hs
  simpa only [Matrix.mulVec, dotProduct, mul_one, Matrix.map_apply] using Pi.hasSum.mp hs i

private theorem summable_joint_nonneg {f : ℕ → Fin m → ℝ} (hf : ∀ r a, 0 ≤ f r a)
    (hs : ∀ a, Summable (fun r => f r a)) : Summable (fun p : ℕ × Fin m => f p.1 p.2) := by
  apply (summable_prod_of_nonneg (fun p => hf p.1 p.2)).mpr
  refine ⟨fun _ => (hasSum_fintype _).summable, ?_⟩
  simp only [tsum_fintype]
  exact summable_sum (s := Finset.univ) (fun a _ => hs a)

private theorem summable_firstHit {k : ℕ} {c : ℚ} (h : C.admissible k c = true) (i : Fin n) :
    Summable (fun p : ℕ × Fin m => (C.hit p.1 i p.2 : ℝ)) := by
  apply summable_joint_nonneg (fun r a => C.real_hit_nonneg r i a)
  intro a
  exact (Pi.hasSum.mp (Pi.hasSum.mp (C.hasSum_hits h) i) a).summable

/-- The first-hit law is a probability measure derived from the executed rows. -/
theorem firstHit_probability {k : ℕ} {c : ℚ} (h : C.admissible k c = true) (i : Fin n) :
    IsProbabilityMeasure (Measure.sum fun p : ℕ × Fin m =>
      ENNReal.ofReal (C.hit p.1 i p.2 : ℝ) • Measure.dirac p) := by
  constructor
  rw [Measure.sum_apply _ MeasurableSet.univ]
  simp only [Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
  change (∑' p : ℕ × Fin m, ENNReal.ofReal (C.hit p.1 i p.2 : ℝ)) = 1
  have hs := C.summable_firstHit h i
  have ht : (∑' p : ℕ × Fin m, (C.hit p.1 i p.2 : ℝ)) = 1 := by
    rw [hs.tsum_prod]
    simpa only [tsum_fintype] using (C.hasSum_firstHit h i).tsum_eq
  rw [← ENNReal.ofReal_tsum_of_nonneg
    (fun p : ℕ × Fin m => C.real_hit_nonneg p.1 i p.2) hs, ht, ENNReal.ofReal_one]

private theorem series_solution {k : ℕ} {c : ℚ} (h : C.admissible k c = true)
    {b x : Fin n → ℚ} (hx : (1 - C.Q) *ᵥ x = b) :
    (∑' r : ℕ, Qr ^ r) *ᵥ (fun i => (b i : ℝ)) = fun i => (x i : ℝ) := by
  have hr : (1 - Qr) *ᵥ (fun i => (x i : ℝ)) = fun i => (b i : ℝ) := by
    have heq : (1 - C.Q).map (Rat.castHom ℝ) = 1 - Qr := by
      simpa using (Rat.castHom ℝ).mapMatrix.map_sub 1 C.Q
    rw [← heq]
    funext i
    change ((1 - C.Q).map (Rat.castHom ℝ) *ᵥ ((Rat.castHom ℝ) ∘ x)) i = _
    rw [← RingHom.map_mulVec, hx]
    rfl
  rw [← hr, Matrix.mulVec_mulVec, (C.summable_powers h).tsum_pow_mul_one_sub,
    Matrix.one_mulVec]

private theorem summable_reward_norm {k : ℕ} {c : ℚ} (h : C.admissible k c = true)
    (i : Fin n) (f : Fin m → ℝ) :
    Summable (fun p : ℕ × Fin m => (C.hit p.1 i p.2 : ℝ) * ‖f p.2‖) := by
  apply summable_joint_nonneg (f := fun r a => (C.hit r i a : ℝ) * ‖f a‖)
    (fun r a => mul_nonneg (C.real_hit_nonneg r i a) (norm_nonneg (f a)))
  intro a
  exact (Pi.hasSum.mp (Pi.hasSum.mp (C.hasSum_hits h) i) a).summable.mul_right _

/-- Any terminal-state reward is integrable under the constructed first-hit law. -/
theorem integrable_reward {k : ℕ} {c : ℚ} (h : C.admissible k c = true)
    (i : Fin n) (f : Fin m → ℝ) :
    Integrable (fun p : ℕ × Fin m => f p.2) (Measure.sum fun p : ℕ × Fin m =>
      ENNReal.ofReal (C.hit p.1 i p.2 : ℝ) • Measure.dirac p) := by
  apply integrable_sum_dirac (fun _ => ENNReal.ofReal_ne_top)
  simpa only [ENNReal.toReal_ofReal (C.real_hit_nonneg _ _ _)] using C.summable_reward_norm h i f

private theorem integral_reward_series {k : ℕ} {c : ℚ} (h : C.admissible k c = true)
    (i : Fin n) (f : Fin m → ℝ) :
    (∫ p : ℕ × Fin m, f p.2 ∂(Measure.sum fun p : ℕ × Fin m =>
      ENNReal.ofReal (C.hit p.1 i p.2 : ℝ) • Measure.dirac p)) =
      (((∑' r : ℕ, Qr ^ r) * Rr) *ᵥ f) i := by
  have hn := C.summable_reward_norm h i f
  have hs : Summable (fun p : ℕ × Fin m => (C.hit p.1 i p.2 : ℝ) * f p.2) := by
    apply Summable.of_norm
    simpa only [norm_mul, Real.norm_of_nonneg (C.real_hit_nonneg _ _ _)] using hn
  rw [integral_sum_dirac_eq_tsum (fun _ => ENNReal.ofReal_ne_top) (by
    simpa only [ENNReal.toReal_ofReal (C.real_hit_nonneg _ _ _)] using hn)]
  simp only [ENNReal.toReal_ofReal (C.real_hit_nonneg _ _ _), smul_eq_mul]
  rw [hs.tsum_prod]
  simp only [tsum_fintype]
  exact (Pi.hasSum.mp (hasSum_mulVec (C.hasSum_hits h) f) i).tsum_eq

private theorem hasSum_weighted_hits {k : ℕ} {c : ℚ} (h : C.admissible k c = true) :
    HasSum (fun r : ℕ => (r + 1) • (C.hit r).map (Rat.castHom ℝ))
      ((∑' r : ℕ, (r + 1) • Qr ^ r) * Rr) := by
  simpa only [C.cast_hit, Matrix.smul_mul] using
    hasSum_mul (C.summable_weighted_powers h).hasSum Rr

private theorem summable_time {k : ℕ} {c : ℚ} (h : C.admissible k c = true) (i : Fin n) :
    Summable (fun p : ℕ × Fin m => (C.hit p.1 i p.2 : ℝ) * (p.1 + 1 : ℕ)) := by
  apply summable_joint_nonneg (f := fun r a => (C.hit r i a : ℝ) * (r + 1 : ℕ))
    (fun r a => mul_nonneg (C.real_hit_nonneg r i a) (Nat.cast_nonneg (r + 1)))
  intro a
  simpa only [Matrix.smul_apply, Pi.smul_apply, nsmul_eq_mul, Matrix.map_apply, mul_comm, one_mul] using
    (Pi.hasSum.mp (Pi.hasSum.mp (C.hasSum_weighted_hits h) i) a).summable

/-- The actual hitting time, rather than just its formal Bellman residual, is integrable. -/
theorem integrable_time {k : ℕ} {c : ℚ} (h : C.admissible k c = true) (i : Fin n) :
    Integrable (fun p : ℕ × Fin m => ((p.1 + 1 : ℕ) : ℝ)) (Measure.sum fun p : ℕ × Fin m =>
      ENNReal.ofReal (C.hit p.1 i p.2 : ℝ) • Measure.dirac p) := by
  apply integrable_sum_dirac (fun _ => ENNReal.ofReal_ne_top)
  simpa only [ENNReal.toReal_ofReal (C.real_hit_nonneg _ _ _),
    Real.norm_of_nonneg (Nat.cast_nonneg _)] using C.summable_time h i

private theorem integral_time_series {k : ℕ} {c : ℚ} (h : C.admissible k c = true) (i : Fin n) :
    (∫ p : ℕ × Fin m, ((p.1 + 1 : ℕ) : ℝ) ∂(Measure.sum fun p : ℕ × Fin m =>
      ENNReal.ofReal (C.hit p.1 i p.2 : ℝ) • Measure.dirac p)) =
      ((∑' r : ℕ, Qr ^ r) *ᵥ (fun _ => 1)) i := by
  have hn := C.summable_time h i
  rw [integral_sum_dirac_eq_tsum (fun _ => ENNReal.ofReal_ne_top) (by
    simpa only [ENNReal.toReal_ofReal (C.real_hit_nonneg _ _ _),
      Real.norm_of_nonneg (Nat.cast_nonneg _)] using hn)]
  simp only [ENNReal.toReal_ofReal (C.real_hit_nonneg _ _ _), smul_eq_mul]
  rw [hn.tsum_prod]
  simp only [tsum_fintype]
  have hs := hasSum_mulVec (C.hasSum_weighted_hits h) (fun _ => 1)
  have heq : ((∑' r : ℕ, (r + 1) • Qr ^ r) * Rr) *ᵥ (fun _ => (1 : ℝ)) =
      (∑' r : ℕ, Qr ^ r) *ᵥ (fun _ => 1) := by
    rw [← Matrix.mulVec_mulVec, ← C.real_row_sum, Matrix.mulVec_mulVec,
      weighted_series_identity (C.summable_powers h) (C.summable_weighted_powers h)]
  rw [heq] at hs
  simpa only [Matrix.mulVec, dotProduct, mul_one, Matrix.smul_apply, Pi.smul_apply, nsmul_eq_mul,
    Matrix.map_apply, mul_comm, one_mul] using (Pi.hasSum.mp hs i).tsum_eq

/-- Every singleton of the analytic law has the coefficient identified by
`run_firstHit`; the law preserves the first-hit time and terminal state jointly. -/
theorem firstHit_singleton (i : Fin n) (r : ℕ) (a : Fin m) :
    (Measure.sum fun p : ℕ × Fin m =>
      ENNReal.ofReal (C.hit p.1 i p.2 : ℝ) • Measure.dirac p) {(r, a)} =
        ENNReal.ofReal (C.hit r i a : ℝ) := Measure.sum_smul_dirac_singleton

/-- The actual executable solver succeeds under its checked absorption bound.
Its two rational vectors are the unique Bellman solutions, and their casts
are the integrals of reward and hitting time under the constructed probability
law. Both integrability proofs are conclusions. Terminal values are extended
by the original reward and zero time in the returned pair. -/
theorem solve_correct {k : ℕ} {c : ℚ} (h : C.admissible k c = true) :
    ∃ v t : Fin n → ℚ,
      C.solve k c = .ok (Sum.elim v C.reward, Sum.elim t (fun _ => 0)) ∧
      (1 - C.Q) *ᵥ v = C.R *ᵥ C.reward ∧ (1 - C.Q) *ᵥ t = (fun _ => 1) ∧
      (∀ x, (1 - C.Q) *ᵥ x = C.R *ᵥ C.reward → x = v) ∧
      (∀ x, (1 - C.Q) *ᵥ x = (fun _ => 1) → x = t) ∧
      ∀ i : Fin n,
        let μ := Measure.sum fun p : ℕ × Fin m =>
          ENNReal.ofReal (C.hit p.1 i p.2 : ℝ) • Measure.dirac p
        IsProbabilityMeasure μ ∧
        Integrable (fun p : ℕ × Fin m => (C.reward p.2 : ℝ)) μ ∧
        Integrable (fun p : ℕ × Fin m => ((p.1 + 1 : ℕ) : ℝ)) μ ∧
        (∫ p : ℕ × Fin m, (C.reward p.2 : ℝ) ∂μ) = (v i : ℝ) ∧
        (∫ p : ℕ × Fin m, ((p.1 + 1 : ℕ) : ℝ) ∂μ) = (t i : ℝ) := by
  have hd := C.det_ne_zero h
  obtain ⟨v, hv, ev⟩ := solveLinear_spec (1 - C.Q) (C.R *ᵥ C.reward) hd
  obtain ⟨t, ht, et⟩ := solveLinear_spec (1 - C.Q) (fun _ => 1) hd
  refine ⟨v, t, by simp [solve, h, hv, ht], ev, et,
    (fun x hx => solveLinear_unique _ hd (hx.trans ev.symm)),
    (fun x hx => solveLinear_unique _ hd (hx.trans et.symm)), ?_⟩
  intro i
  dsimp only
  refine ⟨C.firstHit_probability h i,
    C.integrable_reward h i (fun a => (C.reward a : ℝ)), C.integrable_time h i, ?_, ?_⟩
  · rw [C.integral_reward_series h i (fun a => (C.reward a : ℝ)), ← Matrix.mulVec_mulVec]
    have heq : Rr *ᵥ (fun a => (C.reward a : ℝ)) =
        fun j => ((C.R *ᵥ C.reward) j : ℝ) := by
      funext j
      exact ((Rat.castHom ℝ).map_mulVec C.R C.reward j).symm
    rw [heq, C.series_solution h ev]
  · rw [C.integral_time_series h i]
    simpa only [Rat.cast_one] using congrFun (C.series_solution h et) i

/-- Every supplied transient start has unfinished probability tending to zero.
This property uses the original finite execution probabilities, independently
of the automatic checker and of any proposed certificate. -/
def AbsorbsAll : Prop :=
  ∀ i : Fin n, Filter.Tendsto (fun horizon => (C.survival horizon i : ℝ))
    Filter.atTop (nhds 0)

/-- The exact finite automatic test is sound and complete for almost-sure
absorption of the full supplied transient domain. Finite completeness is
provided by `finite_horizon_complete`, not an assumption on the input chain. -/
theorem autoCheck_iff_absorbsAll : C.autoCheck = true ↔ C.AbsorbsAll := by
  constructor
  · intro h i
    have hs := (Pi.hasSum.mp
      (hasSum_mulVec (C.summable_powers h).hasSum (fun _ => 1)) i).summable
    have heq (r : ℕ) : (Qr ^ r *ᵥ (fun _ => 1)) i = (C.survival r i : ℝ) := by
      rw [← Matrix.map_pow]
      simp [survival, Matrix.mulVec, dotProduct, Matrix.map_apply]
    simpa only [heq] using hs.tendsto_atTop_zero
  · intro h
    apply C.autoCheck_iff_reaches.mpr
    intro i
    obtain ⟨horizon, hh⟩ := ((h i).eventually_lt_const (by norm_num : (0 : ℝ) < 1)).exists
    exact ⟨horizon, by exact_mod_cast hh⟩

/-- Rejection has a particular nonabsorbing witness, even if other states
terminate. Its original survival probability is one at every horizon. -/
theorem autoCheck_failure_semantics (h : C.autoCheck = false) :
    ∃ i : Fin n, (∀ horizon, C.survival horizon i = 1) ∧
      ¬ Filter.Tendsto (fun horizon => (C.survival horizon i : ℝ))
        Filter.atTop (nhds 0) := by
  obtain ⟨i, hi⟩ := C.autoCheck_failure h
  refine ⟨i, hi, ?_⟩
  intro ht
  obtain ⟨horizon, hh⟩ := (ht.eventually_lt_const (by norm_num : (0 : ℝ) < 1)).exists
  simp [hi horizon] at hh

/-- Full-domain absorption normalizes the original joint first-hit law.
Its singleton coefficients are those proved by `run_firstHit` and
`firstHit_singleton`; the time coordinate `r` denotes duration `r+1`. -/
theorem AbsorbsAll.firstHit_probability (h : C.AbsorbsAll) (i : Fin n) :
    IsProbabilityMeasure (Measure.sum fun p : ℕ × Fin m =>
      ENNReal.ofReal (C.hit p.1 i p.2 : ℝ) • Measure.dirac p) :=
  C.firstHit_probability (C.autoCheck_iff_absorbsAll.mpr h) i

/-- The automatic certificate makes the rational Bellman matrix nonsingular. -/
theorem autoCheck_det_ne_zero (h : C.autoCheck = true) : (1 - C.Q).det ≠ 0 :=
  C.det_ne_zero h

/-- The computed certificate guarantees actual success of `autoSolve`. Both
returned vectors are unique Bellman solutions and equal the reward and actual
duration integrals. Normalization and both integrability claims are conclusions;
callers provide no block bound, inverse, candidate solution or moment hypothesis. -/
theorem autoSolve_correct (h : C.autoCheck = true) :
    ∃ v t : Fin n → ℚ,
      C.autoSolve = .ok (Sum.elim v C.reward, Sum.elim t (fun _ => 0)) ∧
      (1 - C.Q) *ᵥ v = C.R *ᵥ C.reward ∧ (1 - C.Q) *ᵥ t = (fun _ => 1) ∧
      (∀ x, (1 - C.Q) *ᵥ x = C.R *ᵥ C.reward → x = v) ∧
      (∀ x, (1 - C.Q) *ᵥ x = (fun _ => 1) → x = t) ∧
      ∀ i : Fin n,
        let μ := Measure.sum fun p : ℕ × Fin m =>
          ENNReal.ofReal (C.hit p.1 i p.2 : ℝ) • Measure.dirac p
        IsProbabilityMeasure μ ∧
        Integrable (fun p : ℕ × Fin m => (C.reward p.2 : ℝ)) μ ∧
        Integrable (fun p : ℕ × Fin m => ((p.1 + 1 : ℕ) : ℝ)) μ ∧
        (∫ p : ℕ × Fin m, (C.reward p.2 : ℝ) ∂μ) = (v i : ℝ) ∧
        (∫ p : ℕ × Fin m, ((p.1 + 1 : ℕ) : ℝ) ∂μ) = (t i : ℝ) :=
  C.solve_correct h

/-- Success of the actual automatic solver is equivalent to full-domain
absorption; a successful check cannot fall through to the singular branch. -/
theorem autoSolve_success_iff : (∃ vt, C.autoSolve = .ok vt) ↔ C.AbsorbsAll := by
  constructor
  · rintro ⟨vt, hvt⟩
    apply C.autoCheck_iff_absorbsAll.mp
    by_contra h
    have hf : C.autoCheck = false := Bool.eq_false_iff.mpr h
    rw [C.autoSolve_of_rejected hf] at hvt
    cases hvt
  · intro h
    obtain ⟨v, t, hs, _⟩ := C.autoSolve_correct (C.autoCheck_iff_absorbsAll.mpr h)
    exact ⟨_, hs⟩

/-- The only possible automatic solver error is rejection of full-domain
absorption; the retained low-level singular error is unreachable here. -/
theorem autoSolve_ne_singular : C.autoSolve ≠ .error .singular := by
  cases h : C.autoCheck with
  | false => simp [C.autoSolve_of_rejected h]
  | true =>
    obtain ⟨v, t, hs, _⟩ := C.autoSolve_correct h
    simp [hs]

/-- A pair observed in the automatic output is the pair of original first-hit
integrals. This is a reusable consumer of the full automatic correctness theorem. -/
theorem autoSolve_integrals (h : C.autoCheck = true) (i : Fin n) (value duration : ℚ)
    (result : C.autoSolve.map (fun vt => (vt.1 (.inl i), vt.2 (.inl i))) =
      .ok (value, duration)) :
    let μ := Measure.sum fun p : ℕ × Fin m =>
      ENNReal.ofReal (C.hit p.1 i p.2 : ℝ) • Measure.dirac p
    (∫ p : ℕ × Fin m, (C.reward p.2 : ℝ) ∂μ) = (value : ℝ) ∧
      (∫ p : ℕ × Fin m, ((p.1 + 1 : ℕ) : ℝ) ∂μ) = (duration : ℝ) := by
  obtain ⟨v, t, hs, _, _, _, _, hsemantic⟩ := C.autoSolve_correct h
  have hv : v i = value ∧ t i = duration := by
    rw [hs] at result
    simpa only [Except.map, Sum.elim_inl, Except.ok.injEq, Prod.mk.injEq] using result
  obtain ⟨_, _, _, he, ht⟩ := hsemantic i
  exact ⟨he.trans (congrArg (fun q : ℚ => (q : ℝ)) hv.1),
    ht.trans (congrArg (fun q : ℚ => (q : ℝ)) hv.2)⟩


end FiniteMarkovChain.Chain
