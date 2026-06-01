/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.MechanismDesign.Auction.Transfer
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# EconCSLib.MechanismDesign.Auction.Myerson

Myerson-specific theory for single-parameter mechanisms over `ℝ`.

This file extends the single-parameter transfer mechanism layer with:

- the canonical payment rule `myersonPayment`
- the induced mechanism `withMyersonPayment`
- zero normalization
- the monotonicity, implementability, and uniqueness statements usually grouped
  under Myerson's Lemma

It is the mechanism-design layer that depends on interval integration.

## Structure hierarchy

```
MechanismWithTransfers I (fun _ => ℝ) (I → ℝ) ℝ   -- scalar reports, scalar allocations
  └─ SingleParameterMechanism I ℝ                 -- single-parameter layer
       └─ withMyersonPayment x                    -- allocation rule + Myerson payment

SingleParameterMechanism.IsMonotone               -- implementability condition
  └─ SingleParameterMechanism.IsDSIC              -- via Myerson payment formula
```
-/

namespace SingleParameterMechanism

section MyersonLemma

variable {I : Type*}

/-- The canonical Myerson payment formula associated with an allocation rule
`x`. Holding all other bids fixed, agent `i` pays

`bᵢ xᵢ(b) - ∫₀^{bᵢ} xᵢ(z, b₋ᵢ) dz`. -/
noncomputable def myersonPayment
    [DecidableEq I]
    (x : (I → ℝ) → I → ℝ) (b : I → ℝ) (i : I) : ℝ :=
  b i * x b i - ∫ z in 0..b i, x (Function.update b i z) i

/-- The single-parameter mechanism obtained by equipping an allocation rule
with its canonical Myerson payment rule. -/
noncomputable def withMyersonPayment
    [DecidableEq I]
    (x : (I → ℝ) → I → ℝ) : SingleParameterMechanism I ℝ where
  allocationRule := x
  paymentRule := myersonPayment x

/-- Utility under the canonical Myerson payment rule can be written in the
standard envelope-friendly form. -/
lemma withMyersonPayment_quasiLinearUtility_eq [DecidableEq I]
    (x : (I → ℝ) → I → ℝ) (v b : I → ℝ) (i : I) :
    (withMyersonPayment x).quasiLinearUtility b v i =
      (v i - b i) * x b i + ∫ z in 0..b i, x (Function.update b i z) i := by
  simp [SingleParameterMechanism.quasiLinearUtility, SingleParameterMechanism.quasiLinearValue,
    SingleParameterMechanism.payment, withMyersonPayment, myersonPayment]
  ring

/-- Zero normalization for payment rules:
reporting `0` yields payment `0`, holding the other reports fixed. -/
def ZeroNormalized [DecidableEq I] (p : (I → ℝ) → I → ℝ) : Prop :=
  ∀ (i : I) (b : I → ℝ), p (Function.update b i 0) i = 0

/-- The canonical Myerson payment rule is zero-normalized. -/
theorem myersonPayment_zeroNormalized [DecidableEq I] (x : (I → ℝ) → I → ℝ) :
    ZeroNormalized (myersonPayment x) := by
  intro i b
  simp [myersonPayment]

/-- Myerson Lemma, Property 1:
every DSIC single-parameter mechanism has a monotone allocation rule. -/
theorem isMonotone_of_isDSIC [DecidableEq I] {M : SingleParameterMechanism I ℝ}
    (hdsic : M.IsDSIC) :
    M.IsMonotone := by
  intro i θ θ' hθ b
  by_cases hEq : θ = θ'
  · simp [hEq]
  have hlt : θ < θ' := lt_of_le_of_ne hθ hEq
  let v : I → ℝ := Function.update b i θ
  let v' : I → ℝ := Function.update b i θ'
  have h1 : θ * M.allocationRule (Function.update b i θ') i -
      M.payment (Function.update b i θ') i ≤
      θ * M.allocationRule (Function.update b i θ) i -
      M.payment (Function.update b i θ) i := by
    have := hdsic v i θ' b
    simpa [SingleParameterMechanism.IsDSIC, MechanismWithTransfers.isDSIC,
      MechanismWithTransfers.toStrategicGame, IsWeaklyDominant, WeaklyDominates,
      SingleParameterMechanism.payment, v]
      using this
  have h2 : θ' * M.allocationRule (Function.update b i θ) i -
      M.payment (Function.update b i θ) i ≤
      θ' * M.allocationRule (Function.update b i θ') i -
      M.payment (Function.update b i θ') i := by
    have := hdsic v' i θ b
    simpa [SingleParameterMechanism.IsDSIC, MechanismWithTransfers.isDSIC,
      MechanismWithTransfers.toStrategicGame, IsWeaklyDominant, WeaklyDominates,
      SingleParameterMechanism.payment, v']
      using this
  nlinarith

/-- For a DSIC single-parameter mechanism, fixing all other bids yields the
standard two-sided bound on payment differences. -/
theorem payment_sandwich [DecidableEq I]
    {x p : (I → ℝ) → I → ℝ}
    (hdsic : ({ allocationRule := x, paymentRule := p } :
      SingleParameterMechanism I ℝ).IsDSIC)
    (b : I → ℝ) (i : I) (y z : ℝ) :
    z * (x (Function.update b i y) i - x (Function.update b i z) i) ≤
      p (Function.update b i y) i - p (Function.update b i z) i ∧
    p (Function.update b i y) i - p (Function.update b i z) i ≤
      y * (x (Function.update b i y) i - x (Function.update b i z) i) := by
  let vy : I → ℝ := Function.update b i y
  have h1 : y * x (Function.update b i z) i - p (Function.update b i z) i ≤
      y * x (Function.update b i y) i - p (Function.update b i y) i := by
    have := hdsic vy i z b
    simpa [SingleParameterMechanism.IsDSIC, MechanismWithTransfers.isDSIC,
      MechanismWithTransfers.toStrategicGame, IsWeaklyDominant, WeaklyDominates,
      SingleParameterMechanism.payment, vy]
      using this
  let vz : I → ℝ := Function.update b i z
  have h2 : z * x (Function.update b i y) i - p (Function.update b i y) i ≤
      z * x (Function.update b i z) i - p (Function.update b i z) i := by
    have := hdsic vz i y b
    simpa [SingleParameterMechanism.IsDSIC, MechanismWithTransfers.isDSIC,
      MechanismWithTransfers.toStrategicGame, IsWeaklyDominant, WeaklyDominates,
      SingleParameterMechanism.payment, vz]
      using this
  constructor <;> linarith

/-- If two payment rules implement the same allocation rule in DSIC form, then
their difference along a one-dimensional deviation is controlled by the change
in the allocation rule. This is the comparison estimate used in the proof of
the Myerson payment identity. -/
theorem payment_difference_bound [DecidableEq I]
    {x p q : (I → ℝ) → I → ℝ}
    (hpdsic : ({ allocationRule := x, paymentRule := p } :
      SingleParameterMechanism I ℝ).IsDSIC)
    (hqdsic : ({ allocationRule := x, paymentRule := q } :
      SingleParameterMechanism I ℝ).IsDSIC)
    (b : I → ℝ) (i : I) (y z : ℝ) :
    |(p (Function.update b i y) i - q (Function.update b i y) i) -
        (p (Function.update b i z) i - q (Function.update b i z) i)| ≤
      (y - z) * (x (Function.update b i y) i - x (Function.update b i z) i) := by
  obtain ⟨hp₁, hp₂⟩ := payment_sandwich hpdsic b i y z
  obtain ⟨hq₁, hq₂⟩ := payment_sandwich hqdsic b i y z
  rw [abs_le]
  constructor <;> linarith

/-- Myerson Lemma, Property 2:
a monotone allocation rule is DSIC when paired with the canonical Myerson
payment rule. -/
theorem withMyersonPayment_isDSIC_of_isMonotone [DecidableEq I]
    {x : (I → ℝ) → I → ℝ}
    (hx : IsMonotone ({ allocationRule := x, paymentRule := myersonPayment x } :
      SingleParameterMechanism I ℝ)) :
    (withMyersonPayment x).IsDSIC := by
  intro v i (s' : ℝ) (reports : I → ℝ)
  let g : ℝ → ℝ := fun z => x (Function.update reports i z) i
  have hgmono : Monotone g := by
    intro z₁ z₂ hz
    exact hx i z₁ z₂ hz reports
  have hform : ∀ r : ℝ,
      (withMyersonPayment x).quasiLinearUtility (Function.update reports i r) v i =
        (v i - r) * g r + ∫ z in 0..r, g z := by
    intro r
    rw [withMyersonPayment_quasiLinearUtility_eq]
    simp [g, Function.update_idem]
  change
    (withMyersonPayment x).quasiLinearUtility (Function.update reports i s') v i ≤
      (withMyersonPayment x).quasiLinearUtility (Function.update reports i (v i)) v i
  by_cases hs : s' ≤ v i
  · have hg0s : IntervalIntegrable g MeasureTheory.volume 0 s' := hgmono.intervalIntegrable
    have hgsv : IntervalIntegrable g MeasureTheory.volume s' (v i) := hgmono.intervalIntegrable
    have hmonoInt :
        (v i - s') * g s' ≤ ∫ z in s'..v i, g z := by
      simpa using
        intervalIntegral.integral_mono_on hs intervalIntegrable_const hgsv
          (fun z hz => hgmono hz.1)
    calc
      (withMyersonPayment x).quasiLinearUtility (Function.update reports i s') v i
          = (v i - s') * g s' + ∫ z in 0..s', g z := hform s'
      _ ≤ (∫ z in s'..v i, g z) + ∫ z in 0..s', g z := by
        exact add_le_add hmonoInt le_rfl
      _ = ∫ z in 0..v i, g z := by
        simpa [add_comm] using intervalIntegral.integral_add_adjacent_intervals hg0s hgsv
      _ = (withMyersonPayment x).quasiLinearUtility (Function.update reports i (v i)) v i := by
        rw [hform (v i)]
        ring
  · have hvs : v i ≤ s' := le_of_not_ge hs
    have hg0v : IntervalIntegrable g MeasureTheory.volume 0 (v i) := hgmono.intervalIntegrable
    have hgvs : IntervalIntegrable g MeasureTheory.volume (v i) s' := hgmono.intervalIntegrable
    have hbracket : (v i - s') * g s' + ∫ z in v i..s', g z ≤ 0 := by
      have hmonoInt : ∫ z in v i..s', g z ≤ (s' - v i) * g s' := by
        simpa using
          intervalIntegral.integral_mono_on hvs hgvs intervalIntegrable_const
            (fun z hz => hgmono hz.2)
      nlinarith
    calc
      (withMyersonPayment x).quasiLinearUtility (Function.update reports i s') v i
          = (v i - s') * g s' + ∫ z in 0..s', g z := hform s'
      _ = (v i - s') * g s' + ((∫ z in 0..v i, g z) + ∫ z in v i..s', g z) := by
        rw [← intervalIntegral.integral_add_adjacent_intervals hg0v hgvs]
      _ = (∫ z in 0..v i, g z) + ((v i - s') * g s' + ∫ z in v i..s', g z) := by
        ring
      _ ≤ ∫ z in 0..v i, g z + 0 := by
        simpa [add_comm, add_left_comm, add_assoc] using
          add_le_add_left hbracket (∫ z in 0..v i, g z)
      _ = ∫ z in 0..v i, g z := by simp
      _ = (withMyersonPayment x).quasiLinearUtility (Function.update reports i (v i)) v i := by
        rw [hform (v i)]
        ring

/-- Myerson Lemma, Property 2, reformulated:
an allocation rule is implementable if it is monotone. -/
theorem isImplementable_of_isMonotone [DecidableEq I]
    {x : (I → ℝ) → I → ℝ}
    (hx : IsMonotone ({ allocationRule := x, paymentRule := myersonPayment x } :
      SingleParameterMechanism I ℝ)) :
    IsImplementable x := by
  refine ⟨myersonPayment x, ?_⟩
  simpa [withMyersonPayment] using withMyersonPayment_isDSIC_of_isMonotone hx

/-- Myerson Lemma `(a)`:
an allocation rule is implementable if and only if it is monotone. -/
theorem isImplementable_iff_isMonotone [DecidableEq I]
    (x : (I → ℝ) → I → ℝ) :
    IsImplementable x ↔
      IsMonotone ({ allocationRule := x, paymentRule := myersonPayment x } :
        SingleParameterMechanism I ℝ) := by
  constructor
  · intro hx
    rcases hx with ⟨p, hp⟩
    simpa [SingleParameterMechanism.IsMonotone] using
      (isMonotone_of_isDSIC (M := ({ allocationRule := x, paymentRule := p } :
        SingleParameterMechanism I ℝ)) hp)
  · intro hx
    exact isImplementable_of_isMonotone hx

/-- Explicit payment identity used in Myerson's Lemma:
for a DSIC single-parameter mechanism with zero-normalized payments, the payment
rule is given pointwise by the Myerson payment identity. -/
theorem payment_formula_of_isDSIC_of_zeroNormalized [DecidableEq I]
    {x p : (I → ℝ) → I → ℝ}
    (hdsic : ({ allocationRule := x, paymentRule := p } :
      SingleParameterMechanism I ℝ).IsDSIC)
    (h0 : ZeroNormalized p)
    (b : I → ℝ) (i : I) :
    p b i = b i * x b i - ∫ z in 0..b i, x (Function.update b i z) i := by
  have hx :
      IsMonotone ({ allocationRule := x, paymentRule := p } :
        SingleParameterMechanism I ℝ) :=
    isMonotone_of_isDSIC hdsic
  have hmyersonDSIC :
      ({ allocationRule := x, paymentRule := myersonPayment x } :
        SingleParameterMechanism I ℝ).IsDSIC := by
    exact withMyersonPayment_isDSIC_of_isMonotone (x := x) hx
  have hcompare :
      ∀ y z : ℝ, z ≤ y →
        |(p (Function.update b i y) i - myersonPayment x (Function.update b i y) i) -
            (p (Function.update b i z) i - myersonPayment x (Function.update b i z) i)| ≤
          (y - z) * (x (Function.update b i y) i - x (Function.update b i z) i) := by
    intro y z hyz
    simpa using
      payment_difference_bound (x := x) (p := p) (q := myersonPayment x)
        hdsic hmyersonDSIC b i y z
  have hzero_compare :
      p (Function.update b i 0) i - myersonPayment x (Function.update b i 0) i = 0 := by
    rw [h0]
    exact myersonPayment_zeroNormalized x i b |> Eq.symm |> sub_eq_zero.mpr
  let g : ℝ → ℝ := fun t => x (Function.update b i t) i
  let d : ℝ → ℝ := fun t =>
    p (Function.update b i t) i - myersonPayment x (Function.update b i t) i
  have hgmono : Monotone g := by
    intro s t hst
    exact hx i s t hst b
  have hcompare' :
      ∀ y z : ℝ, z ≤ y → |d y - d z| ≤ (y - z) * (g y - g z) := by
    intro y z hyz
    simpa [d, g] using hcompare y z hyz
  have hd0 : d 0 = 0 := by
    simpa [d] using hzero_compare
  have hpartition :
      ∀ a c : ℝ, a ≤ c → ∀ N : ℕ, 0 < N →
        |d c - d a| ≤ ((c - a) * (g c - g a)) / N := by
    intro a c hac N hN
    let h : ℝ := (c - a) / N
    let t : ℕ → ℝ := fun k => a + k * h
    have hN0 : (N : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hN)
    have hh_nonneg : 0 ≤ h := by
      dsimp [h]
      exact div_nonneg (sub_nonneg.mpr hac) (by positivity)
    have ht0 : t 0 = a := by
      simp [t]
    have htN : t N = c := by
      dsimp [t, h]
      field_simp [hN0]
      ring
    have htstep : ∀ k : ℕ, t (k + 1) - t k = h := by
      intro k
      simp [t, Nat.cast_add, Nat.cast_one]
      ring
    have hstep_bound :
        ∀ k ∈ Finset.range N,
          |d (t (k + 1)) - d (t k)| ≤ h * (g (t (k + 1)) - g (t k)) := by
      intro k hk
      have hkcast : (k : ℝ) ≤ (k + 1 : ℕ) := by
        exact_mod_cast (Nat.le_succ k)
      have hkord : t k ≤ t (k + 1) := by
        dsimp [t]
        simpa [add_comm, add_left_comm, add_assoc] using
          add_le_add_left (mul_le_mul_of_nonneg_right hkcast hh_nonneg) a
      simpa [htstep k] using hcompare' (t (k + 1)) (t k) hkord
    calc
      |d c - d a| = |d (t N) - d (t 0)| := by rw [htN, ht0]
      _ = |Finset.sum (Finset.range N) (fun k => d (t (k + 1)) - d (t k))| := by
        rw [← Finset.sum_range_sub fun k => d (t k)]
      _ ≤ Finset.sum (Finset.range N) (fun k => |d (t (k + 1)) - d (t k)|) := by
        simpa using Finset.abs_sum_le_sum_abs
          (fun k => d (t (k + 1)) - d (t k)) (Finset.range N)
      _ ≤ Finset.sum (Finset.range N) (fun k => h * (g (t (k + 1)) - g (t k))) := by
        exact Finset.sum_le_sum hstep_bound
      _ = h * Finset.sum (Finset.range N) (fun k => g (t (k + 1)) - g (t k)) := by
        rw [← Finset.mul_sum]
      _ = h * (g (t N) - g (t 0)) := by
        rw [Finset.sum_range_sub fun k => g (t k)]
      _ = ((c - a) / N) * (g c - g a) := by simp [h, htN, ht0]
      _ = ((c - a) * (g c - g a)) / N := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        ring
  have hzero_of_abs_le_div_nat :
      ∀ {u A : ℝ}, 0 ≤ A → (∀ N : ℕ, 0 < N → |u| ≤ A / N) → u = 0 := by
    intro u A _ hbound
    have hlim0 : Filter.Tendsto (fun N : ℕ => A / N) Filter.atTop (nhds 0) := by
      simpa [div_eq_mul_inv, one_div] using
        (tendsto_const_nhds.mul tendsto_one_div_atTop_nhds_zero_nat :
          Filter.Tendsto (fun N : ℕ => A * (1 / (N : ℝ))) Filter.atTop (nhds (A * 0)))
    have hlim :
        Filter.Tendsto (fun N : ℕ => A / ((N + 1 : ℕ) : ℝ)) Filter.atTop (nhds 0) := by
      simpa [Function.comp_def] using hlim0.comp (Filter.tendsto_add_atTop_nat 1)
    have hzero : Filter.Tendsto (fun _ : ℕ => |u|) Filter.atTop (nhds 0) :=
      squeeze_zero (fun _ => abs_nonneg u) (fun N => hbound (N + 1) (Nat.succ_pos N)) hlim
    exact abs_eq_zero.mp (tendsto_nhds_unique tendsto_const_nhds hzero)
  have hdb0 : d (b i) - d 0 = 0 := by
    by_cases hbi : 0 ≤ b i
    · let A : ℝ := (b i - 0) * (g (b i) - g 0)
      have hA_nonneg : 0 ≤ A := by
        dsimp [A]
        exact mul_nonneg (sub_nonneg.mpr hbi) (sub_nonneg.mpr (hgmono hbi))
      have hA_bound : ∀ N : ℕ, 0 < N → |d (b i) - d 0| ≤ A / N := by
        intro N hN
        simpa [A, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
          hpartition 0 (b i) hbi N hN
      exact hzero_of_abs_le_div_nat hA_nonneg hA_bound
    · have hbi' : b i ≤ 0 := le_of_not_ge hbi
      let A : ℝ := (0 - b i) * (g 0 - g (b i))
      have hA_nonneg : 0 ≤ A := by
        dsimp [A]
        exact mul_nonneg (sub_nonneg.mpr hbi') (sub_nonneg.mpr (hgmono hbi'))
      have hA_bound : ∀ N : ℕ, 0 < N → |d (b i) - d 0| ≤ A / N := by
        intro N hN
        simpa [A, abs_sub_comm, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
          hpartition (b i) 0 hbi' N hN
      exact hzero_of_abs_le_div_nat hA_nonneg hA_bound
  have hdb : d (b i) = 0 := by
    rw [hd0, sub_zero] at hdb0
    exact hdb0
  have hp_eq : p b i - myersonPayment x b i = 0 := by
    simpa [d, Function.update_eq_self] using hdb
  simpa [myersonPayment] using sub_eq_zero.mp hp_eq

/-- Uniqueness of zero-normalized DSIC payment rules:
among zero-normalized payment rules, the canonical Myerson payment rule is the
unique one that implements a monotone allocation rule. -/
theorem payment_eq_myersonPayment_of_isDSIC_of_zeroNormalized [DecidableEq I]
    {x p : (I → ℝ) → I → ℝ}
    (hdsic : ({ allocationRule := x, paymentRule := p } :
      SingleParameterMechanism I ℝ).IsDSIC)
    (h0 : ZeroNormalized p) :
    p = myersonPayment x := by
  funext b i
  simpa [myersonPayment] using payment_formula_of_isDSIC_of_zeroNormalized hdsic h0 b i

/-- Myerson Lemma `(b)`:
if `x` is monotone, then there is a unique zero-normalized payment rule making
`(x, p)` DSIC. -/
theorem existsUnique_zeroNormalized_payment_of_isMonotone [DecidableEq I]
    {x : (I → ℝ) → I → ℝ}
    (hx : IsMonotone ({ allocationRule := x, paymentRule := myersonPayment x } :
      SingleParameterMechanism I ℝ)) :
    ∃! p : (I → ℝ) → I → ℝ,
      ZeroNormalized p ∧
        ({ allocationRule := x, paymentRule := p } : SingleParameterMechanism I ℝ).IsDSIC := by
  refine ⟨myersonPayment x, ?_, ?_⟩
  · exact ⟨myersonPayment_zeroNormalized x, withMyersonPayment_isDSIC_of_isMonotone hx⟩
  · intro p hp
    exact payment_eq_myersonPayment_of_isDSIC_of_zeroNormalized hp.2 hp.1

/-- Myerson Lemma `(c)`:
the unique zero-normalized DSIC payment rule from `(b)` is given by the explicit
formula `bᵢ xᵢ(b) - ∫₀^{bᵢ} xᵢ(z, b₋ᵢ) dz`. -/
theorem payment_formula_of_zeroNormalized_and_isDSIC [DecidableEq I]
    {x p : (I → ℝ) → I → ℝ}
    (hp : ZeroNormalized p ∧
      ({ allocationRule := x, paymentRule := p } : SingleParameterMechanism I ℝ).IsDSIC)
    (b : I → ℝ) (i : I) :
    p b i = b i * x b i - ∫ z in 0..b i, x (Function.update b i z) i :=
  payment_formula_of_isDSIC_of_zeroNormalized hp.2 hp.1 b i

end MyersonLemma

end SingleParameterMechanism
