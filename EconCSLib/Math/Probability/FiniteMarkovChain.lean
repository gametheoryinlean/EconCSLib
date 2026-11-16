/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.Math.Probability.FiniteLaw
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Exact finite absorbing Markov-chain computation

Reusable exact finite-chain algorithms. Transient and terminal states have
explicit `Fin` encodings. Nonnegative rational rows sum to one, and terminal states
are absorbing. This is a Markov specification, not an EFG history quotient:
there is no assertion that an arbitrary EFG endpoint contains enough memory.

`run` computes censored first-hit data by the original transition rows.
`admissible` checks a finite-step absorption bound. `solve` uses executable
rational determinants and Cramer's rule, returning an explicit error if the
bound fails or the linear system is singular. `autoCheck` enumerates the full
transient domain at horizon `n+1`, and `autoSolve` computes its exact bound
before invoking that solver. Analytic correctness is proved separately in
`FiniteMarkovChain.Semantics`, keeping this executable module free of measure
and integral dependencies.
-/

namespace FiniteMarkovChain

open Matrix
open scoped BigOperators

/-- A fixed finite chain with transient block `Q`, terminal block `R`, and
state-dependent terminal reward. All fields are data except normalization. -/
structure Chain (n m : ℕ) where
  /-- Transient-to-transient probabilities. -/
  transient : Matrix (Fin n) (Fin n) ℚ≥0
  /-- Transient-to-terminal probabilities. -/
  terminal : Matrix (Fin n) (Fin m) ℚ≥0
  /-- Each complete transient row is a probability distribution. -/
  normalized : ∀ i, (∑ j, transient i j) + (∑ a, terminal i a) = 1
  /-- Original payoff at each terminal state. -/
  reward : Fin m → ℚ

namespace Chain

variable {n m : ℕ} (C : Chain n m)

/-- Rational transient matrix used in the linear systems. -/
def Q : Matrix (Fin n) (Fin n) ℚ := fun i j => C.transient i j

/-- Rational terminal matrix used in the linear systems. -/
def R : Matrix (Fin n) (Fin m) ℚ := fun i a => C.terminal i a

/-- The actual normalized row, enumerating every transient and terminal state. -/
def row (i : Fin n) : FiniteLaw (Fin n ⊕ Fin m) where
  atoms := (List.ofFn fun j => (Sum.inl j, C.transient i j)) ++
    (List.ofFn fun a => (Sum.inr a, C.terminal i a))
  normalized := by
    simpa only [List.map_append, List.map_map, Function.comp_def, List.sum_append,
      List.sum_ofFn, List.map_ofFn] using C.normalized i

/-- Terminal states stutter; transient states use their fixed transition row. -/
def step : (Fin n ⊕ Fin m) → FiniteLaw (Fin n ⊕ Fin m)
  | .inl i => C.row i
  | .inr a => FiniteLaw.pure (.inr a)

/-- Exact one-step expectation, separating the two matrix blocks. -/
theorem expectRat_row (i : Fin n) (f : (Fin n ⊕ Fin m) → ℚ) :
    (C.row i).expectRat f =
      (∑ j, C.Q i j * f (.inl j)) + ∑ a, C.R i a * f (.inr a) := by
  simp [row, FiniteLaw.expectRat, Q, R, Function.comp_def,
    List.map_ofFn, List.sum_ofFn]

/-- Nonnegative entries of the transient block. -/
theorem Q_nonneg (i j : Fin n) : 0 ≤ C.Q i j := (C.transient i j).property

/-- Nonnegative entries of the terminal block. -/
theorem R_nonneg (i : Fin n) (a : Fin m) : 0 ≤ C.R i a := (C.terminal i a).property

/-- Rational row normalization is inherited from the actual probability data. -/
theorem row_sum (i : Fin n) : (∑ j, C.Q i j) + (∑ a, C.R i a) = 1 := by
  dsimp [Q, R]
  exact_mod_cast C.normalized i

/-- A censored result is a still-active state or the first terminal state
and the number of preceding transient transitions. Hitting time is `r + 1`. -/
abbrev Result (n m : ℕ) := Fin n ⊕ (ℕ × Fin m)

/-- Retain a first hit while counting one additional earlier transition. -/
def delay : Result n m → Result n m
  | .inl i => .inl i
  | .inr (r, a) => .inr (r + 1, a)

/-- Execute at most `horizon` transitions from a transient state. A result
`inl` means only that the horizon ended before a hit. -/
def run : ℕ → Fin n → FiniteLaw (Result n m)
  | 0, i => FiniteLaw.pure (.inl i)
  | horizon + 1, i => (C.row i).bind fun state => match state with
    | .inl j => (run horizon j).map delay
    | .inr a => FiniteLaw.pure (.inr (0, a))

/-- First-hit coefficients: terminate after `r` transient transitions. -/
def hit (r : ℕ) : Matrix (Fin n) (Fin m) ℚ := C.Q ^ r * C.R

/-- Every transient path coefficient is nonnegative. -/
theorem pow_nonneg (r : ℕ) (i j : Fin n) : 0 ≤ (C.Q ^ r) i j :=
  Matrix.pow_apply_nonneg C.Q_nonneg r i j

/-- Every first-hit coefficient is nonnegative. -/
theorem hit_nonneg (r : ℕ) (i : Fin n) (a : Fin m) : 0 ≤ C.hit r i a :=
  Finset.sum_nonneg fun j _ => mul_nonneg (C.pow_nonneg r i j) (C.R_nonneg j a)

/-- The finite executor's complete censored first-hit law, tested against any
rational observable. The active term has not yet terminated; the sum records
each possible first-hit time separately. -/
theorem run_expect (horizon : ℕ) (i : Fin n)
    (active : Fin n → ℚ) (finished : ℕ → Fin m → ℚ) :
    (C.run horizon i).expectRat (Sum.elim active (fun x => finished x.1 x.2)) =
      (C.Q ^ horizon *ᵥ active) i +
        ∑ r ∈ Finset.range horizon, (C.hit r *ᵥ finished r) i := by
  induction horizon generalizing i finished with
  | zero => simp [run, FiniteLaw.expectRat_pure]
  | succ horizon ih =>
    simp only [run, FiniteLaw.expectRat_bind, C.expectRat_row,
      FiniteLaw.expectRat_map, FiniteLaw.expectRat_pure]
    have hdelay : (Sum.elim active (fun x => finished x.1 x.2)) ∘ delay =
        Sum.elim active (fun x => finished (x.1 + 1) x.2) := by
      funext x
      cases x with
      | inl j => rfl
      | inr pair => cases pair; rfl
    rw [hdelay]
    change (∑ j, C.Q i j *
      (C.run horizon j).expectRat
        (Sum.elim active (fun x => finished (x.1 + 1) x.2))) +
        ∑ a, C.R i a * finished 0 a = _
    have ihshift (j : Fin n) := ih j (fun r a => finished (r + 1) a)
    simp_rw [ihshift]
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib]
    have hfirst : (∑ j, C.Q i j * (C.Q ^ horizon *ᵥ active) j) =
        (C.Q ^ (horizon + 1) *ᵥ active) i := by
      change (C.Q *ᵥ (C.Q ^ horizon *ᵥ active)) i = _
      rw [Matrix.mulVec_mulVec, pow_succ']
    have hsum : (∑ j, C.Q i j *
        ∑ r ∈ Finset.range horizon, (C.hit r *ᵥ fun a => finished (r + 1) a) j) =
        ∑ r ∈ Finset.range horizon, (C.hit (r + 1) *ᵥ finished (r + 1)) i := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro r _
      change (C.Q *ᵥ (C.hit r *ᵥ finished (r + 1))) i = _
      rw [Matrix.mulVec_mulVec]
      rw [show C.Q * C.hit r = C.hit (r + 1) by
        simp only [hit, pow_succ', Matrix.mul_assoc]]
    rw [hfirst, hsum]
    rw [Finset.sum_range_succ']
    simp only [hit, pow_zero, Matrix.one_mul]
    change _ + _ + (C.R *ᵥ finished 0) i = _
    ring

/-- Each first-hit coefficient is the probability of that concrete censored
execution result, once the horizon includes its hit time. -/
theorem run_firstHit (horizon r : ℕ) (hr : r < horizon) (i : Fin n) (a : Fin m) :
    (C.run horizon i).expectRat (fun result =>
      if result = Sum.inr (r, a) then 1 else 0) = C.hit r i a := by
  have heq : (fun result : Result n m => if result = Sum.inr (r, a) then (1 : ℚ) else 0) =
      Sum.elim (fun _ => 0) (fun x => if x.1 = r then if x.2 = a then 1 else 0 else 0) := by
    funext result
    cases result <;> simp [Prod.ext_iff, ite_and]
  rw [heq, C.run_expect horizon i (fun _ => 0)
    (fun s b => if s = r then if b = a then 1 else 0 else 0)]
  simp [Matrix.mulVec, dotProduct, Finset.mem_range, hr]

/-- The survival probability is the row sum of the transient power. -/
theorem run_survival (horizon : ℕ) (i : Fin n) :
    (C.run horizon i).expectRat (Sum.elim (fun _ => 1) (fun _ => 0)) =
      ∑ j, (C.Q ^ horizon) i j := by
  simpa [Matrix.mulVec, dotProduct] using
    C.run_expect horizon i (fun _ => 1) (fun _ _ => 0)

/-- A checked `k`-step survival bound. The guaranteed absorption probability
is at least `1-c > 0` from every transient state. -/
def admissible (k : ℕ) (c : ℚ) : Bool :=
  decide (0 < k ∧ 0 ≤ c ∧ c < 1 ∧ ∀ i, (∑ j, (C.Q ^ k) i j) ≤ c)

/-- The checker exposes exactly the finite rational inequalities it tests. -/
theorem admissible_iff (k : ℕ) (c : ℚ) :
    C.admissible k c = true ↔
      0 < k ∧ 0 ≤ c ∧ c < 1 ∧ ∀ i, (∑ j, (C.Q ^ k) i j) ≤ c := by
  simp [admissible]

/-- Failure is explicit and does not assign a fictitious zero solution. -/
inductive SolveError
  | absorptionBound
  | singular
  deriving DecidableEq, Repr

/-- Exact Cramer solving on the finite rational matrix, with a singularity
test before dividing. No inverse matrix or solution is supplied by a caller. -/
def solveLinear (A : Matrix (Fin n) (Fin n) ℚ) (b : Fin n → ℚ) :
    Option (Fin n → ℚ) :=
  if A.det = 0 then none else some (A.det⁻¹ • A.cramer b)

/-- At a nonsingular matrix, the actual returned vector satisfies the system. -/
theorem solveLinear_spec (A : Matrix (Fin n) (Fin n) ℚ) (b : Fin n → ℚ)
    (hA : A.det ≠ 0) :
    ∃ x, solveLinear A b = some x ∧ A *ᵥ x = b := by
  refine ⟨A.det⁻¹ • A.cramer b, by simp [solveLinear, hA], ?_⟩
  rw [Matrix.mulVec_smul, Matrix.mulVec_cramer, smul_smul, inv_mul_cancel₀ hA, one_smul]

/-- The computed nonsingular solution is unique. -/
theorem solveLinear_unique (A : Matrix (Fin n) (Fin n) ℚ) (hA : A.det ≠ 0)
    {x y : Fin n → ℚ} (hx : A *ᵥ x = A *ᵥ y) : x = y :=
  (Matrix.mulVec_injective_iff_isUnit.mpr
    ((Matrix.isUnit_iff_isUnit_det A).mpr (isUnit_iff_ne_zero.mpr hA))) hx

/-- Solve both Bellman systems, extending the returned vectors by `v=g`
and `t=0` at terminal states. -/
def solve (k : ℕ) (c : ℚ) :
    Except SolveError (((Fin n ⊕ Fin m) → ℚ) × ((Fin n ⊕ Fin m) → ℚ)) :=
  if C.admissible k c then
    match solveLinear (1 - C.Q) (C.R *ᵥ C.reward),
      solveLinear (1 - C.Q) (fun _ => 1) with
    | some v, some t => .ok (Sum.elim v C.reward, Sum.elim t (fun _ => 0))
    | _, _ => .error .singular
  else .error .absorptionBound

/-- Exact unfinished probability, identified with the finite executor by
`run_survival`. No transient state is removed from the supplied domain. -/
def survival (horizon : ℕ) (i : Fin n) : ℚ := ∑ j, (C.Q ^ horizon) i j

/-- A transient start is unfinished at time zero. -/
theorem survival_zero (i : Fin n) : C.survival 0 i = 1 := by
  simp [survival, Matrix.one_apply]

/-- Survival evolves by the original transient transition matrix. -/
theorem survival_succ (horizon : ℕ) (i : Fin n) :
    C.survival (horizon + 1) i = ∑ j, C.Q i j * C.survival horizon j := by
  simp only [survival, pow_succ', Matrix.mul_apply, Finset.mul_sum]
  exact Finset.sum_comm

/-- Unfinished probabilities are nonnegative. -/
theorem survival_nonneg (horizon : ℕ) (i : Fin n) : 0 ≤ C.survival horizon i :=
  Finset.sum_nonneg fun j _ => C.pow_nonneg horizon i j

/-- Normalized nonnegative rows keep every survival probability at most one. -/
theorem survival_le_one (horizon : ℕ) (i : Fin n) : C.survival horizon i ≤ 1 := by
  induction horizon generalizing i with
  | zero => simp [C.survival_zero]
  | succ horizon ih =>
    rw [C.survival_succ]
    calc
      _ ≤ ∑ j, C.Q i j * 1 := Finset.sum_le_sum fun j _ =>
        mul_le_mul_of_nonneg_left (ih j) (C.Q_nonneg i j)
      _ ≤ 1 := by
        simp only [mul_one]
        have := C.row_sum i
        have := Finset.sum_nonneg (fun a (_ : a ∈ Finset.univ) => C.R_nonneg i a)
        linarith

/-- Increasing the execution horizon cannot increase unfinished mass. -/
theorem survival_antitone (i : Fin n) : Antitone (fun horizon => C.survival horizon i) := by
  have hstep (horizon : ℕ) : ∀ i, C.survival (horizon + 1) i ≤ C.survival horizon i := by
    induction horizon with
    | zero => intro i; simpa [C.survival_zero] using C.survival_le_one 1 i
    | succ horizon ih =>
      intro i
      rw [C.survival_succ, C.survival_succ horizon]
      exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (ih j) (C.Q_nonneg i j)
  exact antitone_nat_of_succ_le fun horizon => hstep horizon i

private theorem survival_deficit (horizon : ℕ) (i : Fin n) :
    1 - C.survival (horizon + 1) i =
      (∑ a, C.R i a) + ∑ j, C.Q i j * (1 - C.survival horizon j) := by
  rw [C.survival_succ]
  simp only [mul_sub, mul_one, Finset.sum_sub_distrib]
  linarith [C.row_sum i]

/-- Positive finite-step termination means a positive immediate exit or a
positive transient edge to a state that can terminate in the remaining steps. -/
theorem survival_succ_lt_one_iff (horizon : ℕ) (i : Fin n) :
    C.survival (horizon + 1) i < 1 ↔
      (∃ a, 0 < C.R i a) ∨ ∃ j, 0 < C.Q i j ∧ C.survival horizon j < 1 := by
  have hr := Finset.sum_nonneg (fun a (_ : a ∈ Finset.univ) => C.R_nonneg i a)
  have hq (j : Fin n) : 0 ≤ C.Q i j * (1 - C.survival horizon j) :=
    mul_nonneg (C.Q_nonneg i j) (sub_nonneg.mpr (C.survival_le_one horizon j))
  have hadd : 0 < (∑ a, C.R i a) + ∑ j, C.Q i j * (1 - C.survival horizon j) ↔
      0 < ∑ a, C.R i a ∨ 0 < ∑ j, C.Q i j * (1 - C.survival horizon j) := by
    have := Finset.sum_nonneg fun j (_ : j ∈ Finset.univ) => hq j
    constructor
    · intro h; by_cases h' : 0 < ∑ a, C.R i a
      · exact Or.inl h'
      · exact Or.inr (by linarith)
    · rintro (h | h) <;> linarith
  rw [← sub_pos, C.survival_deficit,
    hadd,
    Finset.sum_pos_iff_of_nonneg (fun a _ => C.R_nonneg i a),
    Finset.sum_pos_iff_of_nonneg (fun j _ => hq j)]
  simp only [Finset.mem_univ, true_and]
  apply or_congr Iff.rfl
  apply exists_congr
  intro j
  rw [mul_pos_iff]
  have := C.Q_nonneg i j
  simp only [sub_pos]
  constructor
  · rintro (h | h)
    · exact h
    · linarith [h.1]
  · exact Or.inl

-- Finite reachability sets provide the path-shortening argument without a
-- separate graph representation. Their recurrence is the positive-edge law above.
private def finishWithin (horizon : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun i => C.survival horizon i < 1

private theorem mem_finishWithin (horizon : ℕ) (i : Fin n) :
    i ∈ C.finishWithin horizon ↔ C.survival horizon i < 1 := by
  simp [finishWithin]

private theorem finishWithin_mono : Monotone C.finishWithin := by
  intro h k hle i hi
  rw [C.mem_finishWithin] at hi ⊢
  exact (C.survival_antitone i hle).trans_lt hi

private theorem finishWithin_step {h k : ℕ}
    (heq : C.finishWithin h = C.finishWithin k) :
    C.finishWithin (h + 1) = C.finishWithin (k + 1) := by
  ext i
  simp only [C.mem_finishWithin, C.survival_succ_lt_one_iff]
  simp_rw [← C.mem_finishWithin, heq]

private theorem finishWithin_stable (horizon : ℕ) (hle : n ≤ horizon) :
    C.finishWithin horizon = C.finishWithin n := by
  have hc : (C.finishWithin horizon).card = (C.finishWithin n).card := by
    apply Nat.stabilises_of_monotone (Finset.card_mono.comp C.finishWithin_mono)
      (fun k => by simpa using Finset.card_le_univ (C.finishWithin k)) _ hle
    intro k heq
    have hsets := Finset.eq_of_subset_of_card_le (C.finishWithin_mono (Nat.le_succ k))
      heq.ge
    exact congrArg Finset.card (C.finishWithin_step hsets)
  exact (Finset.eq_of_subset_of_card_le (C.finishWithin_mono hle) hc.le).symm

/-- Finite-dimensional completeness: any positive-probability terminal route
can be witnessed within `n` steps. The increasing reachable sets stabilize
after at most `n` strict cardinality increases, including when `n = 0`. -/
theorem finite_horizon_complete (i : Fin n) :
    (∃ horizon, C.survival horizon i < 1) ↔ C.survival n i < 1 := by
  constructor
  · rintro ⟨horizon, hh⟩
    by_cases hle : horizon ≤ n
    · exact (C.survival_antitone i hle).trans_lt hh
    · have heq := C.finishWithin_stable horizon (Nat.le_of_not_ge hle)
      rw [← C.mem_finishWithin, ← heq, C.mem_finishWithin]
      exact hh
  · exact fun h => ⟨n, h⟩

/-- Automatically compute the maximum of zero and all `(n+1)`-step survival
rows using the explicit `Fin n` enumeration. An empty transient domain gives zero. -/
def autoBound : ℚ≥0 :=
  Finset.univ.sup fun i => ⟨C.survival (n + 1) i, C.survival_nonneg (n + 1) i⟩

/-- Each transient row is below the computed common survival bound. -/
theorem survival_le_autoBound (i : Fin n) : C.survival (n + 1) i ≤ (C.autoBound : ℚ) := by
  exact show (⟨C.survival (n + 1) i, C.survival_nonneg (n + 1) i⟩ : ℚ≥0) ≤ C.autoBound from
    Finset.le_sup (f := fun j =>
      (⟨C.survival (n + 1) j, C.survival_nonneg (n + 1) j⟩ : ℚ≥0)) (Finset.mem_univ i)

/-- The computed bound is nonnegative and at most one, including the empty case. -/
theorem autoBound_bounds : 0 ≤ (C.autoBound : ℚ) ∧ C.autoBound ≤ 1 := by
  refine ⟨C.autoBound.property, Finset.sup_le fun i _ => ?_⟩
  exact show C.survival (n + 1) i ≤ 1 from C.survival_le_one (n + 1) i

/-- Exact automatic absorption test on every supplied transient state. -/
def autoCheck : Bool := C.admissible (n + 1) C.autoBound

/-- The automatic test is exactly positivity of a finite terminal route from
every state. This theorem supplies its finite-dimensional completeness argument. -/
theorem autoCheck_iff_reaches :
    C.autoCheck = true ↔ ∀ i, ∃ horizon, C.survival horizon i < 1 := by
  have hb : C.autoCheck = true ↔ C.autoBound < 1 := by
    rw [autoCheck, C.admissible_iff]
    have hnonneg := C.autoBound_bounds.1
    constructor
    · exact fun h => h.2.2.1
    · exact fun h => ⟨Nat.zero_lt_succ n, hnonneg, h, C.survival_le_autoBound⟩
  rw [hb, autoBound, Finset.sup_lt_iff (by norm_num : (0 : ℚ≥0) < 1)]
  simp only [Finset.mem_univ, forall_const]
  constructor
  · exact fun h i => ⟨n + 1, h i⟩
  · intro h i
    exact (C.survival_antitone i (Nat.le_succ n)).trans_lt
      ((C.finite_horizon_complete i).mp (h i))

/-- A rejected full-domain test exhibits a state whose unfinished probability
stays exactly one forever. It does not say that every state fails to absorb. -/
theorem autoCheck_failure (h : C.autoCheck = false) :
    ∃ i : Fin n, ∀ horizon, C.survival horizon i = 1 := by
  have hn : ¬ ∀ i, ∃ horizon, C.survival horizon i < 1 := by
    intro hr
    have := C.autoCheck_iff_reaches.mpr hr
    simp [h] at this
  push Not at hn
  obtain ⟨i, hi⟩ := hn
  exact ⟨i, fun horizon => (C.survival_le_one horizon i).antisymm (hi horizon)⟩

/-- Compute the certificate and invoke the existing exact rational solver.
No absorption proof, block bound, candidate solution or rate is supplied. -/
def autoSolve :
    Except SolveError (((Fin n ⊕ Fin m) → ℚ) × ((Fin n ⊕ Fin m) → ℚ)) :=
  C.solve (n + 1) C.autoBound

/-- A failed automatic check preserves the original explicit bound error. -/
theorem autoSolve_of_rejected (h : C.autoCheck = false) :
    C.autoSolve = .error .absorptionBound := by
  change C.admissible (n + 1) C.autoBound = false at h
  simp [autoSolve, solve, h]

end Chain


end FiniteMarkovChain
