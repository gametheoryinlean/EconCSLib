/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.OpenProblem.New.QueryComplexityOfTarski.Problem

/-!
# QueryComplexityOfTarski: supporting material

Auxiliary definitions and lemmas for the problem statement.
-/

section

/-!
## Memoization for the existing finite Tarski query trees

The transformation receives no oracle table. It reuses cached replies and only stores
replies returned at fresh query nodes. This normalizes the already defined trees and
finite lotteries, not arbitrary coin-based algorithms.
-/

namespace EconCSLib.OpenProblem.New.EconCSBench.QueryComplexityOfTarski

open scoped BigOperators

abbrev QueryMemo (N d : ℕ) := Grid N d → Option (Grid N d)

/-- Every cached answer agrees with the fixed oracle. -/
def QueryMemo.IsConsistent {N d : ℕ} (memo : QueryMemo N d)
    (f : Grid N d → Grid N d) : Prop :=
  ∀ point answer, memo point = some answer → answer = f point

/-- The empty cache is consistent with every oracle. -/
theorem QueryMemo.empty_consistent {N d : ℕ} (f : Grid N d → Grid N d) :
    QueryMemo.IsConsistent (fun _ => none : QueryMemo N d) f := by
  intro point answer h
  cases h

/-- Recording an actual answer preserves consistency. -/
theorem QueryMemo.IsConsistent.update {N d : ℕ} {memo : QueryMemo N d}
    {f : Grid N d → Grid N d} (h : memo.IsConsistent f) (point : Grid N d) :
    QueryMemo.IsConsistent (Function.update memo point (some (f point))) f := by
  intro q answer hq
  by_cases heq : q = point
  · subst q
    simpa using hq.symm
  · apply h q answer
    simpa [Function.update, heq] using hq

/-- Cached replies incur no query; fresh replies enter the next cache. -/
def TarskiQueryTree.memoize {N d : ℕ} :
    TarskiQueryTree N d → QueryMemo N d → TarskiQueryTree N d
  | .output point, _ => .output point
  | .query point next, memo =>
      match memo point with
      | some answer => (next answer).memoize memo
      | none => .query point (fun answer =>
          (next answer).memoize (Function.update memo point (some answer)))

/-- Normalization from an empty cache is independent of the hidden oracle. -/
def TarskiQueryTree.normalize {N d : ℕ} (tree : TarskiQueryTree N d) :
    TarskiQueryTree N d := tree.memoize (fun _ => none)

/-- Memoization preserves output for every fixed oracle and consistent cache. -/
theorem TarskiQueryTree.memoize_output {N d : ℕ} (tree : TarskiQueryTree N d)
    (memo : QueryMemo N d) (f : Grid N d → Grid N d)
    (h : memo.IsConsistent f) :
    ((tree.memoize memo).run f).1 = (tree.run f).1 := by
  induction tree generalizing memo with
  | output point => rfl
  | query point next ih =>
      cases hm : memo point with
      | none =>
          simpa [memoize, hm, run] using
            ih (f point) (Function.update memo point (some (f point))) (h.update point)
      | some answer =>
          have ha := h point answer hm
          subst answer
          simpa [memoize, hm, run] using ih (f point) memo h

/-- Repeated queries can only decrease the charged query count. -/
theorem TarskiQueryTree.memoize_cost_le {N d : ℕ} (tree : TarskiQueryTree N d)
    (memo : QueryMemo N d) (f : Grid N d → Grid N d)
    (h : memo.IsConsistent f) :
    ((tree.memoize memo).run f).2 ≤ (tree.run f).2 := by
  induction tree generalizing memo with
  | output point => exact le_rfl
  | query point next ih =>
      cases hm : memo point with
      | none =>
          simpa [memoize, hm, run] using
            Nat.add_le_add_right
              (ih (f point) (Function.update memo point (some (f point)))
                (h.update point)) 1
      | some answer =>
          have ha := h point answer hm
          subst answer
          simp only [memoize, hm, run]
          exact (ih (f point) memo h).trans (Nat.le_add_right _ 1)

/-- A structural fresh-query invariant, including every possible reply branch. -/
def TarskiQueryTree.QueriesFresh {N d : ℕ} :
    TarskiQueryTree N d → QueryMemo N d → Prop
  | .output _, _ => True
  | .query point next, memo =>
      memo point = none ∧ ∀ answer,
        (next answer).QueriesFresh (Function.update memo point (some answer))

/-- No cached point is queried along any branch of the transformed tree. -/
theorem TarskiQueryTree.memoize_queriesFresh {N d : ℕ} (tree : TarskiQueryTree N d)
    (memo : QueryMemo N d) : (tree.memoize memo).QueriesFresh memo := by
  induction tree generalizing memo with
  | output point => trivial
  | query point next ih =>
      cases hm : memo point with
      | none =>
          simp only [memoize, hm, QueriesFresh]
          exact ⟨trivial, fun answer => ih answer _⟩
      | some answer => simpa [memoize, hm] using ih answer memo

/-- The finite set of points with no cached reply. -/
def QueryMemo.uncached {N d : ℕ} (memo : QueryMemo N d) : Finset (Grid N d) :=
  Finset.univ.filter fun point => memo point = none

theorem QueryMemo.uncached_update {N d : ℕ} (memo : QueryMemo N d)
    (point answer : Grid N d) :
    QueryMemo.uncached (Function.update memo point (some answer)) =
      memo.uncached.erase point := by
  classical
  ext q
  by_cases hq : q = point
  · subst q
    simp [uncached]
  · simp [uncached, Function.update, hq]

/-- Fresh-query trees are bounded by the number of initially uncached points. -/
theorem TarskiQueryTree.cost_le_uncached_of_queriesFresh {N d : ℕ}
    (tree : TarskiQueryTree N d) (memo : QueryMemo N d)
    (hfresh : tree.QueriesFresh memo) (f : Grid N d → Grid N d) :
    (tree.run f).2 ≤ memo.uncached.card := by
  induction tree generalizing memo with
  | output point => exact Nat.zero_le _
  | query point next ih =>
      obtain ⟨hm, hn⟩ := hfresh
      have hmem : point ∈ memo.uncached := by simp [QueryMemo.uncached, hm]
      have hchild := ih (f point) (Function.update memo point (some (f point)))
        (hn (f point))
      calc
        ((TarskiQueryTree.query point next).run f).2 =
            ((next (f point)).run f).2 + 1 := rfl
        _ ≤ (QueryMemo.uncached (Function.update memo point (some (f point)))).card + 1 :=
          Nat.add_le_add_right hchild 1
        _ = memo.uncached.card := by
          rw [QueryMemo.uncached_update, Finset.card_erase_add_one hmem]

/-- The count bound does not require the initial cached values to be correct. -/
theorem TarskiQueryTree.memoize_cost_le_uncached {N d : ℕ}
    (tree : TarskiQueryTree N d) (memo : QueryMemo N d)
    (f : Grid N d → Grid N d) :
    ((tree.memoize memo).run f).2 ≤ memo.uncached.card :=
  (tree.memoize memo).cost_le_uncached_of_queriesFresh memo
    (tree.memoize_queriesFresh memo) f

theorem TarskiQueryTree.normalize_output {N d : ℕ} (tree : TarskiQueryTree N d)
    (f : Grid N d → Grid N d) :
    (tree.normalize.run f).1 = (tree.run f).1 :=
  tree.memoize_output _ f (QueryMemo.empty_consistent f)

theorem TarskiQueryTree.normalize_cost_le {N d : ℕ} (tree : TarskiQueryTree N d)
    (f : Grid N d → Grid N d) :
    (tree.normalize.run f).2 ≤ (tree.run f).2 :=
  tree.memoize_cost_le _ f (QueryMemo.empty_consistent f)

theorem TarskiQueryTree.normalize_cost_le_card {N d : ℕ} (tree : TarskiQueryTree N d)
    (f : Grid N d → Grid N d) :
    (tree.normalize.run f).2 ≤ Fintype.card (Grid N d) := by
  simpa [normalize, QueryMemo.uncached] using
    tree.memoize_cost_le_uncached (fun _ => none) f

theorem TarskiQueryTree.normalize_isCorrect_iff {N d : ℕ}
    (tree : TarskiQueryTree N d) : tree.normalize.IsCorrect ↔ tree.IsCorrect := by
  simp only [IsCorrect, normalize_output]

/-- Normalize each deterministic component without changing the seed law. -/
def RandomizedTarskiQueryAlgorithm.normalize {N d seeds : ℕ}
    (A : RandomizedTarskiQueryAlgorithm N d seeds) :
    RandomizedTarskiQueryAlgorithm N d seeds where
  seedDist := A.seedDist
  program seed := (A.program seed).normalize

/-- Every seed keeps its output, so every fixed oracle keeps its success probability. -/
theorem RandomizedTarskiQueryAlgorithm.normalize_successProbability {N d seeds : ℕ}
    (A : RandomizedTarskiQueryAlgorithm N d seeds) (f : Grid N d → Grid N d) :
    A.normalize.successProbability f = A.successProbability f := by
  simp only [successProbability, normalize, TarskiQueryTree.normalize_output]

theorem RandomizedTarskiQueryAlgorithm.normalize_isBoundedErrorCorrect_iff
    {N d seeds : ℕ} (A : RandomizedTarskiQueryAlgorithm N d seeds) :
    A.normalize.IsBoundedErrorCorrect ↔ A.IsBoundedErrorCorrect := by
  simp only [IsBoundedErrorCorrect, normalize_successProbability]

/-- Unconditional expected cost, including unsuccessful seeds, cannot increase. -/
theorem RandomizedTarskiQueryAlgorithm.normalize_expectedQueryCount_le
    {N d seeds : ℕ} (A : RandomizedTarskiQueryAlgorithm N d seeds)
    (f : Grid N d → Grid N d) :
    A.normalize.expectedQueryCount f ≤ A.expectedQueryCount f := by
  apply Finset.sum_le_sum
  intro seed _
  apply mul_le_mul_of_nonneg_left
  · exact_mod_cast (A.program seed).normalize_cost_le f
  · exact A.seedDist.property.1 seed

/-- The normalized cost is at most the number of grid points for every seed. -/
theorem RandomizedTarskiQueryAlgorithm.normalize_seed_cost_le_card
    {N d seeds : ℕ} (A : RandomizedTarskiQueryAlgorithm N d seeds)
    (seed : Fin (seeds + 1)) (f : Grid N d → Grid N d) :
    ((A.normalize.program seed).run f).2 ≤ Fintype.card (Grid N d) :=
  (A.program seed).normalize_cost_le_card f

end EconCSLib.OpenProblem.New.EconCSBench.QueryComplexityOfTarski

end


section

/-!
## Finite compression of measurable seed families

The key records outputs and truncated original costs for a finite family of promised
oracles. The all-oracle special case is also retained. Selecting a representative is a
semantic existence construction, not oracle access granted to any executing query
tree.
-/

namespace EconCSLib.OpenProblem.New.EconCSBench.QueryComplexityOfTarski

open MeasureTheory
open scoped BigOperators

noncomputable section

/-- The real masses of a finite measurable partition form a native lottery. -/
def fiberLottery {Seed I : Type*} [MeasurableSpace Seed] [Fintype I]
    (μ : Measure Seed) [IsProbabilityMeasure μ] (key : Seed → I)
    (hkey : ∀ i, MeasurableSet {seed | key seed = i}) : Lottery ℝ I := by
  classical
  refine ⟨fun i => μ.real {seed | key seed = i}, ?_, ?_⟩
  · intro i
    exact ENNReal.toReal_nonneg
  · have hsum := sum_measureReal_preimage_singleton (μ := μ) Finset.univ
      (f := key) (fun i _ => hkey i)
    simpa using hsum

/-- Finite partition integration, without a measurable-space choice for the labels. -/
theorem fiberLottery_expectedValue {Seed I : Type*}
    [MeasurableSpace Seed] [Fintype I]
    (μ : Measure Seed) [IsProbabilityMeasure μ] (key : Seed → I)
    (hkey : ∀ i, MeasurableSet {seed | key seed = i}) (g : I → ℝ) :
    ∑ i, (fiberLottery μ key hkey).val i * g i =
      ∫ seed, g (key seed) ∂μ := by
  classical
  have hpoint : (fun seed => g (key seed)) =
      fun seed => ∑ i, {seed | key seed = i}.indicator (fun _ => g i) seed := by
    funext seed
    simp [Set.indicator_apply, eq_comm]
  rw [hpoint, integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [integral_indicator_const _ (hkey i)]
    rfl
  · intro i _
    exact (integrable_const (g i)).indicator (hkey i)

theorem fiber_integrable {Seed I : Type*} [MeasurableSpace Seed] [Fintype I]
    (μ : Measure Seed) [IsProbabilityMeasure μ] (key : Seed → I)
    (hkey : ∀ i, MeasurableSet {seed | key seed = i}) (g : I → ℝ) :
    Integrable (fun seed => g (key seed)) μ := by
  classical
  have hs : Integrable (fun seed =>
      ∑ i, {seed | key seed = i}.indicator (fun _ => g i) seed) μ :=
    integrable_finsetSum Finset.univ fun i _ =>
      (integrable_const (g i)).indicator (hkey i)
  convert hs using 1
  funext seed
  simp [Set.indicator_apply, eq_comm]

/-- A selected representative comes from the same key whenever that key occurs. -/
def fiberRepresentative {Seed I : Type*} [Nonempty Seed] (key : Seed → I) (i : I) :
    Seed := by
  classical
  exact if h : ∃ seed, key seed = i then Classical.choose h
    else Classical.choice inferInstance

theorem fiberRepresentative_key {Seed I : Type*} [Nonempty Seed]
    (key : Seed → I) (seed : Seed) :
    key (fiberRepresentative key (key seed)) = key seed := by
  have h : ∃ x, key x = key seed := ⟨seed, rfl⟩
  simp only [fiberRepresentative, dif_pos h]
  exact Classical.choose_spec h

/-!
## Promise-indexed compression
-/

attribute [local instance] Classical.propDecidable

/-- Only promised oracles contribute coordinates to this finite key. -/
abbrev PromisePerformance (N d : ℕ) (P : (Grid N d → Grid N d) → Prop) :=
  {f : Grid N d → Grid N d // P f} →
    Grid N d × Fin (Fintype.card (Grid N d) + 1)

def TarskiQueryTree.promisePerformance {N d : ℕ}
    (P : (Grid N d → Grid N d) → Prop) (tree : TarskiQueryTree N d) :
    PromisePerformance N d P := fun f =>
  ((tree.run f.val).1, ⟨min (tree.run f.val).2 (Fintype.card (Grid N d)),
    Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩)

theorem TarskiQueryTree.normalize_dominates_of_promisePerformance_eq {N d : ℕ}
    {P : (Grid N d → Grid N d) → Prop} {representative tree : TarskiQueryTree N d}
    (h : representative.promisePerformance P = tree.promisePerformance P)
    (f : Grid N d → Grid N d) (hf : P f) :
    (representative.normalize.run f).1 = (tree.run f).1 ∧
      (representative.normalize.run f).2 ≤ (tree.run f).2 := by
  have hp := congrFun h ⟨f, hf⟩
  have ho := congrArg Prod.fst hp
  have hc := congrArg (fun p => (p.2 : ℕ)) hp
  refine ⟨(representative.normalize_output f).trans ho, ?_⟩
  have hb := le_min (representative.normalize_cost_le f)
    (representative.normalize_cost_le_card f)
  change min (representative.run f).2 (Fintype.card (Grid N d)) =
    min (tree.run f).2 (Fintype.card (Grid N d)) at hc
  rw [hc] at hb
  exact hb.trans (Nat.min_le_left _ _)

theorem measurable_promisePerformance {N d : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] (P : (Grid N d → Grid N d) → Prop)
    (program : Seed → TarskiQueryTree N d)
    (h : ∀ f, P f → Measurable (fun seed => (program seed).run f)) :
    Measurable (fun seed => (program seed).promisePerformance P) := by
  apply measurable_pi_lambda
  intro f
  let truncate : Grid N d × ℕ → Grid N d × Fin (Fintype.card (Grid N d) + 1) :=
    fun p => (p.1, ⟨min p.2 (Fintype.card (Grid N d)),
      Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩)
  exact (measurable_of_countable truncate).comp (h f.val f.property)

/-- Representatives need only agree on promised inputs. -/
def promiseCompressedProgram {N d : ℕ} {Seed : Type*} [Nonempty Seed]
    (P : (Grid N d → Grid N d) → Prop) (program : Seed → TarskiQueryTree N d)
    (key : PromisePerformance N d P) : TarskiQueryTree N d :=
  (program (fiberRepresentative
    (fun seed => (program seed).promisePerformance P) key)).normalize

theorem promiseCompressedProgram_dominates {N d : ℕ} {Seed : Type*} [Nonempty Seed]
    (P : (Grid N d → Grid N d) → Prop) (program : Seed → TarskiQueryTree N d)
    (seed : Seed) (f : Grid N d → Grid N d) (hf : P f) :
    ((promiseCompressedProgram P program ((program seed).promisePerformance P)).run f).1 =
        ((program seed).run f).1 ∧
      ((promiseCompressedProgram P program ((program seed).promisePerformance P)).run f).2 ≤
        ((program seed).run f).2 :=
  TarskiQueryTree.normalize_dominates_of_promisePerformance_eq
    (fiberRepresentative_key (fun seed => (program seed).promisePerformance P) seed) f hf

def promiseCompressedLottery {N d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (P : (Grid N d → Grid N d) → Prop) (μ : Measure Seed) [IsProbabilityMeasure μ]
    (program : Seed → TarskiQueryTree N d)
    (h : ∀ f, P f → Measurable (fun seed => (program seed).run f)) :
    Lottery ℝ (PromisePerformance N d P) :=
  fiberLottery μ (fun seed => (program seed).promisePerformance P)
    (fun key => (measurable_promisePerformance P program h) (measurableSet_singleton key))

theorem promiseCompressedLottery_output_expectation {N d : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] [Nonempty Seed]
    (P : (Grid N d → Grid N d) → Prop) (μ : Measure Seed) [IsProbabilityMeasure μ]
    (program : Seed → TarskiQueryTree N d)
    (h : ∀ f, P f → Measurable (fun seed => (program seed).run f))
    (f : Grid N d → Grid N d) (hf : P f) (g : Grid N d → ℝ) :
    ∑ key, (promiseCompressedLottery P μ program h).val key *
      g ((promiseCompressedProgram P program key).run f).1 =
        ∫ seed, g ((program seed).run f).1 ∂μ := by
  unfold promiseCompressedLottery
  rw [fiberLottery_expectedValue]
  apply integral_congr_ae
  filter_upwards [] with seed
  rw [(promiseCompressedProgram_dominates P program seed f hf).1]

theorem promiseCompressedLottery_expected_cost_le {N d : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] [Nonempty Seed]
    (P : (Grid N d → Grid N d) → Prop) (μ : Measure Seed) [IsProbabilityMeasure μ]
    (program : Seed → TarskiQueryTree N d)
    (h : ∀ f, P f → Measurable (fun seed => (program seed).run f))
    (f : Grid N d → Grid N d) (hf : P f)
    (hfinite : Integrable (fun seed => (((program seed).run f).2 : ℝ)) μ) :
    ∑ key, (promiseCompressedLottery P μ program h).val key *
      (((promiseCompressedProgram P program key).run f).2 : ℝ) ≤
        ∫ seed, (((program seed).run f).2 : ℝ) ∂μ := by
  unfold promiseCompressedLottery
  rw [fiberLottery_expectedValue]
  apply integral_mono (fiber_integrable μ (fun seed => (program seed).promisePerformance P)
      (fun key => (measurable_promisePerformance P program h) (measurableSet_singleton key))
      (fun key => (((promiseCompressedProgram P program key).run f).2 : ℝ))) hfinite
  intro seed
  exact Nat.cast_le.mpr (promiseCompressedProgram_dominates P program seed f hf).2

/-- Arbitrary measurable seed families compress using assumptions only on the fixed
promise domain. Count bounds hold on all inputs, but output and expected cost
comparisons are asserted only on promised inputs. -/
theorem exists_finite_lottery_of_promised_measurable_seed_family {N d : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] (P : (Grid N d → Grid N d) → Prop)
    (μ : Measure Seed) [IsProbabilityMeasure μ] (program : Seed → TarskiQueryTree N d)
    (h : ∀ f, P f → Measurable (fun seed => (program seed).run f)) :
    ∃ seeds : ℕ, ∃ A : RandomizedTarskiQueryAlgorithm N d seeds,
      (∀ (f : Grid N d → Grid N d), P f → ∀ g : Grid N d → ℝ,
        ∑ seed, A.seedDist.val seed * g ((A.program seed).run f).1 =
          ∫ seed, g ((program seed).run f).1 ∂μ) ∧
      (∀ f : Grid N d → Grid N d, P f →
        Integrable (fun seed => (((program seed).run f).2 : ℝ)) μ →
          A.expectedQueryCount f ≤ ∫ seed, (((program seed).run f).2 : ℝ) ∂μ) ∧
      ∀ seed f, ((A.program seed).run f).2 ≤ Fintype.card (Grid N d) := by
  letI : Nonempty Seed := nonempty_of_isProbabilityMeasure μ
  letI : Nonempty (PromisePerformance N d P) :=
    ⟨(program (Classical.choice (inferInstance : Nonempty Seed))).promisePerformance P⟩
  let L := promiseCompressedLottery P μ program h
  have hcard : Fintype.card (PromisePerformance N d P) - 1 + 1 =
      Fintype.card (PromisePerformance N d P) :=
    Nat.sub_add_cancel (Nat.succ_le_of_lt Fintype.card_pos)
  let e : Fin (Fintype.card (PromisePerformance N d P) - 1 + 1) ≃
      PromisePerformance N d P :=
    (finCongr hcard).trans (Fintype.equivFin (PromisePerformance N d P)).symm
  let A : RandomizedTarskiQueryAlgorithm N d (Fintype.card (PromisePerformance N d P) - 1) :=
    { seedDist := ⟨fun seed => L.val (e seed),
        fun seed => L.property.1 (e seed),
        (e.sum_comp L.val).trans L.property.2⟩
      program := fun seed => promiseCompressedProgram P program (e seed) }
  refine ⟨_, A, ?_, ?_, ?_⟩
  · intro f hf g
    change (∑ seed, L.val (e seed) *
      g ((promiseCompressedProgram P program (e seed)).run f).1) = _
    rw [e.sum_comp (fun key => L.val key *
      g ((promiseCompressedProgram P program key).run f).1)]
    exact promiseCompressedLottery_output_expectation P μ program h f hf g
  · intro f hf hfinite
    change (∑ seed, L.val (e seed) *
      (((promiseCompressedProgram P program (e seed)).run f).2 : ℝ)) ≤ _
    rw [e.sum_comp (fun key => L.val key *
      (((promiseCompressedProgram P program key).run f).2 : ℝ))]
    exact promiseCompressedLottery_expected_cost_le P μ program h f hf hfinite
  · intro seed f
    exact TarskiQueryTree.normalize_cost_le_card _ f

/-- The Tarski promise requires no measurability assumptions on nonmonotone inputs. -/
theorem exists_finite_lottery_of_monotone_measurable_seed_family {N d : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] (μ : Measure Seed) [IsProbabilityMeasure μ]
    (program : Seed → TarskiQueryTree N d)
    (h : ∀ f, IsGridMonotone f → Measurable (fun seed => (program seed).run f)) :
    ∃ seeds : ℕ, ∃ A : RandomizedTarskiQueryAlgorithm N d seeds,
      (∀ (f : Grid N d → Grid N d), IsGridMonotone f → ∀ g : Grid N d → ℝ,
        ∑ seed, A.seedDist.val seed * g ((A.program seed).run f).1 =
          ∫ seed, g ((program seed).run f).1 ∂μ) ∧
      (∀ f : Grid N d → Grid N d, IsGridMonotone f →
        Integrable (fun seed => (((program seed).run f).2 : ℝ)) μ →
          A.expectedQueryCount f ≤ ∫ seed, (((program seed).run f).2 : ℝ) ∂μ) ∧
      ∀ seed f, ((A.program seed).run f).2 ≤ Fintype.card (Grid N d) :=
  exists_finite_lottery_of_promised_measurable_seed_family IsGridMonotone μ program h

/-- Unrestricted-input specialization of the promise-indexed theorem. -/
theorem exists_finite_lottery_of_measurable_seed_family {N d : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] (μ : Measure Seed) [IsProbabilityMeasure μ]
    (program : Seed → TarskiQueryTree N d)
    (h : ∀ f : Grid N d → Grid N d,
      Measurable (fun seed => (program seed).run f)) :
    ∃ seeds : ℕ, ∃ A : RandomizedTarskiQueryAlgorithm N d seeds,
      (∀ (f : Grid N d → Grid N d) (g : Grid N d → ℝ),
        ∑ seed, A.seedDist.val seed * g ((A.program seed).run f).1 =
          ∫ seed, g ((program seed).run f).1 ∂μ) ∧
      (∀ f : Grid N d → Grid N d,
        Integrable (fun seed => (((program seed).run f).2 : ℝ)) μ →
          A.expectedQueryCount f ≤ ∫ seed, (((program seed).run f).2 : ℝ) ∂μ) ∧
      ∀ seed f, ((A.program seed).run f).2 ≤ Fintype.card (Grid N d) := by
  obtain ⟨seeds, A, hout, hcost, hbound⟩ :=
    exists_finite_lottery_of_promised_measurable_seed_family
      (fun _ => True) μ program (fun f _ => h f)
  exact ⟨seeds, A, fun f => hout f trivial, fun f => hcost f trivial, hbound⟩

end
end EconCSLib.OpenProblem.New.EconCSBench.QueryComplexityOfTarski

end


section

/-!
## Finite unrolling of terminating transcript strategies

The strategy only sees its transcript. Local computation is uncharged; no effective
procedure for finding the common halting bound is asserted.
-/

namespace EconCSLib.OpenProblem.New.EconCSBench.QueryComplexityOfTarski

/-- A transcript records queried points and the replies actually received. -/
abbrev TarskiTranscript (N d : ℕ) := List (Grid N d × Grid N d)

/-- A next decision has no access to the hidden oracle beyond the transcript. -/
inductive TarskiNextDecision (N d : ℕ)
  | output (point : Grid N d)
  | query (point : Grid N d)

/-- A total next-decision strategy may make arbitrarily many oracle queries. -/
abbrev TarskiTranscriptStrategy (N d : ℕ) :=
  TarskiTranscript N d → TarskiNextDecision N d

/-- Finite execution of one fixed strategy against one fixed oracle. Each query is
charged, including repeated queries; stopping is free. -/
inductive TarskiTranscriptStrategy.Executes {N d : ℕ}
    (strategy : TarskiTranscriptStrategy N d) (f : Grid N d → Grid N d) :
    TarskiTranscript N d → Grid N d → ℕ → Prop
  | output {history point} (hdecision : strategy history = .output point) :
      Executes strategy f history point 0
  | query {history point result cost} (hdecision : strategy history = .query point)
      (hnext : Executes strategy f (history ++ [(point, f point)]) result cost) :
      Executes strategy f history result (cost + 1)

/-- A finite tree with at most `fuel` queries. At a cutoff query it returns the requested
point without issuing that query. No oracle table is supplied. -/
def TarskiTranscriptStrategy.unroll {N d : ℕ}
    (strategy : TarskiTranscriptStrategy N d) :
    ℕ → TarskiTranscript N d → TarskiQueryTree N d
  | 0, history =>
      match strategy history with
      | .output point => .output point
      | .query point => .output point
  | fuel + 1, history =>
      match strategy history with
      | .output point => .output point
      | .query point => .query point fun answer =>
          strategy.unroll fuel (history ++ [(point, answer)])

/-- An execution that fits inside the unrolling budget keeps both its result and its exact
query count. -/
theorem TarskiTranscriptStrategy.unroll_run_of_executes {N d : ℕ}
    {strategy : TarskiTranscriptStrategy N d} {f : Grid N d → Grid N d}
    {history : TarskiTranscript N d} {point : Grid N d} {cost : ℕ}
    (h : strategy.Executes f history point cost) :
    ∀ fuel, cost ≤ fuel → (strategy.unroll fuel history).run f = (point, cost) := by
  induction h with
  | output hdecision =>
      intro fuel _
      cases fuel <;> simp [unroll, hdecision, TarskiQueryTree.run]
  | @query history query result cost hdecision hnext ih =>
      intro fuel hcost
      cases fuel with
      | zero => omega
      | succ fuel =>
          have hle : cost ≤ fuel := by omega
          simp [unroll, hdecision, TarskiQueryTree.run, ih fuel hle]

/-- The execution relation is deterministic in both output and charged cost. -/
theorem TarskiTranscriptStrategy.executes_unique {N d : ℕ}
    {strategy : TarskiTranscriptStrategy N d} {f : Grid N d → Grid N d}
    {history : TarskiTranscript N d} {point point' : Grid N d} {cost cost' : ℕ}
    (h : strategy.Executes f history point cost)
    (h' : strategy.Executes f history point' cost') :
    point = point' ∧ cost = cost' := by
  have hrun := unroll_run_of_executes h (max cost cost') (le_max_left _ _)
  have hrun' := unroll_run_of_executes h' (max cost cost') (le_max_right _ _)
  exact Prod.mk.inj (hrun.symm.trans hrun')

/-- Halting is an execution property. -/
def TarskiTranscriptStrategy.TerminatesOn {N d : ℕ}
    (strategy : TarskiTranscriptStrategy N d) (promise : Set (Grid N d → Grid N d)) : Prop :=
  ∀ f ∈ promise, ∃ point cost, strategy.Executes f [] point cost

/-- Finitely many promised oracles give one common finite unrolling depth. The tree is
chosen before the oracle; no correctness outside the promise is asserted. -/
theorem TarskiTranscriptStrategy.exists_unroll_on_finite_promise {N d : ℕ}
    (strategy : TarskiTranscriptStrategy N d)
    (promise : Finset (Grid N d → Grid N d))
    (hhalt : strategy.TerminatesOn (promise : Set (Grid N d → Grid N d))) :
    ∃ fuel, ∀ f ∈ promise, ∀ point cost,
      strategy.Executes f [] point cost →
        (strategy.unroll fuel []).run f = (point, cost) := by
  classical
  have hchoices : ∀ f : {f // f ∈ promise},
      ∃ point cost, strategy.Executes f.val [] point cost :=
    fun f => hhalt f.val f.property
  choose point cost hrun using hchoices
  let fuel := Finset.univ.sup cost
  refine ⟨fuel, ?_⟩
  intro f hf result count h
  let promised : {f // f ∈ promise} := ⟨f, hf⟩
  have hle : cost promised ≤ fuel :=
    Finset.le_sup (f := cost) (Finset.mem_univ promised)
  have heq := executes_unique (hrun promised) h
  exact unroll_run_of_executes h fuel (heq.2 ▸ hle)

/-- One finite tree preserves every halting result and exact query count on a finite
promise domain; it need not preserve behavior elsewhere. -/
theorem TarskiTranscriptStrategy.exists_tree_on_finite_promise {N d : ℕ}
    (strategy : TarskiTranscriptStrategy N d)
    (promise : Finset (Grid N d → Grid N d))
    (hhalt : strategy.TerminatesOn (promise : Set (Grid N d → Grid N d))) :
    ∃ tree : TarskiQueryTree N d, ∀ f ∈ promise,
      ∀ point cost, strategy.Executes f [] point cost → tree.run f = (point, cost) := by
  obtain ⟨fuel, hfuel⟩ := strategy.exists_unroll_on_finite_promise promise hhalt
  exact ⟨strategy.unroll fuel [], hfuel⟩

/-- The cutoff is a structural bound on every oracle branch, including branches outside
the promise. -/
theorem TarskiTranscriptStrategy.unroll_cost_le {N d : ℕ}
    (strategy : TarskiTranscriptStrategy N d) (fuel : ℕ)
    (history : TarskiTranscript N d) (f : Grid N d → Grid N d) :
    ((strategy.unroll fuel history).run f).2 ≤ fuel := by
  induction fuel generalizing history with
  | zero =>
      cases h : strategy history <;> simp [unroll, h, TarskiQueryTree.run]
  | succ fuel ih =>
      cases h : strategy history with
      | output point => simp [unroll, h, TarskiQueryTree.run]
      | query point =>
          simpa [unroll, h, TarskiQueryTree.run] using
            Nat.add_le_add_right (ih (history ++ [(point, f point)])) 1

/-- Set-indexed version of the finite-promise bridge. -/
theorem TarskiTranscriptStrategy.exists_tree_on_finite_set {N d : ℕ}
    (strategy : TarskiTranscriptStrategy N d)
    (promise : Set (Grid N d → Grid N d)) (hfinite : promise.Finite)
    (hhalt : strategy.TerminatesOn promise) :
    ∃ tree : TarskiQueryTree N d, ∀ f ∈ promise,
      ∀ point cost, strategy.Executes f [] point cost → tree.run f = (point, cost) := by
  classical
  have hhalt' : strategy.TerminatesOn (hfinite.toFinset : Set (Grid N d → Grid N d)) := by
    simpa only [hfinite.coe_toFinset] using hhalt
  obtain ⟨tree, htree⟩ := strategy.exists_tree_on_finite_promise hfinite.toFinset hhalt'
  refine ⟨tree, ?_⟩
  intro f hf point cost hrun
  exact htree f (hfinite.mem_toFinset.mpr hf) point cost hrun

/-- On a finite grid, every oracle promise domain is automatically finite. -/
theorem TarskiTranscriptStrategy.exists_tree_on_promise {N d : ℕ}
    (strategy : TarskiTranscriptStrategy N d)
    (promise : Set (Grid N d → Grid N d))
    (hhalt : strategy.TerminatesOn promise) :
    ∃ tree : TarskiQueryTree N d, ∀ f ∈ promise,
      ∀ point cost, strategy.Executes f [] point cost → tree.run f = (point, cost) :=
  strategy.exists_tree_on_finite_set promise (Set.toFinite promise) hhalt

/-- In particular, termination on monotone oracles suffices; no behavior on nonmonotone
oracles is assumed or preserved. -/
theorem TarskiTranscriptStrategy.exists_tree_on_monotone_oracles {N d : ℕ}
    (strategy : TarskiTranscriptStrategy N d)
    (hhalt : ∀ f, IsGridMonotone f →
      ∃ point cost, strategy.Executes f [] point cost) :
    ∃ tree : TarskiQueryTree N d, ∀ f, IsGridMonotone f →
      ∀ point cost, strategy.Executes f [] point cost → tree.run f = (point, cost) :=
  strategy.exists_tree_on_promise {f | IsGridMonotone f} hhalt

/-- The choice can be made once per seed, still before the hidden oracle. This is
pointwise in the seed, with no measurability or probability assertion. -/
theorem TarskiTranscriptStrategy.exists_tree_family_on_promise
    {N d : ℕ} {Seed : Type*} (strategy : Seed → TarskiTranscriptStrategy N d)
    (promise : Set (Grid N d → Grid N d))
    (hhalt : ∀ seed, (strategy seed).TerminatesOn promise) :
    ∃ program : Seed → TarskiQueryTree N d, ∀ seed f, f ∈ promise →
      ∀ point cost, (strategy seed).Executes f [] point cost →
        (program seed).run f = (point, cost) := by
  classical
  have h := fun seed => (strategy seed).exists_tree_on_promise promise (hhalt seed)
  choose program hprogram using h
  exact ⟨program, hprogram⟩

end EconCSLib.OpenProblem.New.EconCSBench.QueryComplexityOfTarski

end


section

/-!
## Almost-surely terminating abstract query strategies

The next-decision function is total and sees only its transcript. It may make
unboundedly many queries. Almost-sure finite executions with measurable output and
count observables admit the existing finite-lottery query model on a fixed promise
domain. No completeness of the seed measure is assumed.
-/

namespace EconCSLib.OpenProblem.New.EconCSBench.QueryComplexityOfTarski

open MeasureTheory
open scoped BigOperators

noncomputable section

/-- A measurable full-measure subset of the common halting seeds permits finite tree
selection. Observable maps remain measurable even if the tree selection itself has no
specified measurable space. The fallback handles exceptional seeds. -/
theorem exists_measurable_tree_family_of_ae_executes {N d : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] (P : (Grid N d → Grid N d) → Prop)
    (μ : Measure Seed) (fallback : Grid N d)
    (strategy : Seed → TarskiTranscriptStrategy N d)
    (result : (Grid N d → Grid N d) → Seed → Grid N d × ℕ)
    (hmeas : ∀ f, P f → Measurable (result f))
    (hexec : ∀ f, P f → ∀ᵐ seed ∂μ,
      (strategy seed).Executes f [] (result f seed).1 (result f seed).2) :
    ∃ program : Seed → TarskiQueryTree N d,
      (∀ f, P f → Measurable (fun seed => (program seed).run f)) ∧
      ∀ f, P f → (fun seed => (program seed).run f) =ᵐ[μ] result f := by
  classical
  have hgood : ∀ᵐ seed ∂μ, ∀ f : {f : Grid N d → Grid N d // P f},
      (strategy seed).Executes f.val [] (result f.val seed).1 (result f.val seed).2 :=
    ae_all_iff.mpr (fun f => hexec f.val f.property)
  obtain ⟨good, hgood_ae, hgood_meas, hgood_run⟩ := hgood.exists_measurable_mem
  have hchoose : ∀ seed : good, ∃ tree : TarskiQueryTree N d,
      ∀ f, P f → tree.run f = result f seed.val := by
    intro seed
    have hhalt : (strategy seed.val).TerminatesOn {f | P f} := by
      intro f hf
      exact ⟨(result f seed.val).1, (result f seed.val).2,
        hgood_run seed.val seed.property ⟨f, hf⟩⟩
    obtain ⟨tree, htree⟩ :=
      (strategy seed.val).exists_tree_on_promise {f | P f} hhalt
    refine ⟨tree, ?_⟩
    intro f hf
    exact htree f hf _ _ (hgood_run seed.val seed.property ⟨f, hf⟩)
  choose chosen hchosen using hchoose
  let program : Seed → TarskiQueryTree N d := fun seed =>
    if hseed : seed ∈ good then chosen ⟨seed, hseed⟩ else .output fallback
  have hon (seed : Seed) (hseed : seed ∈ good) (f : Grid N d → Grid N d)
      (hf : P f) : (program seed).run f = result f seed := by
    simpa only [program, dif_pos hseed] using hchosen ⟨seed, hseed⟩ f hf
  refine ⟨program, ?_, ?_⟩
  · intro f hf
    have heq : (fun seed => (program seed).run f) =
        fun seed => if seed ∈ good then result f seed else (fallback, 0) := by
      funext seed
      by_cases hseed : seed ∈ good
      · simpa only [if_pos hseed] using hon seed hseed f hf
      · simp only [program, dif_neg hseed, if_neg hseed, TarskiQueryTree.run]
    rw [heq]
    exact Measurable.ite hgood_meas (hmeas f hf) measurable_const
  · intro f hf
    filter_upwards [hgood_ae] with seed hseed
    exact hon seed hseed f hf

/-- Almost-sure finite executions of total transcript strategies compress to a finite
lottery. On promised oracles it has the same output law and no larger finite expected
query cost. Every component has a uniform grid-cardinality cap. -/
theorem exists_finite_lottery_of_ae_terminating_strategies {N d : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] (P : (Grid N d → Grid N d) → Prop)
    (μ : Measure Seed) [IsProbabilityMeasure μ] (fallback : Grid N d)
    (strategy : Seed → TarskiTranscriptStrategy N d)
    (result : (Grid N d → Grid N d) → Seed → Grid N d × ℕ)
    (hmeas : ∀ f, P f → Measurable (result f))
    (hexec : ∀ f, P f → ∀ᵐ seed ∂μ,
      (strategy seed).Executes f [] (result f seed).1 (result f seed).2) :
    ∃ seeds : ℕ, ∃ A : RandomizedTarskiQueryAlgorithm N d seeds,
      (∀ (f : Grid N d → Grid N d), P f → ∀ g : Grid N d → ℝ,
        ∑ seed, A.seedDist.val seed * g ((A.program seed).run f).1 =
          ∫ seed, g (result f seed).1 ∂μ) ∧
      (∀ f : Grid N d → Grid N d, P f →
        Integrable (fun seed => ((result f seed).2 : ℝ)) μ →
          A.expectedQueryCount f ≤ ∫ seed, ((result f seed).2 : ℝ) ∂μ) ∧
      ∀ seed f, ((A.program seed).run f).2 ≤ Fintype.card (Grid N d) := by
  obtain ⟨program, hprogram_meas, hprogram_eq⟩ :=
    exists_measurable_tree_family_of_ae_executes P μ fallback strategy result hmeas hexec
  obtain ⟨seeds, A, hout, hcost, hbound⟩ :=
    exists_finite_lottery_of_promised_measurable_seed_family P μ program hprogram_meas
  refine ⟨seeds, A, ?_, ?_, hbound⟩
  · intro f hf g
    refine (hout f hf g).trans (integral_congr_ae ?_)
    filter_upwards [hprogram_eq f hf] with seed heq
    exact congrArg (fun p : Grid N d × ℕ => g p.1) heq
  · intro f hf hfinite
    have heq : (fun seed => (((program seed).run f).2 : ℝ)) =ᵐ[μ]
        (fun seed => ((result f seed).2 : ℝ)) := by
      filter_upwards [hprogram_eq f hf] with seed heq
      exact congrArg (fun p : Grid N d × ℕ => (p.2 : ℝ)) heq
    calc
      A.expectedQueryCount f ≤ ∫ seed, (((program seed).run f).2 : ℝ) ∂μ :=
        hcost f hf (hfinite.congr heq.symm)
      _ = ∫ seed, ((result f seed).2 : ℝ) ∂μ := integral_congr_ae heq

end
end EconCSLib.OpenProblem.New.EconCSBench.QueryComplexityOfTarski

end


section

/-!
## Tarski query-complexity questions

Bounds take side length `N` before dimension `d`; the asymptotic domain is `N ≥ 2, d ≥
1`. Fixed-dimension polylogarithmic bounds with a dimension-dependent exponent are
already known. The barrier-breaking target instead chooses one exponent before every
dimension, while coefficients and thresholds may depend on dimension
[Chen–Li–Yannakakis 2026, §9].

Upper- and lower-bound directions are separate.
-/

namespace EconCSLib.OpenProblem.New.EconCSBench.QueryComplexityOfTarski

/-- A candidate upper bound; satisfying it need not improve the known bounds. -/
def QueryUpperBoundQuestion (model : QueryModel) (bound : ℕ → ℕ → ℝ) : Prop :=
  ∀ N d : ℕ, 2 ≤ N → 1 ≤ d → HasQueryUpperBound model N d (bound N d)

/-- A candidate lower bound, without requiring every improvement to reach `log^{Ω(d)} N`. -/
def QueryLowerBoundQuestion (model : QueryModel) (bound : ℕ → ℕ → ℝ) : Prop :=
  ∀ N d : ℕ, 2 ≤ N → 1 ≤ d → HasQueryLowerBound model N d (bound N d)

/-- The weaker fixed-dimension reading, already attained by known bounds and not itself a
barrier-breaking target. -/
def FixedDimensionPolylogUpperBoundStatement (model : QueryModel) : Prop :=
  ∀ d : ℕ, 1 ≤ d → ∃ exponent : ℕ, 0 < exponent ∧
    HasFixedDimensionPolylogUpperBound model d exponent

/-- The `log^{O(d)} N` upper side in the fixed-dimension regime. -/
def ExponentialInDimensionLogUpperBoundStatement (model : QueryModel) : Prop :=
  ∃ slope : ℕ, 0 < slope ∧
    ∀ d : ℕ, 1 ≤ d → HasFixedDimensionPolylogUpperBound model d (slope * d + slope)

/-- The combined `log^{Θ(d)} N` question in one fixed query model. The separate directions
above remain independently meaningful research targets. -/
def TarskiQueryComplexityStatement (model : QueryModel) : Prop :=
  ExponentialInDimensionLogLowerBoundStatement model ∧
    ExponentialInDimensionLogUpperBoundStatement model

end EconCSLib.OpenProblem.New.EconCSBench.QueryComplexityOfTarski

end
