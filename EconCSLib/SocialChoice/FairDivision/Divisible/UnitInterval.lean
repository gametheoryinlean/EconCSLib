/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.SocialChoice.FairDivision.Divisible.Instance
import Mathlib.Data.ENNReal.Real
import Mathlib.MeasureTheory.Constructions.UnitInterval
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.Typeclasses.NoAtoms
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.LeftRightLim
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Tactic.Linarith

/-!
# EconCSLib.SocialChoice.FairDivision.Divisible.UnitInterval

Shared measure-theoretic helpers for divisible allocation on intervals.

This file collects reusable facts that are needed by multiple cake-cutting proofs. It keeps
the algorithm files focused on their allocation arguments rather than duplicating basic
measure-continuity infrastructure.
-/

open MeasureTheory Set
open scoped unitInterval

namespace SocialChoice
namespace FairDivision
namespace Divisible

/-- Non-atomicity is preserved when a measure on the unit interval is pushed forward along
    the subtype inclusion into `ℝ`. -/
instance noAtomsMapSubtypeVal (μ : Measure I) [NoAtoms μ] :
    NoAtoms (μ.map Subtype.val) where
  measure_singleton x := by
    rw [Measure.map_apply measurable_subtype_coe (measurableSet_singleton x)]
    exact Set.Subsingleton.measure_zero
      (by
        intro y hy z hz
        exact Subtype.ext (by simpa using hy.trans hz.symm))
      μ

/-- The CDF `t ↦ (ν (Iic t)).toReal` is continuous for a non-atomic finite measure on `ℝ`. -/
lemma cdfRealContinuous (ν : Measure ℝ) [IsFiniteMeasure ν] [NoAtoms ν] :
    Continuous (fun t : ℝ => (ν (Set.Iic t)).toReal) := by
  have hf_mono : Monotone (fun t : ℝ => (ν (Set.Iic t)).toReal) := fun a b hab =>
    (ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).mpr
      (measure_mono (Set.Iic_subset_Iic.mpr hab))
  have hf_right : ∀ a : ℝ, ContinuousWithinAt (fun t => (ν (Set.Iic t)).toReal) (Set.Ioi a) a :=
    by
      intro a
      have htendsto : Filter.Tendsto (ν ∘ Set.Iic) (nhdsWithin a (Set.Ioi a))
          (nhds (ν (Set.Iic a))) := by
        have key := tendsto_measure_biInter_gt (μ := ν) (s := Set.Iic) (a := a)
          (fun _ _ => measurableSet_Iic.nullMeasurableSet)
          (fun _ _ _ h => Set.Iic_subset_Iic.mpr h)
          ⟨a + 1, by linarith, measure_ne_top _ _⟩
        have h_eq : (⋂ r > a, Set.Iic r) = Set.Iic a := by
          ext x; simp only [mem_iInter, mem_Iic, gt_iff_lt]
          constructor
          · intro h
            by_contra hxa; push_neg at hxa
            linarith [h ((a + x) / 2) (by linarith)]
          · intro h r hr; exact le_trans h hr.le
        rwa [h_eq] at key
      exact (ENNReal.continuousAt_toReal (measure_ne_top _ _)).tendsto.comp htendsto
  have hf_left : ∀ a : ℝ, ContinuousWithinAt (fun t => (ν (Set.Iic t)).toReal) (Set.Iio a) a :=
    by
      intro a
      rw [hf_mono.continuousWithinAt_Iio_iff_leftLim_eq]
      obtain ⟨u, hu_mono, hu_lt, hu_nhds⟩ := exists_seq_strictMono_tendsto_nhdsWithin a
      have hu_tendsto : Filter.Tendsto u Filter.atTop (nhds a) :=
        hu_nhds.mono_right nhdsWithin_le_nhds
      have h_union : ⋃ n : ℕ, Set.Iic (u n) = Set.Iio a :=
        iUnion_Iic_eq_Iio_of_lt_of_tendsto hu_lt hu_tendsto
      have h_meas : Filter.Tendsto (fun n => ν (Set.Iic (u n))) Filter.atTop
          (nhds (ν (Set.Iio a))) := by
        have := tendsto_measure_iUnion_atTop (μ := ν)
          (fun m n hmn => Set.Iic_subset_Iic.mpr (hu_mono.monotone hmn))
        rwa [h_union] at this
      have h_leftLim : Function.leftLim (fun t => (ν (Set.Iic t)).toReal) a =
          (ν (Set.Iio a)).toReal :=
        tendsto_nhds_unique
          ((hf_mono.tendsto_leftLim a).comp hu_nhds)
          ((ENNReal.continuousAt_toReal (measure_ne_top _ _)).tendsto.comp h_meas)
      rw [h_leftLim, measure_congr Iio_ae_eq_Iic]
  exact continuous_iff_continuousAt.mpr fun a =>
    continuousAt_iff_continuous_left'_right'.mpr ⟨hf_left a, hf_right a⟩

end Divisible
end FairDivision
end SocialChoice
