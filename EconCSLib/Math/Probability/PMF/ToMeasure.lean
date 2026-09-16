/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.Probability.ProbabilityMassFunction.Monad

/-!
# Probability mass functions as measures

Exact compatibility results between the discrete `PMF` monad and the
measure-theoretic Giry monad.

## Main result

* `PMF.toMeasure_bind_eq_bind_toMeasure` — converting a PMF bind to a measure
  is exactly measure bind of the converted PMFs.

The theorem does not assume that the source type is countable.  Its proof
restricts integration to the countable support of the particular PMF.
-/

open MeasureTheory

namespace PMF

universe uα uβ

/-- `PMF.toMeasure` preserves monadic bind exactly.

Only measurable singletons on the source are needed; the carrier itself may
be uncountable because each PMF has countable support. -/
theorem toMeasure_bind_eq_bind_toMeasure
    {α : Type uα} {β : Type uβ}
    [MeasurableSpace α] [MeasurableSingletonClass α]
    [MeasurableSpace β]
    (p : PMF α) (f : α → PMF β)
    (hf : AEMeasurable (fun a => (f a).toMeasure) p.toMeasure) :
    (p.bind f).toMeasure =
      p.toMeasure.bind (fun a => (f a).toMeasure) := by
  ext s hs
  rw [Measure.bind_apply hs hf,
    PMF.toMeasure_bind_apply p f s hs]
  rw [← p.restrict_toMeasure_support]
  rw [lintegral_countable _ p.support_countable]
  symm
  calc
    ∑' a : p.support,
        (f a).toMeasure s * p.toMeasure ({(a : α)} : Set α) =
        ∑' a : p.support, p a * (f a).toMeasure s := by
      apply tsum_congr
      intro a
      rw [p.toMeasure_apply_singleton a (measurableSet_singleton _)]
      exact mul_comm _ _
    _ = ∑' a, p a * (f a).toMeasure s := by
      exact
        tsum_subtype_eq_of_support_subset
          (f := fun a : α => p a * (f a).toMeasure s) (by
            intro a ha
            simp only [Function.mem_support] at ha
            intro hpa
            exact ha (by simp [hpa]))

end PMF
