/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# EconCSLib.Math.Probability.PMF.ConditionalSampling

Discrete conditional sampling for arbitrary probability mass functions.

`PMF.conditionOnFiber p f value` is the posterior law of a sample from `p`
after observing `f sample = value`.  It is normalized on positive fibers and
uses `p` itself as an irrelevant fallback on zero-mass fibers.  The main
disintegration theorem says that sampling `value` from the marginal and then
sampling from this posterior gives exactly the joint law obtained by sampling
the original value once.

The construction imposes no finiteness assumption on either type.  It is the
probability-theoretic core of mixed-to-behavioral realization: a complete
contingent plan may be sampled in advance or exposed one conditional
coordinate at a time.
-/

namespace PMF

universe uα uβ uγ

variable {α : Type uα} {β : Type uβ}

/-- Conditioning on the whole sample space leaves a probability mass
function unchanged. -/
theorem filter_univ
    (p : PMF α)
    (hpositive :
      ∃ value ∈ (Set.univ : Set α),
        value ∈ p.support) :
    p.filter Set.univ hpositive = p := by
  ext value
  simp [PMF.filter_apply, p.tsum_coe]

/-- The fiber of `f` over one observed value. -/
def fiberSet (f : α → β) (value : β) :
    Set α :=
  {sample | f sample = value}

/-- The observed fiber has positive mass under `p`. -/
def FiberPossible
    (p : PMF α) (f : α → β) (value : β) : Prop :=
  ∃ sample ∈ fiberSet f value,
    sample ∈ p.support

/-- A fiber is possible exactly when its value lies in the support of the
pushforward marginal. -/
theorem fiberPossible_iff_mem_support_map
    (p : PMF α) (f : α → β) (value : β) :
    p.FiberPossible f value ↔
      value ∈ (p.map f).support := by
  constructor
  · rintro ⟨sample, hfiber, hsupported⟩
    exact
      (PMF.mem_support_map_iff
        f p value).mpr
          ⟨sample, hsupported, hfiber⟩
  · intro hsupported
    obtain ⟨sample, hsample, hvalue⟩ :=
      (PMF.mem_support_map_iff
        f p value).mp hsupported
    exact
      ⟨sample, hvalue, hsample⟩

/-- Posterior sample law after observing one value of `f`.

The fallback on an impossible fiber is never selected with positive
probability by the marginal `p.map f`, but makes the kernel total. -/
noncomputable def conditionOnFiber
    (p : PMF α) (f : α → β) (value : β) :
    PMF α := by
  classical
  exact
    if hpossible : p.FiberPossible f value then
      p.filter (fiberSet f value) hpossible
    else
      p

/-- The mass of a fiber is exactly the corresponding pushforward point
mass. -/
theorem tsum_fiberSet_indicator
    (p : PMF α) (f : α → β) (value : β) :
    (∑' sample,
      (fiberSet f value).indicator p sample) =
      p.map f value := by
  rw [PMF.map_apply]
  apply tsum_congr
  intro sample
  by_cases heq : f sample = value
  · simp [fiberSet, heq]
  · have hne : value ≠ f sample :=
      fun h => heq h.symm
    simp [fiberSet, heq, hne]

/-- Point-mass formula for a positive-fiber posterior. -/
theorem conditionOnFiber_apply_of_possible
    (p : PMF α) (f : α → β) (value : β)
    (hpossible : p.FiberPossible f value)
    (sample : α) :
    p.conditionOnFiber f value sample =
      (fiberSet f value).indicator p sample *
        (p.map f value)⁻¹ := by
  classical
  rw [conditionOnFiber, dif_pos hpossible,
    PMF.filter_apply]
  rw [p.tsum_fiberSet_indicator f value]

/-- On a zero-mass fiber, the total posterior kernel is the declared
fallback. -/
theorem conditionOnFiber_of_impossible
    (p : PMF α) (f : α → β) (value : β)
    (himpossible : ¬ p.FiberPossible f value) :
    p.conditionOnFiber f value = p := by
  classical
  simp [conditionOnFiber, himpossible]

/-- Mapping along an injective function preserves the point mass at every
image point. -/
theorem map_apply_of_injective
    (p : PMF α) (f : α → β)
    (hinjective : Function.Injective f)
    (sample : α) :
    p.map f (f sample) = p sample := by
  rw [PMF.map_apply, tsum_eq_single sample]
  · simp
  · intro other hne
    have himage : f sample ≠ f other :=
      fun heq => hne (hinjective heq).symm
    simp [himage]

/-- Discrete disintegration: first sample the observable marginal and then
sample from the corresponding posterior fiber.  The resulting joint law is
exactly the joint pushforward of the original sample.

Impossible fiber values use the total fallback in `conditionOnFiber`, but
their outer marginal mass is zero. -/
theorem bind_conditionOnFiber_map_pair
    (p : PMF α) (f : α → β) :
    (p.map f).bind
        (fun value =>
          (p.conditionOnFiber f value).map
            (fun sample => (value, sample))) =
      p.map (fun sample => (f sample, sample)) := by
  classical
  ext outcome
  obtain ⟨value, sample⟩ := outcome
  rw [PMF.bind_apply, tsum_eq_single value]
  · have hposteriorMap :
        ((p.conditionOnFiber f value).map
          (fun candidate => (value, candidate)))
            (value, sample) =
          p.conditionOnFiber f value sample := by
        apply
          PMF.map_apply_of_injective
            (p.conditionOnFiber f value)
            (fun candidate => (value, candidate))
        intro first second heq
        exact congrArg Prod.snd heq
    rw [hposteriorMap]
    have hjoint :
          p.map (fun candidate =>
              (f candidate, candidate))
              (value, sample) =
            if value = f sample then
              p sample
            else
              0 := by
        rw [PMF.map_apply, tsum_eq_single sample]
        · simp
        · intro other hne
          have hpair :
              (value, sample) ≠
                (f other, other) := by
            intro heq
            exact hne (congrArg Prod.snd heq).symm
          simp [hpair]
    rw [hjoint]
    by_cases hpossible :
          p.FiberPossible f value
    · rw [p.conditionOnFiber_apply_of_possible
        f value hpossible sample]
      by_cases heq : f sample = value
      · have hmarginal :
              p.map f value ≠ 0 := by
            exact
              (p.map f).mem_support_iff
                value |>.mpr
                  ((p.fiberPossible_iff_mem_support_map
                    f value).mp hpossible)
        calc
          p.map f value *
                ((fiberSet f value).indicator
                    p sample *
                  (p.map f value)⁻¹) =
              p sample *
                (p.map f value *
                  (p.map f value)⁻¹) := by
              have hmem :
                  sample ∈ fiberSet f value :=
                heq
              rw [Set.indicator_of_mem hmem]
              ac_rfl
          _ = p sample * 1 := by
            rw [ENNReal.mul_inv_cancel
              hmarginal
              ((p.map f).apply_ne_top value)]
          _ = if value = f sample then
                p sample
              else 0 := by
            simp [heq]
      · have hne : value ≠ f sample :=
          fun h => heq h.symm
        simp [fiberSet, heq, hne]
    · have hmarginal :
            p.map f value = 0 := by
          rw [(p.map f).apply_eq_zero_iff]
          exact
            fun hsupport =>
              hpossible
                ((p.fiberPossible_iff_mem_support_map
                  f value).mpr hsupport)
      rw [hmarginal]
      by_cases heq : value = f sample
      · have hsample : p sample = 0 := by
          by_contra hnonzero
          apply hpossible
          exact
            ⟨sample,
              by simp [fiberSet, heq.symm],
              (p.mem_support_iff sample).mpr
                hnonzero⟩
        simp [heq, hsample]
      · simp [heq]
  · intro other hne
    have hmapZero :
        ((p.conditionOnFiber f other).map
          (fun candidate => (other, candidate)))
            (value, sample) =
          0 := by
      rw [PMF.map_apply, ENNReal.tsum_eq_zero]
      intro candidate
      have hpair :
          (value, sample) ≠
            (other, candidate) := by
        intro heq
        exact hne (congrArg Prod.fst heq).symm
      simp [hpair]
    simp [hmapZero]

/-- Continuation form of discrete disintegration.

An arbitrary continuation may use both the observed value and the posterior
sample.  Exposing the observation first and then drawing from the posterior is
exactly equivalent to drawing the original sample once. -/
theorem bind_map_bind_conditionOnFiber
    {γ : Type uγ}
    (p : PMF α) (f : α → β)
    (continuation : β → α → PMF γ) :
    (p.map f).bind
        (fun value =>
          (p.conditionOnFiber f value).bind
            (continuation value)) =
      p.bind
        (fun sample =>
          continuation (f sample) sample) := by
  let jointContinuation :
      β × α → PMF γ :=
    fun outcome =>
      continuation outcome.1 outcome.2
  calc
    (p.map f).bind
        (fun value =>
          (p.conditionOnFiber f value).bind
            (continuation value)) =
      (p.map f).bind
        (fun value =>
          ((p.conditionOnFiber f value).map
            (fun sample => (value, sample))).bind
              jointContinuation) := by
        apply congrArg
          (fun next =>
            (p.map f).bind next)
        funext value
        rw [PMF.bind_map]
        rfl
    _ = ((p.map f).bind
          (fun value =>
            (p.conditionOnFiber f value).map
              (fun sample => (value, sample)))).bind
            jointContinuation := by
      rw [PMF.bind_bind]
    _ = (p.map
          (fun sample =>
            (f sample, sample))).bind
            jointContinuation := by
      rw [p.bind_conditionOnFiber_map_pair f]
    _ = p.bind
          (fun sample =>
            continuation (f sample) sample) := by
      rw [PMF.bind_map]
      rfl

end PMF
