/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Execution.Discrete.CertifiedPathApproximation
import Mathlib.GroupTheory.ArchimedeanDensely

/-!
# Effective discounted path utilities

This module gives a measure-free algorithm for discounted utilities of
coherent effective path laws.  A utility supplies an executable rational
reward at every absolute time and state or action-recording event, a
nonnegative rational discount `γ < 1`, and a uniform nonnegative rational
reward bound `B`.

At horizon `H`, the algorithm evaluates exactly the first `H` rewards at
offsets `0, ..., H - 1` from the supplied absolute `start`.  Its declared
geometric tail radius is

`B * γ ^ H / (1 - γ)`.

The resulting state and event objects are ordinary
`PrefixApproximationScheme`s, so the exact centers, rational intervals, and
budgeted or least-horizon searches from `CertifiedPathApproximation` apply
directly.  The radius is proved to vanish for every `γ < 1` and therefore
supplies a finite acceptable horizon for every positive rational tolerance.

The stored per-period bound explains the geometric schedule but this pure
layer deliberately does not assert that a particular infinite-path integral
lies in one of its intervals.  Such a conclusion requires a separate
semantic certificate identifying the infinite discounted series and proving
the finite-prefix error estimate.

For a supplied horizon law, evaluating one center is linear in both `H` and
the law's weighted occurrence list.  Producing that law can still grow
exponentially with horizon and branching degree.  Radius search itself uses
only exact rational arithmetic and performs at most the supplied number of
comparisons.

## Main definitions and results

* `DiscountedPathUtility.geometricTailRadius` and its vanishing proof;
* `StateDiscountedPathUtility` and `EventDiscountedPathUtility`;
* exact finite discounted observables and centers at offsets `0, ..., H - 1`;
* direct conversion to the A15 prefix-approximation schemes;
* state-to-event projection and policy-execution correctness.
-/

namespace KernelArena

universe uS uA

namespace DiscountedPathUtility

/-- Executable geometric tail schedule `B * γ^H / (1 - γ)`.  Its convergence
meaning is established below from `γ < 1`; target-error meaning still needs a
separate semantic discounted-series certificate. -/
def geometricTailRadius (discount bound : ℚ≥0) : ApproximationRadius :=
  fun horizon => bound * discount ^ horizon / (1 - discount)

@[simp]
theorem geometricTailRadius_apply (discount bound : ℚ≥0) (horizon : ℕ) :
    geometricTailRadius discount bound horizon =
      bound * discount ^ horizon / (1 - discount) :=
  rfl

/-- The denominator of the geometric tail is positive at every admitted
discount. -/
theorem one_sub_discount_pos {discount : ℚ≥0}
    (hdiscount : discount < 1) : 0 < 1 - discount := by
  change (0 : ℚ) < ((1 - discount : ℚ≥0) : ℚ)
  rw [NNRat.coe_sub (le_of_lt hdiscount)]
  exact sub_pos.mpr (show (discount : ℚ) < 1 from hdiscount)

/-- The geometric tail schedule vanishes at every rational discount below
one.  The proof is Archimedean and supplies no oracle for an external target
expectation. -/
theorem geometricTailRadius_vanishes
    {discount bound : ℚ≥0} (hdiscount : discount < 1) :
    (geometricTailRadius discount bound).Vanishes := by
  intro tolerance htolerance
  by_cases hbound : bound = 0
  · refine ⟨0, ?_⟩
    intro horizon _
    simp [geometricTailRadius, hbound]
  · have hboundPos : 0 < bound := pos_iff_ne_zero.mpr hbound
    have hdenominator : 0 < 1 - discount :=
      one_sub_discount_pos hdiscount
    let threshold : ℚ≥0 := tolerance * (1 - discount) / bound
    have hthreshold : 0 < threshold := by
      dsimp only [threshold]
      exact div_pos (mul_pos htolerance hdenominator) hboundPos
    obtain ⟨cutoff, hcutoff⟩ :=
      exists_pow_lt₀ hdiscount (Units.mk0 threshold hthreshold.ne')
    refine ⟨cutoff, ?_⟩
    intro horizon hcutoffHorizon
    have hpower : discount ^ horizon ≤ discount ^ cutoff :=
      pow_le_pow_of_le_one (show 0 ≤ discount from bot_le)
        (le_of_lt hdiscount) hcutoffHorizon
    apply LT.lt.le
    apply (div_lt_iff₀ hdenominator).2
    calc
      bound * discount ^ horizon ≤ bound * discount ^ cutoff :=
        mul_le_mul_of_nonneg_left hpower (show 0 ≤ bound from bot_le)
      _ < bound * threshold :=
        mul_lt_mul_of_pos_left hcutoff hboundPos
      _ = tolerance * (1 - discount) := by
        dsimp only [threshold]
        exact mul_div_cancel₀ (tolerance * (1 - discount)) hbound

/-- An explicit finite coordinate for offset `0 ≤ offset < horizon`, measured
from the absolute start. -/
def coordinate (start horizon : ℕ) (offset : Fin horizon) :
    Fin (start + horizon + 1) :=
  ⟨start + offset, by omega⟩

@[simp]
theorem coordinate_val (start horizon : ℕ) (offset : Fin horizon) :
    (coordinate start horizon offset).val = start + offset.val :=
  rfl

end DiscountedPathUtility

/-- Executable discounted state reward with a uniform per-period bound. -/
structure StateDiscountedPathUtility (A : KernelArena) where
  /-- Rational reward at an absolute time and state. -/
  reward : ℕ → A.State → ℚ
  /-- Nonnegative rational discount. -/
  discount : ℚ≥0
  /-- Strict discount needed for a finite geometric tail. -/
  discount_lt_one : discount < 1
  /-- Uniform nonnegative rational absolute reward bound. -/
  bound : ℚ≥0
  /-- Every executable one-period reward obeys the supplied bound. -/
  reward_abs_le : ∀ time state, |reward time state| ≤ (bound : ℚ)

/-- Executable discounted action-recording event reward with a uniform
per-period bound. -/
structure EventDiscountedPathUtility (A : KernelArena) where
  /-- Rational reward at an absolute time and complete path event. -/
  reward : ℕ → A.PathEvent → ℚ
  /-- Nonnegative rational discount. -/
  discount : ℚ≥0
  /-- Strict discount needed for a finite geometric tail. -/
  discount_lt_one : discount < 1
  /-- Uniform nonnegative rational absolute reward bound. -/
  bound : ℚ≥0
  /-- Every executable one-period reward obeys the supplied bound. -/
  reward_abs_le : ∀ time event, |reward time event| ≤ (bound : ℚ)

namespace StateDiscountedPathUtility

variable {A : KernelArena}

variable (utility : StateDiscountedPathUtility A)

/-- Exact first `horizon` discounted state rewards from absolute `start`.
Offsets are precisely `0, ..., horizon - 1`; horizon zero is the empty sum. -/
def finiteObservable
    (start horizon : ℕ) (history : A.StatePrefix (start + horizon)) : ℚ :=
  ∑ offset : Fin horizon,
    (utility.discount : ℚ) ^ offset.val *
      utility.reward (start + offset.val)
        (history (DiscountedPathUtility.coordinate start horizon offset))

@[simp]
theorem finiteObservable_zero
    (start : ℕ) (history : A.StatePrefix (start + 0)) :
    utility.finiteObservable start 0 history = 0 := by
  simp [finiteObservable]

/-- The utility's executable geometric tail schedule. -/
def tailRadius :
    ApproximationRadius :=
  DiscountedPathUtility.geometricTailRadius utility.discount utility.bound

@[simp]
theorem tailRadius_apply
    (horizon : ℕ) :
    utility.tailRadius horizon =
      utility.bound * utility.discount ^ horizon / (1 - utility.discount) :=
  rfl

/-- The state discounted utility as an A15 approximation scheme. -/
def approximationScheme
    (start : ℕ) : StatePrefixApproximationScheme A start where
  observable := utility.finiteObservable start
  radius := utility.tailRadius

/-- Exact rational finite-horizon center under a coherent effective state
path law. -/
def center {start : ℕ} {initialPrefix : A.StatePrefix start}
    (utility : StateDiscountedPathUtility A)
    (law : StateEffectivePathLawFrom A start initialPrefix)
    (horizon : ℕ) : ℚ :=
  (utility.approximationScheme start).center law horizon

/-- Exact finite-horizon center paired with the geometric scheme radius. -/
def estimate {start : ℕ} {initialPrefix : A.StatePrefix start}
    (utility : StateDiscountedPathUtility A)
    (law : StateEffectivePathLawFrom A start initialPrefix)
    (horizon : ℕ) : RationalSchemeEstimate :=
  (utility.approximationScheme start).estimate law horizon

/-- Search a bounded number of horizons and evaluate the first state estimate
whose geometric radius meets the tolerance. -/
def search {start : ℕ} {initialPrefix : A.StatePrefix start}
    (utility : StateDiscountedPathUtility A)
    (law : StateEffectivePathLawFrom A start initialPrefix)
    (tolerance : ℚ≥0) (budget : ℕ) :
    Option (ℕ × RationalSchemeEstimate) :=
  (utility.approximationScheme start).search law tolerance budget

/-- Unfolding the state center exposes the exact `FiniteLaw.expectRat` query
of the first `H` discounted rewards. -/
theorem center_eq_expectedPrefixValue
    {start : ℕ} {initialPrefix : A.StatePrefix start}
    (utility : StateDiscountedPathUtility A)
    (law : StateEffectivePathLawFrom A start initialPrefix)
    (horizon : ℕ) :
    utility.center law horizon =
      law.expectedPrefixValue horizon
        (utility.finiteObservable start horizon) :=
  rfl

/-- The declared state radius vanishes at every valid discount. -/
theorem tailRadius_vanishes :
    utility.tailRadius.Vanishes :=
  DiscountedPathUtility.geometricTailRadius_vanishes
    utility.discount_lt_one

/-- Every positive tolerance admits a finite state horizon whose geometric
radius meets it. -/
theorem exists_tailRadius_le
    (tolerance : ℚ≥0) (htolerance : 0 < tolerance) :
    ∃ horizon, utility.tailRadius horizon ≤ tolerance :=
  utility.tailRadius_vanishes.exists_within tolerance htolerance

/-- Compute the least state horizon at which the geometric schedule meets a
positive tolerance. -/
def leastHorizon
    (start : ℕ) (tolerance : ℚ≥0) (htolerance : 0 < tolerance) : ℕ :=
  (utility.approximationScheme start).leastHorizon tolerance
    (utility.exists_tailRadius_le tolerance htolerance)

/-- The computed state horizon meets the tolerance and every earlier one
fails it. -/
theorem leastHorizon_spec
    (start : ℕ) (tolerance : ℚ≥0) (htolerance : 0 < tolerance) :
    utility.tailRadius (utility.leastHorizon start tolerance htolerance) ≤
        tolerance ∧
      ∀ earlier < utility.leastHorizon start tolerance htolerance,
        tolerance < utility.tailRadius earlier :=
  (utility.approximationScheme start).leastHorizon_spec tolerance
    (utility.exists_tailRadius_le tolerance htolerance)

/-- Forget action data in the reward input while retaining the exact state
coordinate and all discount data. -/
def toEvent :
    EventDiscountedPathUtility A where
  reward time event := utility.reward time event.state
  discount := utility.discount
  discount_lt_one := utility.discount_lt_one
  bound := utility.bound
  reward_abs_le time event := utility.reward_abs_le time event.state

end StateDiscountedPathUtility

namespace EventDiscountedPathUtility

variable {A : KernelArena}

variable (utility : EventDiscountedPathUtility A)

/-- Exact first `horizon` discounted action-recording event rewards from
absolute `start`.  Offsets are precisely `0, ..., horizon - 1`. -/
def finiteObservable
    (start horizon : ℕ) (history : A.EventPrefix (start + horizon)) : ℚ :=
  ∑ offset : Fin horizon,
    (utility.discount : ℚ) ^ offset.val *
      utility.reward (start + offset.val)
        (history (DiscountedPathUtility.coordinate start horizon offset))

@[simp]
theorem finiteObservable_zero
    (start : ℕ) (history : A.EventPrefix (start + 0)) :
    utility.finiteObservable start 0 history = 0 := by
  simp [finiteObservable]

/-- The event utility's executable geometric tail schedule. -/
def tailRadius :
    ApproximationRadius :=
  DiscountedPathUtility.geometricTailRadius utility.discount utility.bound

@[simp]
theorem tailRadius_apply
    (horizon : ℕ) :
    utility.tailRadius horizon =
      utility.bound * utility.discount ^ horizon / (1 - utility.discount) :=
  rfl

/-- The event discounted utility as an A15 approximation scheme. -/
def approximationScheme
    (start : ℕ) : EventPrefixApproximationScheme A start where
  observable := utility.finiteObservable start
  radius := utility.tailRadius

/-- Exact rational finite-horizon center under a coherent effective event
path law. -/
def center {start : ℕ} {initialPrefix : A.EventPrefix start}
    (utility : EventDiscountedPathUtility A)
    (law : EventEffectivePathLawFrom A start initialPrefix)
    (horizon : ℕ) : ℚ :=
  (utility.approximationScheme start).center law horizon

/-- Exact finite-horizon center paired with the geometric scheme radius. -/
def estimate {start : ℕ} {initialPrefix : A.EventPrefix start}
    (utility : EventDiscountedPathUtility A)
    (law : EventEffectivePathLawFrom A start initialPrefix)
    (horizon : ℕ) : RationalSchemeEstimate :=
  (utility.approximationScheme start).estimate law horizon

/-- Search a bounded number of horizons and evaluate the first event estimate
whose geometric radius meets the tolerance. -/
def search {start : ℕ} {initialPrefix : A.EventPrefix start}
    (utility : EventDiscountedPathUtility A)
    (law : EventEffectivePathLawFrom A start initialPrefix)
    (tolerance : ℚ≥0) (budget : ℕ) :
    Option (ℕ × RationalSchemeEstimate) :=
  (utility.approximationScheme start).search law tolerance budget

/-- Unfolding the event center exposes the exact `FiniteLaw.expectRat` query
of the first `H` discounted rewards. -/
theorem center_eq_expectedPrefixValue
    {start : ℕ} {initialPrefix : A.EventPrefix start}
    (utility : EventDiscountedPathUtility A)
    (law : EventEffectivePathLawFrom A start initialPrefix)
    (horizon : ℕ) :
    utility.center law horizon =
      law.expectedPrefixValue horizon
        (utility.finiteObservable start horizon) :=
  rfl

/-- The declared event radius vanishes at every valid discount. -/
theorem tailRadius_vanishes :
    utility.tailRadius.Vanishes :=
  DiscountedPathUtility.geometricTailRadius_vanishes
    utility.discount_lt_one

/-- Every positive tolerance admits a finite event horizon whose geometric
radius meets it. -/
theorem exists_tailRadius_le
    (tolerance : ℚ≥0) (htolerance : 0 < tolerance) :
    ∃ horizon, utility.tailRadius horizon ≤ tolerance :=
  utility.tailRadius_vanishes.exists_within tolerance htolerance

/-- Compute the least event horizon at which the geometric schedule meets a
positive tolerance. -/
def leastHorizon
    (start : ℕ) (tolerance : ℚ≥0) (htolerance : 0 < tolerance) : ℕ :=
  (utility.approximationScheme start).leastHorizon tolerance
    (utility.exists_tailRadius_le tolerance htolerance)

/-- The computed event horizon meets the tolerance and every earlier one
fails it. -/
theorem leastHorizon_spec
    (start : ℕ) (tolerance : ℚ≥0) (htolerance : 0 < tolerance) :
    utility.tailRadius (utility.leastHorizon start tolerance htolerance) ≤
        tolerance ∧
      ∀ earlier < utility.leastHorizon start tolerance htolerance,
        tolerance < utility.tailRadius earlier :=
  (utility.approximationScheme start).leastHorizon_spec tolerance
    (utility.exists_tailRadius_le tolerance htolerance)

end EventDiscountedPathUtility

namespace StateDiscountedPathUtility

variable {A : KernelArena}

variable (utility : StateDiscountedPathUtility A)

/-- State reward projection to action-recording events preserves every exact
finite discounted observable definitionally. -/
@[simp]
theorem toEvent_finiteObservable
    (start horizon : ℕ) (history : A.EventPrefix (start + horizon)) :
    utility.toEvent.finiteObservable start horizon history =
      utility.finiteObservable start horizon history.states :=
  rfl

/-- The projected event scheme is definitionally the A15 projection of the
state scheme, including its radius schedule. -/
theorem toEvent_approximationScheme
    (utility : StateDiscountedPathUtility A) (start : ℕ) :
    utility.toEvent.approximationScheme start =
      (utility.approximationScheme start).toEvent :=
  rfl

/-- Executing a state-history policy with action recording preserves the
discounted estimate after forgetting the recorded actions. -/
theorem toEvent_estimate_effectivePathLawFrom
    [(state : A.State) → Decidable (IsEmpty (A.Action state))]
    (utility : StateDiscountedPathUtility A)
    (policy : A.StateHistoryPolicy) (start : ℕ)
    (initialPrefix : A.EventPrefix start) (horizon : ℕ) :
    utility.toEvent.estimate
        ((policy.toEventHistoryPolicy).effectivePathLawFrom
          start initialPrefix) horizon =
      utility.estimate
        (policy.effectivePathLawFrom start initialPrefix.states) horizon := by
  change
    (utility.approximationScheme start).toEvent.estimate
        ((policy.toEventHistoryPolicy).effectivePathLawFrom
          start initialPrefix) horizon =
      (utility.approximationScheme start).estimate
        (policy.effectivePathLawFrom start initialPrefix.states) horizon
  exact
    StatePrefixApproximationScheme.toEvent_estimate_effectivePathLawFrom
      (utility.approximationScheme start) policy initialPrefix horizon

/-- The corresponding projected-event and state scheme intervals are equal. -/
theorem toEvent_interval_effectivePathLawFrom
    [(state : A.State) → Decidable (IsEmpty (A.Action state))]
    (utility : StateDiscountedPathUtility A)
    (policy : A.StateHistoryPolicy) (start : ℕ)
    (initialPrefix : A.EventPrefix start) (horizon : ℕ) :
    (utility.toEvent.approximationScheme start).interval
        ((policy.toEventHistoryPolicy).effectivePathLawFrom
          start initialPrefix) horizon =
      (utility.approximationScheme start).interval
        (policy.effectivePathLawFrom start initialPrefix.states) horizon := by
  rw [utility.toEvent_approximationScheme]
  exact
    StatePrefixApproximationScheme.toEvent_interval_effectivePathLawFrom
      (utility.approximationScheme start) policy initialPrefix horizon

end StateDiscountedPathUtility

end KernelArena
