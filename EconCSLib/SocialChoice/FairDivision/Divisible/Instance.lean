/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.SocialChoice.FairDivision.Cardinal
import EconCSLib.SocialChoice.FairDivision.Divisible.Basic

/-!
# EconCSLib.SocialChoice.FairDivision.Divisible.Instance

Bundled semantic interfaces for divisible-goods fair division.

This file sits above the raw divisible allocation layer. It keeps
`Divisible.Allocation N Ω := FairDivision.Allocation N (Set Ω)` and
`Divisible.IsAllocation` as the low-level feasibility vocabulary,
while exposing canonical bundled instance types for ordinal, cardinal, and
measure-based divisible-goods problems.
-/

namespace SocialChoice
namespace FairDivision
namespace Divisible

open MeasureTheory Set

/-- An ordinal divisible-goods instance.

The cake is represented by the ambient measurable space `Ω`, and shares are
subsets of `Ω`. -/
structure Instance (N Ω : Type*) where
  /-- Each agent's ordinal preference over cake pieces. -/
  sharePref : N → Pref (Set Ω)

namespace Instance

/-- Feasibility for a divisible instance: an allocation is a measurable
    partition of the cake. -/
def feasible {N Ω : Type*} [MeasurableSpace Ω] [Fintype N]
    (_I : Instance N Ω) (A : Allocation N Ω) : Prop :=
  IsAllocation A

/-- View a divisible ordinal instance as a generic no-externality fair-division
    share instance. The resource is the whole cake `Set.univ`. -/
def toShareInstance {N Ω : Type*} [MeasurableSpace Ω] [Fintype N]
    (I : Instance N Ω) :
    SocialChoice.FairDivision.ShareInstance N (Set Ω) (Set Ω) where
  resource := Set.univ
  feasible := fun A => IsAllocation A
  sharePref := I.sharePref

end Instance

/-- A real-valued cardinal divisible-goods instance. -/
structure CardinalInstance (N Ω : Type*) where
  /-- Utility assigned by each agent to each cake piece. -/
  utility : N → Set Ω → ℝ

namespace CardinalInstance

/-- Feasibility for a cardinal divisible instance. -/
def feasible {N Ω : Type*} [MeasurableSpace Ω] [Fintype N]
    (_I : CardinalInstance N Ω)
    (A : Allocation N Ω) : Prop :=
  IsAllocation A

/-- View a divisible cardinal instance as a generic real-valued cardinal
    fair-division instance. The resource is the whole cake `Set.univ`. -/
def toGenericCardinalInstance {N Ω : Type*} [MeasurableSpace Ω] [Fintype N]
    (I : CardinalInstance N Ω) :
    SocialChoice.FairDivision.CardinalInstance N (Set Ω) (Set Ω) where
  resource := Set.univ
  feasible := fun A => IsAllocation A
  utility := I.utility

/-- View a divisible cardinal instance as the induced generic ordinal
    no-externality instance. -/
def toShareInstance {N Ω : Type*} [MeasurableSpace Ω] [Fintype N]
    (I : CardinalInstance N Ω) :
    SocialChoice.FairDivision.ShareInstance N (Set Ω) (Set Ω) :=
  I.toGenericCardinalInstance.toShareInstance

/-! ### Instance-relative fairness and welfare wrappers -/

/-- Envy-freeness for a divisible cardinal instance. -/
def IsEnvyFree {N Ω : Type*} [MeasurableSpace Ω] [Fintype N]
    (I : CardinalInstance N Ω) (A : Allocation N Ω) : Prop :=
  SocialChoice.FairDivision.CardinalInstance.IsEnvyFree
    I.toGenericCardinalInstance A

/-- Proportionality for a divisible cardinal instance, relative to the whole cake. -/
def IsProportional {N Ω : Type*} [MeasurableSpace Ω] [Fintype N]
    (I : CardinalInstance N Ω) (n : ℕ) (A : Allocation N Ω) : Prop :=
  SocialChoice.FairDivision.CardinalInstance.IsProportional
    I.toGenericCardinalInstance n Set.univ A

/-- Equitability for a divisible cardinal instance. -/
def IsEquitable {N Ω : Type*} [MeasurableSpace Ω] [Fintype N]
    (I : CardinalInstance N Ω) (A : Allocation N Ω) : Prop :=
  SocialChoice.FairDivision.CardinalInstance.IsEquitable
    I.toGenericCardinalInstance A

/-- Pareto optimality for a divisible cardinal instance. -/
def IsParetoOptimal {N Ω : Type*} [MeasurableSpace Ω] [Fintype N]
    (I : CardinalInstance N Ω) (A : Allocation N Ω) : Prop :=
  SocialChoice.FairDivision.CardinalInstance.IsParetoOptimal
    I.toGenericCardinalInstance A

/-- Utilitarian welfare for a divisible cardinal instance. -/
noncomputable def utilitarianWelfare {N Ω : Type*}
    [MeasurableSpace Ω] [Fintype N]
    (I : CardinalInstance N Ω) (A : Allocation N Ω) : ℝ :=
  SocialChoice.FairDivision.CardinalInstance.utilitarianWelfare
    I.toGenericCardinalInstance A

/-- Egalitarian welfare for a divisible cardinal instance. -/
noncomputable def egalitarianWelfare {N Ω : Type*}
    [MeasurableSpace Ω] [Fintype N] [Nonempty N]
    (I : CardinalInstance N Ω) (A : Allocation N Ω) : ℝ :=
  SocialChoice.FairDivision.CardinalInstance.egalitarianWelfare
    I.toGenericCardinalInstance A

end CardinalInstance

/-- A measure-based divisible-goods instance. -/
structure MeasureInstance (N Ω : Type*) [MeasurableSpace Ω] where
  /-- Each agent's measure over cake pieces. -/
  measure : N → Measure Ω

namespace MeasureInstance

/-- The raw cake valuation induced by a measure instance. -/
def toCakeValuation {N Ω : Type*} [MeasurableSpace Ω]
    (I : MeasureInstance N Ω) : CakeValuation N Ω ENNReal :=
  MeasureValuation I.measure

/-- The real-valued cardinal instance induced by measure values. -/
noncomputable def toCardinalInstance {N Ω : Type*} [MeasurableSpace Ω]
    (I : MeasureInstance N Ω) : CardinalInstance N Ω where
  utility := fun i S => (I.measure i S).toReal

/-- Feasibility for a measure-based divisible instance. Like the ordinal and
    cardinal divisible cases, this depends only on the ambient cake: a feasible
    allocation is a measurable partition of `Set.univ`. -/
def feasible {N Ω : Type*} [MeasurableSpace Ω] [Fintype N]
    (_I : MeasureInstance N Ω) (A : Allocation N Ω) : Prop :=
  IsAllocation A

/-- View a measure instance as a generic real-valued cardinal fair-division
    instance. -/
noncomputable def toGenericCardinalInstance {N Ω : Type*}
    [MeasurableSpace Ω] [Fintype N]
    (I : MeasureInstance N Ω) :
    SocialChoice.FairDivision.CardinalInstance N (Set Ω) (Set Ω) :=
  I.toCardinalInstance.toGenericCardinalInstance

/-- View a measure instance as the induced generic ordinal no-externality
    instance. -/
noncomputable def toShareInstance {N Ω : Type*} [MeasurableSpace Ω] [Fintype N]
    (I : MeasureInstance N Ω) :
    SocialChoice.FairDivision.ShareInstance N (Set Ω) (Set Ω) :=
  I.toGenericCardinalInstance.toShareInstance

/-! ### Instance-relative fairness wrappers -/

/-- Envy-freeness for a measure-based divisible instance, stated in `ENNReal`. -/
def IsEnvyFree {N Ω : Type*} [MeasurableSpace Ω]
    (I : MeasureInstance N Ω) (A : Allocation N Ω) : Prop :=
  SocialChoice.FairDivision.Divisible.IsEnvyFree I.toCakeValuation A

/-- For finite measure instances, the raw `ENNReal` envy-freeness predicate agrees with
    the real-valued cardinal predicate induced by `toReal`. -/
theorem isEnvyFree_iff_toCardinalInstance_isEnvyFree
    {N Ω : Type*} [MeasurableSpace Ω] [Fintype N]
    (I : MeasureInstance N Ω) [∀ i, IsFiniteMeasure (I.measure i)]
    (A : Allocation N Ω) :
    I.IsEnvyFree A ↔ I.toCardinalInstance.IsEnvyFree A := by
  constructor
  · intro h i j
    exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).mpr (h i j)
  · intro h i j
    exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).mp (h i j)

/-- Proportionality for a measure-based divisible instance, stated in `ENNReal`. -/
def IsProportional {N Ω : Type*} [MeasurableSpace Ω]
    (I : MeasureInstance N Ω) (n : ℕ) (A : Allocation N Ω) : Prop :=
  SocialChoice.FairDivision.Divisible.IsProportional n I.toCakeValuation A

/-- Equitability for a measure-based divisible instance, stated in `ENNReal`. -/
def IsEquitable {N Ω : Type*} [MeasurableSpace Ω]
    (I : MeasureInstance N Ω) (A : Allocation N Ω) : Prop :=
  SocialChoice.FairDivision.Divisible.IsEquitable I.toCakeValuation A

/-- Envy-freeness implies proportionality for complete measure-based divisible allocations. -/
theorem IsEnvyFree.isProportional {N Ω : Type*}
    [MeasurableSpace Ω] [Fintype N]
    (I : MeasureInstance N Ω)
    (A : Allocation N Ω)
    (ha : IsAllocation A)
    (hef : I.IsEnvyFree A) :
    I.IsProportional (Fintype.card N) A :=
  SocialChoice.FairDivision.Divisible.IsEnvyFree.isProportional I.measure A ha hef

end MeasureInstance

end Divisible
end FairDivision
end SocialChoice
