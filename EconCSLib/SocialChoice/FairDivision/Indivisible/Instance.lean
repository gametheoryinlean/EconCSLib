/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.SocialChoice.FairDivision.Cardinal
import EconCSLib.SocialChoice.FairDivision.Indivisible.Efficiency
import EconCSLib.SocialChoice.FairDivision.Indivisible.SocialWelfare
import EconCSLib.SocialChoice.FairDivision.Indivisible.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# EconCSLib.SocialChoice.FairDivision.Indivisible.Instance

Bundled semantic interfaces for indivisible-goods fair division.

This file sits above the raw indivisible allocation layer. It keeps
`Allocation N G := N → Finset G` and `IsAllocation` as the low-level
feasibility vocabulary, while exposing canonical bundled instance types for
ordinal, cardinal, and additive indivisible-goods problems.
-/

open BigOperators

namespace SocialChoice
namespace FairDivision
namespace Indivisible

/-- An ordinal indivisible-goods instance.

`allGoods` is the finite set of goods to allocate. Each agent ranks bundles of
goods, represented as `Finset G`. -/
structure Instance (N G : Type*) where
  /-- The goods that must be allocated. -/
  allGoods : Finset G
  /-- Each agent's ordinal preference over bundles. -/
  sharePref : N → Pref (Finset G)

namespace Instance

/-- Feasibility for an indivisible instance: an allocation partitions
    `I.allGoods`. -/
def feasible {N G : Type*} [Fintype N] [DecidableEq G]
    (I : Instance N G) (A : Allocation N G) : Prop :=
  IsAllocation I.allGoods A

/-- View an indivisible ordinal instance as a generic no-externality
    fair-division share instance. -/
def toShareInstance {N G : Type*} [Fintype N] [DecidableEq G]
    (I : Instance N G) :
    SocialChoice.FairDivision.ShareInstance N (Finset G) (Finset G) where
  resource := I.allGoods
  feasible := fun A => IsAllocation I.allGoods A
  sharePref := I.sharePref

end Instance

/-- A real-valued cardinal indivisible-goods instance. -/
structure CardinalInstance (N G : Type*) where
  /-- The goods that must be allocated. -/
  allGoods : Finset G
  /-- Utility assigned by each agent to each bundle. -/
  utility : N → Finset G → ℝ

namespace CardinalInstance

/-- The raw valuation induced by a cardinal indivisible instance. -/
def toValuation {N G : Type*}
    (I : CardinalInstance N G) : Valuation N G where
  val := I.utility

/-- Feasibility for a cardinal indivisible instance. -/
def feasible {N G : Type*} [Fintype N] [DecidableEq G]
    (I : CardinalInstance N G) (A : Allocation N G) : Prop :=
  IsAllocation I.allGoods A

/-- View an indivisible cardinal instance as a generic real-valued cardinal
    fair-division instance. -/
def toGenericCardinalInstance {N G : Type*} [Fintype N] [DecidableEq G]
    (I : CardinalInstance N G) :
    SocialChoice.FairDivision.CardinalInstance N (Finset G) (Finset G) where
  resource := I.allGoods
  feasible := fun A => IsAllocation I.allGoods A
  utility := I.utility

/-- View an indivisible cardinal instance as the induced generic ordinal
    no-externality instance. -/
def toShareInstance {N G : Type*} [Fintype N] [DecidableEq G]
    (I : CardinalInstance N G) :
    SocialChoice.FairDivision.ShareInstance N (Finset G) (Finset G) :=
  I.toGenericCardinalInstance.toShareInstance

/-! ### Instance-relative fairness and welfare wrappers -/

/-- Envy-freeness for an indivisible cardinal instance. -/
def IsEnvyFree {N G : Type*}
    (I : CardinalInstance N G) (A : Allocation N G) : Prop :=
  SocialChoice.FairDivision.Indivisible.IsEnvyFree I.toValuation A

/-- Envy-freeness up to one good for an indivisible cardinal instance. -/
def IsEF1 {N G : Type*} [DecidableEq G]
    (I : CardinalInstance N G) (A : Allocation N G) : Prop :=
  SocialChoice.FairDivision.Indivisible.IsEF1 I.toValuation A

/-- Envy-freeness up to any good for an indivisible cardinal instance. -/
def IsEFX {N G : Type*} [DecidableEq G]
    (I : CardinalInstance N G) (A : Allocation N G) : Prop :=
  SocialChoice.FairDivision.Indivisible.IsEFX I.toValuation A

/-- Proportionality for an indivisible cardinal instance, relative to the
    instance's full set of goods. -/
def IsProportional {N G : Type*}
    (I : CardinalInstance N G) (n : ℕ) (A : Allocation N G) : Prop :=
  SocialChoice.FairDivision.Indivisible.IsProportional n I.toValuation I.allGoods A

/-- Equitability for an indivisible cardinal instance. -/
def IsEquitable {N G : Type*}
    (I : CardinalInstance N G) (A : Allocation N G) : Prop :=
  SocialChoice.FairDivision.Indivisible.IsEquitable I.toValuation A

/-- Maximin-share guarantee for an indivisible cardinal instance. -/
def IsMaxminShare {N G : Type*} [Fintype N] [DecidableEq G]
    (I : CardinalInstance N G) (A : Allocation N G) : Prop :=
  SocialChoice.FairDivision.Indivisible.IsMaxminShare I.toValuation I.allGoods A

/-- Pareto optimality for an indivisible cardinal instance. -/
def IsParetoOptimal {N G : Type*} [Fintype N] [DecidableEq G]
    (I : CardinalInstance N G) (A : Allocation N G) : Prop :=
  SocialChoice.FairDivision.Indivisible.IsParetoOptimal I.toValuation I.allGoods A

/-- Utilitarian welfare for an indivisible cardinal instance. -/
noncomputable def utilitarianWelfare {N G : Type*} [Fintype N]
    (I : CardinalInstance N G) (A : Allocation N G) : ℝ :=
  SocialChoice.FairDivision.Indivisible.utilitarianWelfare I.toValuation A

/-- Egalitarian welfare for an indivisible cardinal instance. -/
noncomputable def egalitarianWelfare {N G : Type*} [Fintype N] [Nonempty N]
    (I : CardinalInstance N G) (A : Allocation N G) : ℝ :=
  SocialChoice.FairDivision.Indivisible.egalitarianWelfare I.toValuation A

/-- Utilitarian optimality for an indivisible cardinal instance. -/
def IsUtilitarianOptimal {N G : Type*} [Fintype N] [DecidableEq G]
    (I : CardinalInstance N G) (A : Allocation N G) : Prop :=
  SocialChoice.FairDivision.Indivisible.IsUtilitarianOptimal I.toValuation I.allGoods A

/-- Maximin social-welfare optimality for an indivisible cardinal instance. -/
def IsMaxmin {N G : Type*} [Fintype N] [Nonempty N] [DecidableEq G]
    (I : CardinalInstance N G) (A : Allocation N G) : Prop :=
  SocialChoice.FairDivision.Indivisible.IsMaxmin I.toValuation I.allGoods A

end CardinalInstance

/-- An additive indivisible-goods instance, represented by per-item weights. -/
structure AdditiveInstance (N G : Type*) where
  /-- The goods that must be allocated. -/
  allGoods : Finset G
  /-- Per-agent, per-good weights. -/
  weight : N → G → ℝ

namespace AdditiveInstance

/-- The raw additive valuation induced by additive per-item weights. -/
def toAdditiveValuation {N G : Type*}
    (I : AdditiveInstance N G) : AdditiveValuation N G where
  weight := I.weight

/-- The abstract valuation induced by additive per-item weights. -/
def toValuation {N G : Type*}
    (I : AdditiveInstance N G) : Valuation N G :=
  I.toAdditiveValuation.toValuation

/-- The cardinal instance induced by additive per-item weights. -/
def toCardinalInstance {N G : Type*}
    (I : AdditiveInstance N G) : CardinalInstance N G where
  allGoods := I.allGoods
  utility := I.toValuation.val

/-- View an additive indivisible instance as a generic real-valued cardinal
    fair-division instance. -/
def toGenericCardinalInstance {N G : Type*} [Fintype N] [DecidableEq G]
    (I : AdditiveInstance N G) :
    SocialChoice.FairDivision.CardinalInstance N (Finset G) (Finset G) :=
  I.toCardinalInstance.toGenericCardinalInstance

/-- View an additive indivisible instance as the induced generic ordinal
    no-externality instance. -/
def toShareInstance {N G : Type*} [Fintype N] [DecidableEq G]
    (I : AdditiveInstance N G) :
    SocialChoice.FairDivision.ShareInstance N (Finset G) (Finset G) :=
  I.toGenericCardinalInstance.toShareInstance

/-! ### Instance-relative fairness wrappers -/

/-- Envy-freeness for an additive indivisible instance. -/
def IsEnvyFree {N G : Type*}
    (I : AdditiveInstance N G) (A : Allocation N G) : Prop :=
  SocialChoice.FairDivision.Indivisible.IsEnvyFree I.toValuation A

/-- Envy-freeness up to one good for an additive indivisible instance. -/
def IsEF1 {N G : Type*} [DecidableEq G]
    (I : AdditiveInstance N G) (A : Allocation N G) : Prop :=
  SocialChoice.FairDivision.Indivisible.IsEF1 I.toValuation A

/-- Envy-freeness up to any good for an additive indivisible instance. -/
def IsEFX {N G : Type*} [DecidableEq G]
    (I : AdditiveInstance N G) (A : Allocation N G) : Prop :=
  SocialChoice.FairDivision.Indivisible.IsEFX I.toValuation A

/-- Proportionality for an additive indivisible instance. -/
def IsProportional {N G : Type*}
    (I : AdditiveInstance N G) (n : ℕ) (A : Allocation N G) : Prop :=
  SocialChoice.FairDivision.Indivisible.IsProportional n I.toValuation I.allGoods A

/-- Equitability for an additive indivisible instance. -/
def IsEquitable {N G : Type*}
    (I : AdditiveInstance N G) (A : Allocation N G) : Prop :=
  SocialChoice.FairDivision.Indivisible.IsEquitable I.toValuation A

/-- Maximin-share guarantee for an additive indivisible instance. -/
def IsMaxminShare {N G : Type*} [Fintype N] [DecidableEq G]
    (I : AdditiveInstance N G) (A : Allocation N G) : Prop :=
  SocialChoice.FairDivision.Indivisible.IsMaxminShare I.toValuation I.allGoods A

/-- Pareto optimality for an additive indivisible instance. -/
def IsParetoOptimal {N G : Type*} [Fintype N] [DecidableEq G]
    (I : AdditiveInstance N G) (A : Allocation N G) : Prop :=
  SocialChoice.FairDivision.Indivisible.IsParetoOptimal I.toValuation I.allGoods A

/-- Utilitarian welfare for an additive indivisible instance. -/
noncomputable def utilitarianWelfare {N G : Type*} [Fintype N]
    (I : AdditiveInstance N G) (A : Allocation N G) : ℝ :=
  SocialChoice.FairDivision.Indivisible.utilitarianWelfare I.toValuation A

/-- Egalitarian welfare for an additive indivisible instance. -/
noncomputable def egalitarianWelfare {N G : Type*} [Fintype N] [Nonempty N]
    (I : AdditiveInstance N G) (A : Allocation N G) : ℝ :=
  SocialChoice.FairDivision.Indivisible.egalitarianWelfare I.toValuation A

/-- Utilitarian optimality for an additive indivisible instance. -/
def IsUtilitarianOptimal {N G : Type*} [Fintype N] [DecidableEq G]
    (I : AdditiveInstance N G) (A : Allocation N G) : Prop :=
  SocialChoice.FairDivision.Indivisible.IsUtilitarianOptimal I.toValuation I.allGoods A

/-- Maximin social-welfare optimality for an additive indivisible instance. -/
def IsMaxmin {N G : Type*} [Fintype N] [Nonempty N] [DecidableEq G]
    (I : AdditiveInstance N G) (A : Allocation N G) : Prop :=
  SocialChoice.FairDivision.Indivisible.IsMaxmin I.toValuation I.allGoods A

/-- Feasibility for an additive indivisible instance. -/
def feasible {N G : Type*} [Fintype N] [DecidableEq G]
    (I : AdditiveInstance N G) (A : Allocation N G) : Prop :=
  IsAllocation I.allGoods A

end AdditiveInstance

end Indivisible
end FairDivision
end SocialChoice
