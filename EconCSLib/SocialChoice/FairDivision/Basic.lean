/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.SocialChoice.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Basic

/-!
# EconCSLib.SocialChoice.FairDivision.Basic

Generic fair-division vocabulary as a structured special case of social choice.

This file introduces:

- `Allocation N S` as the common shape of an allocation
- `Instance` for fully general fair-division problems with preferences over
  complete allocations
- `ShareInstance` for the standard no-externality model where each agent ranks
  only the share they receive
- the lift `ShareInstance.toInstance`, showing how fair division fits into the
  generic social-choice layer
-/

namespace SocialChoice
namespace FairDivision

/-- A fair-division allocation assigns each agent a share. -/
abbrev Allocation (N S : Type*) := N → S

/-- A fully general fair-division instance.

    This allows preferences over complete allocations, so it can express
    externalities or other global allocation comparisons. -/
structure Instance (N R S : Type*) where
  /-- Resource-side data for the instance. -/
  resource : R
  /-- Feasible allocations for the given resource data. -/
  feasible : Allocation N S → Prop
  /-- Each agent's preference over complete allocations. -/
  pref : N → Pref (Allocation N S)

/-- A no-externality fair-division instance where each agent ranks only the share
    they personally receive. -/
structure ShareInstance (N R S : Type*) where
  /-- Resource-side data for the instance. -/
  resource : R
  /-- Feasible allocations for the given resource data. -/
  feasible : Allocation N S → Prop
  /-- Each agent's preference over individual shares. -/
  sharePref : N → Pref S

namespace ShareInstance

/-- Lift a no-externality fair-division instance to a fully general
    allocation-preference instance by comparing allocations pointwise through the
    share assigned to the evaluating agent. -/
def toInstance {N R S : Type*}
    (I : ShareInstance N R S) : Instance N R S where
  resource := I.resource
  feasible := I.feasible
  pref i :=
    { rel := fun A B => I.sharePref i (A i) (B i)
      prop :=
        { reflexive := ⟨fun A => (I.sharePref i |>.prop.reflexive).refl (A i)⟩
          transitive := ⟨fun _ _ _ hAB hBC =>
            (I.sharePref i |>.prop.transitive).trans _ _ _ hAB hBC⟩
          total := fun A B => I.sharePref i |>.prop.total (A i) (B i) } }

end ShareInstance

/-- A fair-division solution concept is a predicate selecting acceptable
    allocations relative to a fully general instance. -/
def SolutionConcept (N R S : Type*) :=
  Instance N R S → Allocation N S → Prop

/-- A fair-division rule returns a feasible allocation for every instance. -/
def Rule (N R S : Type*) :=
  (I : Instance N R S) → {A : Allocation N S // I.feasible A}

end FairDivision
end SocialChoice
