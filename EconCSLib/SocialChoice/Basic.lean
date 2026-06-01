/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.Foundation.Preference
import Mathlib.Data.Set.Basic

/-!
# EconCSLib.SocialChoice.Basic

Generic social-choice vocabulary: alternatives, feasible sets, and
instance-level rules/correspondences. Bundled preferences come from
`Foundation.Preference` so that social choice, fair division, and matching use
the same semantic object.

## Main definitions

* `SocialChoice.Instance N A` — a generic social-choice instance over feasible
  alternatives and agent preferences
* `SocialChoice.SolutionConcept N A` — predicate selecting acceptable alternatives
  relative to an instance
* `SocialChoice.Rule N A` — a single-valued feasible choice
* `SocialChoice.Correspondence N A` — a set-valued choice rule

## References

* [MSZ] Maschler, Solan, Zamir, *Game Theory*, Chapter 21
* Arrow, K.J. (1951). *Social Choice and Individual Values*.
-/

namespace SocialChoice

/-! ### Generic instances and rules -/

/-- A generic social-choice instance consists of feasible alternatives together with
    each agent's preference over the alternative space. -/
structure Instance (N A : Type*) where
  /-- Feasible alternatives for this instance. -/
  feasible : A → Prop
  /-- Each agent's weak preference over alternatives. -/
  pref : N → Pref A

/-- A solution concept is a predicate selecting acceptable alternatives relative
    to a social-choice instance. -/
def SolutionConcept (N A : Type*) :=
  Instance N A → A → Prop

/-- A rule returns a feasible alternative for every instance. -/
def Rule (N A : Type*) :=
  (I : Instance N A) → {a : A // I.feasible a}

/-- A correspondence is a set-valued choice rule on instances. -/
def Correspondence (N A : Type*) :=
  Instance N A → Set A

end SocialChoice
