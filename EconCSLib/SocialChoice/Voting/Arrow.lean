/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.SocialChoice.Voting.Decisive
import Mathlib.Data.Fintype.EquivFin

/-!
# EconCSLib.SocialChoice.Voting.Arrow

Arrow's Impossibility Theorem: there is no social welfare function
satisfying unanimity, IIA, and non-dictatorship when |A| ≥ 3.

## Main results

* `arrow_impossibility` — Arrow's theorem [MSZ 21.10]

This file is the public theorem entrypoint over the shared `SWF` /
bundled-preference API. Its implementation delegates to the internal complete
proof module.

## Implementation note

The public theorem below delegates to the complete decisive-coalitions proof
over the shared social-choice API.

## References

* [MSZ] Chapter 21, Theorem 21.10
* Arrow, K.J. (1951). *Social Choice and Individual Values*.
-/

namespace SocialChoice
namespace Voting

variable {N A : Type*}

/-- A finite alternative set with at least three elements contains three distinct
    alternatives. This local helper packages the cardinality assumption into the
    witness shape used by the decisive-coalitions proof of Arrow's theorem. -/
private theorem exists_three_distinct_of_card_ge_three {A : Type*} [Fintype A]
    (hA : Fintype.card A ≥ 3) :
    ∃ x y z : A, x ≠ y ∧ x ≠ z ∧ y ≠ z := by
  classical
  let e := Fintype.equivFin A
  refine ⟨e.symm ⟨0, ?_⟩, e.symm ⟨1, ?_⟩, e.symm ⟨2, ?_⟩, ?_, ?_, ?_⟩
  · exact lt_of_lt_of_le (by decide : 0 < 3) hA
  · exact lt_of_lt_of_le (by decide : 1 < 3) hA
  · exact lt_of_lt_of_le (by decide : 2 < 3) hA
  · intro h
    have := congrArg e h
    simp at this
  · intro h
    have := congrArg e h
    simp at this
  · intro h
    have := congrArg e h
    simp at this

/-- **Arrow's Impossibility Theorem** [MSZ 21.10]:

    If there are at least 3 alternatives, every social welfare function
    satisfying unanimity and IIA is dictatorial.
    The implementation uses the decisive-coalitions proof over the shared
    bundled-preference interface. -/
theorem arrow_impossibility [Fintype A] [Fintype N] [Nonempty N]
    (hA : Fintype.card A ≥ 3)
    (F : SWF N A) (hU : F.Unanimity) (hIIA : F.IIA) :
    F.Dictatorial := by
  classical
  exact arrow_of_unanimity_iia (N := N) (A := A) (h0 := exists_three_distinct_of_card_ge_three hA) hU hIIA

end Voting
end SocialChoice
