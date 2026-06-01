/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.SocialChoice.Voting.VotingRules

/-!
# EconCSLib.SocialChoice.Voting.ProfileSurgery

Reusable profile-modification constructions for strict voting profiles.

The main construction is `zProfile P Q R`, the Muller-Satterthwaite splice:
alternatives in `R` are ranked above alternatives outside `R`; inside `R` the
ballot follows `P`, and outside `R` it follows `Q`.
-/

namespace SocialChoice
namespace Voting

variable {N A : Type*}

/-- The rank function used by `zBallot`: first separate alternatives by
membership in `R`, then use the relevant source ballot's rank. -/
private noncomputable def zKey [Fintype A] (P Q : LinearOrder A) (R : Set A)
    [∀ a : A, Decidable (a ∈ R)] (a : A) : Nat :=
  let base := Fintype.card A + 1
  let block := if a ∈ R then 0 else 1
  let localRank := if a ∈ R then rank P a else rank Q a
  block * base + localRank

private theorem zKey_injective [Fintype A] (P Q : LinearOrder A) (R : Set A)
    [∀ a : A, Decidable (a ∈ R)] :
    Function.Injective (zKey P Q R) := by
  intro a b h
  by_cases ha : a ∈ R <;> by_cases hb : b ∈ R
  · have hr : rank P a = rank P b := by
      simpa [zKey, ha, hb] using h
    exact rank_injective P hr
  · have hrank := rank_lt_card P a
    have hr : rank P a = Fintype.card A + 1 + rank Q b := by
      simpa [zKey, ha, hb, Nat.add_assoc] using h
    omega
  · have hrank := rank_lt_card P b
    have hr : Fintype.card A + 1 + rank Q a = rank P b := by
      simpa [zKey, ha, hb, Nat.add_assoc] using h
    omega
  · have hr : rank Q a = rank Q b := by
      simpa [zKey, ha, hb] using h
    exact rank_injective Q hr

/-- Splice two ballots across a set of alternatives. -/
noncomputable def zBallot [Fintype A] (P Q : LinearOrder A) (R : Set A)
    [∀ a : A, Decidable (a ∈ R)] : LinearOrder A :=
  ballotFromInjective (inferInstance : LinearOrder Nat) (zKey P Q R) (zKey_injective P Q R)

/-- Pointwise profile splice. -/
noncomputable def zProfile [Fintype N] [Fintype A]
    (P Q : Profile N A) (R : Set A) [∀ a : A, Decidable (a ∈ R)] :
    Profile N A where
  pref := fun i => zBallot (P.pref i) (Q.pref i) R

@[simp]
theorem zProfile_apply [Fintype N] [Fintype A]
    (P Q : Profile N A) (R : Set A) [∀ a : A, Decidable (a ∈ R)] (i : N) :
    (zProfile P Q R).pref i = zBallot (P.pref i) (Q.pref i) R :=
  rfl

/-- Inside `R`, the splice follows the first profile. -/
theorem zProfile_prefers_inside [Fintype N] [Fintype A]
    (P Q : Profile N A) (R : Set A) [∀ a : A, Decidable (a ∈ R)]
    {a b : A} (ha : a ∈ R) (hb : b ∈ R) (i : N) :
    Prefers (zProfile P Q R) i a b ↔ Prefers P i a b := by
  simp [Prefers, zProfile, zBallot, zKey, ha, hb, rank_lt_iff]

/-- Outside `R`, the splice follows the second profile. -/
theorem zProfile_prefers_outside [Fintype N] [Fintype A]
    (P Q : Profile N A) (R : Set A) [∀ a : A, Decidable (a ∈ R)]
    {a b : A} (ha : a ∉ R) (hb : b ∉ R) (i : N) :
    Prefers (zProfile P Q R) i a b ↔ Prefers Q i a b := by
  simp [Prefers, zProfile, zBallot, zKey, ha, hb, rank_lt_iff]

/-- Every alternative inside `R` is ranked above every alternative outside `R`. -/
theorem zProfile_prefers_inside_outside [Fintype N] [Fintype A]
    (P Q : Profile N A) (R : Set A) [∀ a : A, Decidable (a ∈ R)]
    {a b : A} (ha : a ∈ R) (hb : b ∉ R) (i : N) :
    Prefers (zProfile P Q R) i a b := by
  have hrank := rank_lt_card (P.pref i) a
  simp [Prefers, zProfile, zBallot, zKey, ha, hb]
  omega

end Voting
end SocialChoice
