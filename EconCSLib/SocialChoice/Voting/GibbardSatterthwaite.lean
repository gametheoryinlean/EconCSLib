/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.SocialChoice.Voting.Arrow
import EconCSLib.SocialChoice.Voting.ProfileSurgery
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card

/-!
# EconCSLib.SocialChoice.Voting.GibbardSatterthwaite

The Gibbard-Satterthwaite theorem and its standard finite-profile proof route.

The public statements use the voting layer's set-valued `VotingRule` interface
plus a `Resolute` hypothesis. The proof is intentionally deferred while the
voting architecture is being rebuilt.

## Theorem statements

* `muller_satterthwaite` — monotonic + unanimous + resolute implies dictatorial
* `strategyproof_monotonic` — resolute strategy-proof implies monotonic
* `gibbard_satterthwaite` — resolute strategy-proof + unanimous implies
  dictatorial

## References

* [MSZ] Chapter 21, Theorems 21.27, 21.35, 21.39
* Gibbard (1973), Satterthwaite (1975)
-/

namespace SocialChoice
namespace Voting

variable {N A : Type*}

private def pairSet (a b : A) : Set A :=
  {x | x = a ∨ x = b}

private def tripleSet (a b c : A) : Set A :=
  {x | x = a ∨ x = b ∨ x = c}

private theorem pairSet_nonempty (a b : A) : (pairSet a b).Nonempty :=
  ⟨a, Or.inl rfl⟩

private theorem mem_pair_left (a b : A) : a ∈ pairSet a b :=
  Or.inl rfl

private theorem mem_pair_right (a b : A) : b ∈ pairSet a b :=
  Or.inr rfl

private theorem mem_triple_left (a b c : A) : a ∈ tripleSet a b c :=
  Or.inl rfl

private theorem mem_triple_mid (a b c : A) : b ∈ tripleSet a b c :=
  Or.inr (Or.inl rfl)

private theorem mem_triple_right (a b c : A) : c ∈ tripleSet a b c :=
  Or.inr (Or.inr rfl)

private theorem pair_subset_triple_left (a b c : A) :
    pairSet a b ⊆ tripleSet a b c := by
  intro x hx
  rcases hx with hx | hx
  · exact Or.inl hx
  · exact Or.inr (Or.inl hx)

private theorem pair_subset_triple_right (a b c : A) :
    pairSet a c ⊆ tripleSet a b c := by
  intro x hx
  rcases hx with hx | hx
  · exact Or.inl hx
  · exact Or.inr (Or.inr hx)

private theorem pair_subset_triple_mid_right (a b c : A) :
    pairSet b c ⊆ tripleSet a b c := by
  intro x hx
  rcases hx with hx | hx
  · exact Or.inr (Or.inl hx)
  · exact Or.inr (Or.inr hx)

@[reducible]
private noncomputable def hybridProfile [Fintype N] [DecidableEq N] [Fintype A]
    (P Q : Profile N A) (S : Finset N) : Profile N A where
  pref := fun i => if i ∈ S then Q.pref i else P.pref i

private theorem resolute_eq_singleton_of_mem [Fintype N] [Fintype A]
    {f : VotingRule N A} (hf_res : Resolute f) {P : Profile N A} {a : A}
    (ha : a ∈ f P) : f P = {a} := by
  rcases Finset.card_eq_one.mp (hf_res P) with ⟨b, hb⟩
  have hba : a = b := by
    simpa [hb] using ha
  simp [hb, hba]

private theorem hybridProfile_insert_eq_update [Fintype N] [DecidableEq N] [Fintype A]
    (P Q : Profile N A) (S : Finset N) {i : N} (hi : i ∉ S) :
    hybridProfile P Q (insert i S) = updateProfile (hybridProfile P Q S) i (Q.pref i) := by
  classical
  apply Profile.ext
  intro j
  by_cases hji : j = i
  · subst hji
    simp [hi]
  · simp [hji]

private theorem hybridProfile_erase_eq_update [Fintype N] [DecidableEq N] [Fintype A]
    (P Q : Profile N A) (S : Finset N) {i : N} (hi : i ∉ S) :
    hybridProfile P Q S = updateProfile (hybridProfile P Q (insert i S)) i (P.pref i) := by
  classical
  apply Profile.ext
  intro j
  by_cases hji : j = i
  · subst hji
    simp [hi]
  · simp [hji]

private theorem strategyproof_insert_preserves_choice [Fintype N] [DecidableEq N] [Fintype A]
    (f : VotingRule N A) (hf_res : Resolute f)
    (hSP : ResoluteStrategyproofness f hf_res)
    {P Q : Profile N A} {a : A} (hLift : SimpleLift Q P a)
    {S : Finset N} {i : N} (hi : i ∉ S)
    (ha : a ∈ f (hybridProfile P Q S)) :
    a ∈ f (hybridProfile P Q (insert i S)) := by
  classical
  by_contra hnot
  let H0 := hybridProfile P Q S
  let H1 := hybridProfile P Q (insert i S)
  have hf0 : f H0 = {a} := resolute_eq_singleton_of_mem hf_res ha
  rcases Finset.card_eq_one.mp (hf_res H1) with ⟨b, hb⟩
  have hbmem : b ∈ f H1 := by simp [hb]
  have hba : b ≠ a := by
    intro h
    exact hnot (by simpa [h] using hbmem)
  have hforward : ¬ Prefers H0 i b a := by
    have hupdate : f (updateProfile H0 i (Q.pref i)) = {b} := by
      rw [← hybridProfile_insert_eq_update P Q S hi]
      exact hb
    exact hSP H0 i (Q.pref i) a b hf0 hupdate
  have hreverse : ¬ Prefers H1 i a b := by
    have hupdate : f (updateProfile H1 i (P.pref i)) = {a} := by
      rw [← hybridProfile_erase_eq_update P Q S hi]
      exact hf0
    exact hSP H1 i (P.pref i) b a hb hupdate
  have hP_or := Prefers.total_of_ne P i (Ne.symm hba)
  cases hP_or with
  | inl hPab =>
      have hQab := (hLift i b).left hPab
      have hH1ab : Prefers H1 i a b := by
        simpa [H1, hybridProfile, Prefers] using hQab
      exact hreverse hH1ab
  | inr hPba =>
      have hH0ba : Prefers H0 i b a := by
        simpa [H0, hybridProfile, Prefers, hi] using hPba
      exact hforward hH0ba

/-! ### Profile-surgery lemmas -/

/-- If a monotonic resolute voting rule selects `a` at `P`, then `a` remains
selected after the MSZ splice `Z(P,Q;R)`, provided `a ∈ R`.

This is the set-valued strict-profile form of [MSZ 21.31]. -/
theorem monotonic_zProfile [Fintype N] [Fintype A]
    (f : VotingRule N A) (hM : Monotonicity f)
    (P Q : Profile N A) (R : Set A) [∀ a : A, Decidable (a ∈ R)]
    {a : A} (haR : a ∈ R) (ha : a ∈ f P) :
    a ∈ f (zProfile P Q R) := by
  exact hM P (zProfile P Q R) a ha (by
    intro i x
    constructor
    · intro hax
      by_cases hxR : x ∈ R
      · exact (zProfile_prefers_inside P Q R haR hxR i).mpr hax
      · exact zProfile_prefers_inside_outside P Q R haR hxR i
    · intro hxa
      by_cases hxR : x ∈ R
      · exact (zProfile_prefers_inside P Q R hxR haR i).mp hxa
      · have hax := zProfile_prefers_inside_outside P Q R haR hxR i
        exact False.elim ((Prefers.asymm (zProfile P Q R) i hax) hxa))

/-- If every voter strictly prefers `a` to `b`, then a unanimous monotonic
resolute voting rule cannot choose `b`. This is the set-valued strict-profile
form of [MSZ 21.32]. -/
theorem unanimous_strict_pref_not_chosen [Fintype N] [Nonempty N] [Fintype A]
    (f : VotingRule N A) (hU : Unanimity f) (_hM : Monotonicity f)
    (P : Profile N A) {a b : A}
    (hab : ∀ i : N, Prefers P i a b) :
    b ∉ f P := by
  exact hU P a b hab

/-- Under unanimity and monotonicity, every winner of `zProfile P Q R` belongs
to `R` whenever `R` is nonempty. This is the set-valued strict-profile form of
[MSZ 21.33]. -/
theorem zProfile_choice_mem [Fintype N] [Nonempty N] [Fintype A]
    (f : VotingRule N A) (hU : Unanimity f) (_hM : Monotonicity f)
    (P Q : Profile N A) (R : Set A) [∀ a : A, Decidable (a ∈ R)]
    (hR : R.Nonempty) {a : A} (ha : a ∈ f (zProfile P Q R)) :
    a ∈ R := by
  by_contra haR
  rcases hR with ⟨b, hbR⟩
  exact (hU (zProfile P Q R) b a
    (fun i => zProfile_prefers_inside_outside P Q R hbR haR i)) ha

private noncomputable def choiceProfile [Fintype N] [Fintype A]
    (P : Profile N A) (R : Set A) : Profile N A := by
  classical
  exact @zProfile N A _ _ P P R (fun x => Classical.propDecidable (x ∈ R))

private theorem zProfile_choice_contraction [Fintype N] [Fintype A]
    (f : VotingRule N A) (hM : Monotonicity f)
    (P : Profile N A) (R S : Set A)
    {a : A} (hSR : S ⊆ R) (haS : a ∈ S)
    (ha : a ∈ f (choiceProfile P R)) :
    a ∈ f (choiceProfile P S) := by
  classical
  have haR : a ∈ R := hSR haS
  exact hM (choiceProfile P R) (choiceProfile P S) a ha (by
    dsimp [choiceProfile]
    intro i x
    constructor
    · intro hax
      by_cases hxS : x ∈ S
      · have hxR : x ∈ R := hSR hxS
        have hP := (zProfile_prefers_inside P P R haR hxR i).mp hax
        exact (zProfile_prefers_inside P P S haS hxS i).mpr hP
      · exact zProfile_prefers_inside_outside P P S haS hxS i
    · intro hxa
      by_cases hxS : x ∈ S
      · have hxR : x ∈ R := hSR hxS
        have hP := (zProfile_prefers_inside P P S hxS haS i).mp hxa
        exact (zProfile_prefers_inside P P R hxR haR i).mpr hP
      · have hax := zProfile_prefers_inside_outside P P S haS hxS i
        exact False.elim ((Prefers.asymm (zProfile P P S) i hax) hxa))

private noncomputable def revealedRel [Fintype N] [Fintype A]
    (f : VotingRule N A) (P : Profile N A) (a b : A) : Prop := by
  classical
  exact a = b ∨ a ∈ f (choiceProfile P (pairSet a b))

private theorem revealedRel_total [Fintype N] [Nonempty N] [Fintype A]
    (f : VotingRule N A) (hf_total : IsTotal f)
    (hU : Unanimity f) (hM : Monotonicity f)
    (P : Profile N A) (a b : A) :
    revealedRel f P a b ∨ revealedRel f P b a := by
  classical
  by_cases hab : a = b
  · left
    exact Or.inl hab
  · rcases hf_total (choiceProfile P (pairSet a b)) with ⟨c, hc⟩
    have hcPair : c ∈ pairSet a b :=
      by
        simpa [choiceProfile] using
          zProfile_choice_mem f hU hM P P (pairSet a b) (pairSet_nonempty a b) hc
    rcases hcPair with hcA | hcB
    · left
      exact Or.inr (by simpa [hcA] using hc)
    · right
      have hbChoice : b ∈ f (choiceProfile P (pairSet a b)) := by
        simpa [hcB] using hc
      have hb : b ∈ f (choiceProfile P (pairSet b a)) :=
        zProfile_choice_contraction f hM P (pairSet a b) (pairSet b a)
          (by
            intro x hx
            rcases hx with rfl | rfl
            · exact Or.inr rfl
            · exact Or.inl rfl)
          (mem_pair_left b a) hbChoice
      exact Or.inr hb

private theorem revealedRel_trans [Fintype N] [Nonempty N] [Fintype A]
    (f : VotingRule N A) (hf_total : IsTotal f) (hf_res : Resolute f)
    (hU : Unanimity f) (hM : Monotonicity f)
    (P : Profile N A) :
    Transitive (revealedRel f P) := by
  classical
  intro a b c hab hbc
  by_cases hab_eq : a = b
  · simpa [hab_eq] using hbc
  by_cases hbc_eq : b = c
  · simpa [← hbc_eq] using hab
  by_cases hac_eq : a = c
  · exact Or.inl hac_eq
  have haPair : a ∈ f (zProfile P P (pairSet a b)) := by
    rcases hab with hEq | hmem
    · exact False.elim (hab_eq hEq)
    · exact hmem
  have hbPair : b ∈ f (zProfile P P (pairSet b c)) := by
    rcases hbc with hEq | hmem
    · exact False.elim (hbc_eq hEq)
    · exact hmem
  by_contra hnotRel
  have hnotA : a ∉ f (choiceProfile P (pairSet a c)) := by
    intro ha
    exact hnotRel (Or.inr ha)
  rcases hf_total (choiceProfile P (tripleSet a b c)) with ⟨d, hd⟩
  have hdTriple : d ∈ tripleSet a b c :=
    by
      simpa [choiceProfile] using
        zProfile_choice_mem f hU hM P P (tripleSet a b c)
          ⟨a, mem_triple_left a b c⟩ hd
  rcases hdTriple with hdA | hdBC
  · subst d
    have haAC : a ∈ f (choiceProfile P (pairSet a c)) :=
      zProfile_choice_contraction f hM P (tripleSet a b c) (pairSet a c)
        (pair_subset_triple_right a b c) (mem_pair_left a c) hd
    exact hnotA haAC
  · rcases hdBC with hdB | hdC
    · subst d
      have hbAB : b ∈ f (choiceProfile P (pairSet a b)) :=
        zProfile_choice_contraction f hM P (tripleSet a b c) (pairSet a b)
          (pair_subset_triple_left a b c) (mem_pair_right a b) hd
      have haPair' : a ∈ f (choiceProfile P (pairSet a b)) := by
        simpa [choiceProfile] using haPair
      have hsingle := resolute_eq_singleton_of_mem (f := f) hf_res haPair'
      have : b = a := by
        rw [hsingle] at hbAB
        simpa using hbAB
      exact hab_eq this.symm
    · subst d
      have hcBC : c ∈ f (choiceProfile P (pairSet b c)) :=
        zProfile_choice_contraction f hM P (tripleSet a b c) (pairSet b c)
          (pair_subset_triple_mid_right a b c) (mem_pair_right b c) hd
      have hbPair' : b ∈ f (choiceProfile P (pairSet b c)) := by
        simpa [choiceProfile] using hbPair
      have hsingle := resolute_eq_singleton_of_mem (f := f) hf_res hbPair'
      have : c = b := by
        rw [hsingle] at hcBC
        simpa using hcBC
      exact hbc_eq this.symm

private noncomputable def revealedSWF [Fintype N] [Nonempty N] [Fintype A]
    (f : VotingRule N A) (hf_total : IsTotal f) (hf_res : Resolute f)
    (hU : Unanimity f) (hM : Monotonicity f) : SWF N A :=
  fun P =>
    { rel := revealedRel f P
      prop :=
        { reflexive := fun _ => Or.inl rfl
          transitive := revealedRel_trans f hf_total hf_res hU hM P
          total := revealedRel_total f hf_total hU hM P } }

private theorem revealedSWF_unanimity [Fintype N] [Nonempty N] [Fintype A]
    (f : VotingRule N A) (hf_total : IsTotal f) (hf_res : Resolute f)
    (hU : Unanimity f) (hM : Monotonicity f) :
    SWF.Unanimity (revealedSWF f hf_total hf_res hU hM) := by
  classical
  intro P a b hab
  have hne : a ≠ b := by
    intro h
    subst b
    let i : N := Classical.ofNonempty
    exact (Prefers.asymm P i (hab i)) (hab i)
  have hnotB : b ∉ f (choiceProfile P (pairSet a b)) := by
    apply hU
    intro i
    simpa [choiceProfile] using
      (zProfile_prefers_inside P P (pairSet a b)
        (mem_pair_left a b) (mem_pair_right a b) i).mpr (hab i)
  constructor
  · right
    rcases hf_total (choiceProfile P (pairSet a b)) with ⟨c, hc⟩
    have hcPair : c ∈ pairSet a b := by
      simpa [choiceProfile] using
        zProfile_choice_mem f hU hM P P (pairSet a b) (pairSet_nonempty a b) hc
    rcases hcPair with hcA | hcB
    · simpa [hcA] using hc
    · exact False.elim (hnotB (by simpa [hcB] using hc))
  · intro hba
    rcases hba with hEq | hb
    · exact hne hEq.symm
    · have hnotB' : b ∉ f (choiceProfile P (pairSet b a)) := by
        apply hU
        intro i
        simpa [choiceProfile] using
          (zProfile_prefers_inside P P (pairSet b a)
            (mem_pair_right b a) (mem_pair_left b a) i).mpr (hab i)
      exact hnotB' hb

private theorem binary_choice_preserved [Fintype N] [Fintype A]
    (f : VotingRule N A) (hM : Monotonicity f)
    {P Q : Profile N A} {a b : A} (hne : a ≠ b)
    (hab : ∀ i : N, Prefers P i a b ↔ Prefers Q i a b)
    (ha : a ∈ f (choiceProfile P (pairSet a b))) :
    a ∈ f (choiceProfile Q (pairSet a b)) := by
  classical
  exact hM (choiceProfile P (pairSet a b)) (choiceProfile Q (pairSet a b)) a ha (by
    dsimp [choiceProfile]
    intro i x
    constructor
    · intro hax
      by_cases hxa : x = a
      · subst x
        exact False.elim ((Prefers.asymm (zProfile P P (pairSet a b)) i hax) hax)
      by_cases hxb : x = b
      · subst x
        have hP := (zProfile_prefers_inside P P (pairSet a b)
          (mem_pair_left a b) (mem_pair_right a b) i).mp hax
        have hQ := (hab i).mp hP
        exact (zProfile_prefers_inside Q Q (pairSet a b)
          (mem_pair_left a b) (mem_pair_right a b) i).mpr hQ
      · exact zProfile_prefers_inside_outside Q Q (pairSet a b)
          (mem_pair_left a b) (by intro hx; exact hx.elim hxa hxb) i
    · intro hxa
      by_cases hxa_eq : x = a
      · subst x
        exact False.elim ((Prefers.asymm (zProfile Q Q (pairSet a b)) i hxa) hxa)
      by_cases hxb : x = b
      · subst x
        have hQba := (zProfile_prefers_inside Q Q (pairSet a b)
          (mem_pair_right a b) (mem_pair_left a b) i).mp hxa
        have hnotQab : ¬ Prefers Q i a b := Prefers.asymm Q i hQba
        have hnotPab : ¬ Prefers P i a b := fun hPab => hnotQab ((hab i).mp hPab)
        have hPba : Prefers P i b a := by
          rcases Prefers.total_of_ne P i hne with hPab | hPba
          · exact False.elim (hnotPab hPab)
          · exact hPba
        exact (zProfile_prefers_inside P P (pairSet a b)
          (mem_pair_right a b) (mem_pair_left a b) i).mpr hPba
      · have hax := zProfile_prefers_inside_outside Q Q (pairSet a b)
          (mem_pair_left a b) (by intro hx; exact hx.elim hxa_eq hxb) i
        exact False.elim ((Prefers.asymm (zProfile Q Q (pairSet a b)) i hax) hxa))

private theorem revealedSWF_iia [Fintype N] [Nonempty N] [Fintype A]
    (f : VotingRule N A) (hf_total : IsTotal f) (hf_res : Resolute f)
    (hU : Unanimity f) (hM : Monotonicity f) :
    SWF.IIA (revealedSWF f hf_total hf_res hU hM) := by
  classical
  intro P Q a b hab
  by_cases hne : a = b
  · subst b
    simp [revealedSWF, revealedRel]
  · constructor
    · intro h
      rcases h with hEq | ha
      · exact Or.inl hEq
      · exact Or.inr (binary_choice_preserved f hM hne hab ha)
    · intro h
      rcases h with hEq | ha
      · exact Or.inl hEq
      · exact Or.inr (binary_choice_preserved f hM hne
          (fun i => (hab i).symm) ha)

/-! ### Intermediate theorems -/

/-- **Muller-Satterthwaite Theorem**: if there are at least three alternatives,
every resolute, unanimous, and monotonic voting rule on a finite nonempty voter
set is dictatorial. [MSZ 21.27] -/
theorem muller_satterthwaite [Fintype N] [Nonempty N] [Fintype A] [Nonempty A]
    (hA : Fintype.card A ≥ 3)
    (f : VotingRule N A) (hf_total : IsTotal f) (hf_res : Resolute f)
    (hU : Unanimity f) (hM : Monotonicity f) :
    Dictatorial f := by
  classical
  let F : SWF N A := revealedSWF f hf_total hf_res hU hM
  have hFdict : SWF.Dictatorial F :=
    arrow_impossibility hA F
      (by simpa [F] using revealedSWF_unanimity f hf_total hf_res hU hM)
      (by simpa [F] using revealedSWF_iia f hf_total hf_res hU hM)
  rcases hFdict with ⟨i, hdict⟩
  refine ⟨i, ?_⟩
  intro P
  let t : A := topChoice P i
  rcases hf_total P with ⟨w, hw⟩
  have hwt : w = t := by
    by_contra hne
    have htw : Prefers P i t w := topChoice_topRank P i w hne
    have hstrict := hdict P t w htw
    have hwPair : w ∈ f (choiceProfile P (pairSet w t)) := by
      simpa [choiceProfile] using
        monotonic_zProfile f hM P P (pairSet w t) (mem_pair_left w t) hw
    have hrel : revealedRel f P w t := Or.inr hwPair
    exact hstrict.2 hrel
  have hsingle := resolute_eq_singleton_of_mem (f := f) hf_res hw
  simpa [t, hwt] using hsingle

/-- Strategy-proofness implies monotonicity for finite voter sets. [MSZ 21.35] -/
theorem strategyproof_monotonic [Fintype N] [Fintype A]
    (f : VotingRule N A) (hf_res : Resolute f)
    (hSP : ResoluteStrategyproofness f hf_res) :
    Monotonicity f := by
  classical
  intro P Q a ha hLift
  have hAll : ∀ S : Finset N, a ∈ f (hybridProfile P Q S) := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
        simpa [hybridProfile] using ha
    | insert i S hi ih =>
        exact strategyproof_insert_preserves_choice f hf_res hSP hLift hi ih
  simpa [hybridProfile] using hAll (Finset.univ : Finset N)

/-! ### Gibbard-Satterthwaite theorem -/

/-- **Gibbard-Satterthwaite Theorem**: if there are at least three alternatives,
every resolute, nonmanipulable, and unanimous voting rule on a finite nonempty
voter set is dictatorial. [MSZ 21.39, Gibbard 1973, Satterthwaite 1975] -/
theorem gibbard_satterthwaite [Fintype N] [Nonempty N] [Fintype A] [Nonempty A]
    (hA : Fintype.card A ≥ 3)
    (f : VotingRule N A) (hf_total : IsTotal f) (hf_res : Resolute f)
    (hU : Unanimity f) (hSP : ResoluteStrategyproofness f hf_res) :
    Dictatorial f := by
  exact muller_satterthwaite hA f hf_total hf_res hU
    (strategyproof_monotonic f hf_res hSP)

end Voting
end SocialChoice
