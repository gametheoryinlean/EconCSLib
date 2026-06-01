/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.SocialChoice.Voting.VotingRules
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.Minimal
import Mathlib.Order.SetNotation

/-!
# EconCSLib.SocialChoice.Voting.Decisive

Decisive coalitions and the decisive-coalitions proof of Arrow's impossibility
theorem over strict voting profiles.

This file records the public decisive-coalition vocabulary for the strict
ranked-ballot voting domain. The proof route is the standard one:

1. unanimity implies the grand coalition is decisive;
2. weak decisiveness for one ordered pair spreads to decisiveness for all pairs;
3. any decisive coalition of size at least two has a strictly smaller nonempty
   decisive subcoalition;
4. a minimal decisive coalition is a singleton;
5. the singleton voter is a dictator.
-/

namespace SocialChoice
namespace Voting

variable {N A : Type*}

/-- A coalition is decisive for `a` over `b` if unanimous strict support inside
the coalition forces the social strict preference `a ≻ b`. -/
def IsDecisiveFor [Fintype N] [Fintype A]
    (F : SWF N A) (C : Set N) (a b : A) : Prop :=
  ∀ P : Profile N A, (∀ i ∈ C, Prefers P i a b) → strict (F P) a b

/-- A coalition is decisive if it is decisive for every ordered pair of
alternatives. -/
def IsDecisive [Fintype N] [Fintype A] (F : SWF N A) (C : Set N) : Prop :=
  ∀ a b, IsDecisiveFor F C a b

/-- An individual is a dictator exactly when their singleton coalition is
decisive. -/
def SWF.IsDictator [Fintype N] [Fintype A] (F : SWF N A) (i : N) : Prop :=
  IsDecisive F {i}

theorem unanimity_univ_isDecisive [Fintype N] [Fintype A]
    {F : SWF N A} (h : SWF.Unanimity F) : IsDecisive F Set.univ := by
  intro a b P hP
  exact h P a b (fun i => hP i (by simp))

theorem singleton_unanimity_isDictator [Fintype N] [Fintype A] [Subsingleton N]
    {F : SWF N A} (h : SWF.Unanimity F) (i : N) :
    F.IsDictator i := by
  intro a b P hi
  apply h
  intro j
  rw [← Subsingleton.allEq i j]
  exact hi i rfl

theorem singleton_unanimity_dictatorial [Fintype N] [Fintype A]
    [Subsingleton N] [Nonempty N] {F : SWF N A}
    (h : SWF.Unanimity F) : SWF.Dictatorial F := by
  refine ⟨(Classical.ofNonempty : N), ?_⟩
  intro P a b hab
  apply h
  intro j
  rw [← Subsingleton.allEq (Classical.ofNonempty : N) j]
  exact hab

/-- Weak decisiveness tests a coalition against a complement unanimously
supporting the opposite strict ranking. -/
def IsWeaklyDecisiveFor [Fintype N] [Fintype A]
    (F : SWF N A) (C : Set N) (a b : A) : Prop :=
  ∀ P : Profile N A,
    (∀ i ∈ C, Prefers P i a b) ∧ (∀ i ∉ C, Prefers P i b a) →
      strict (F P) a b

theorem isWeaklyDecisiveFor_of_isDecisiveFor [Fintype N] [Fintype A]
    {F : SWF N A} {C : Set N} {a b : A}
    (h : IsDecisiveFor F C a b) : IsWeaklyDecisiveFor F C a b := by
  intro P hP
  exact h P hP.left

theorem iia_strict [Fintype N] [Fintype A] {F : SWF N A} (hF : SWF.IIA F)
    {P Q : Profile N A} {a b : A}
    (hab : ∀ i, Prefers P i a b ↔ Prefers Q i a b)
    (hba : ∀ i, Prefers P i b a ↔ Prefers Q i b a) :
    strict (F P) a b ↔ strict (F Q) a b := by
  simp [strict, hF P Q a b hab, hF P Q b a hba]

private theorem prefers_trans [Fintype N] [Fintype A] (P : Profile N A) (i : N)
    {a b c : A} (hab : Prefers P i a b) (hbc : Prefers P i b c) :
    Prefers P i a c := by
  unfold Prefers BallotPrefers at *
  letI := P.pref i
  exact lt_trans hab hbc

/-! ### Strict ballot surgery for the decisive-coalitions proof -/

private noncomputable def defaultBallot (A : Type*) [Fintype A] : LinearOrder A :=
  ballotFromInjective (inferInstance : LinearOrder (Fin (Fintype.card A)))
    (Fintype.equivFin A) (Fintype.equivFin A).injective

private noncomputable def betweenKey [Fintype A] (r : LinearOrder A)
    (x y z a : A) : Nat :=
  if a = x then 0 else if a = y then 1 else if a = z then 2 else rank r a + 3

private theorem betweenKey_injective [Fintype A] (r : LinearOrder A)
    {x y z : A} (_hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    Function.Injective (betweenKey r x y z) := by
  classical
  intro a b h
  unfold betweenKey at h
  by_cases hax : a = x <;> by_cases hbx : b = x
  · simp_all
  · by_cases hby : b = y <;> by_cases hbz : b = z <;> simp_all
  · by_cases hay : a = y <;> by_cases haz : a = z <;> simp_all
  · by_cases hay : a = y <;> by_cases hby : b = y
    · simp_all
    · by_cases hbz : b = z <;> simp_all
    · by_cases haz : a = z <;> simp_all
    · by_cases haz : a = z <;> by_cases hbz : b = z
      · simp_all
      · simp_all
      · simp_all
      · simp_all
        exact rank_injective r (by omega)

private noncomputable def betweenBallot [Fintype A] (r : LinearOrder A)
    {x y z : A} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    LinearOrder A :=
  ballotFromInjective (inferInstance : LinearOrder Nat) (betweenKey r x y z)
    (betweenKey_injective r hxy hxz hyz)

private theorem betweenBallot_xy [Fintype A] (r : LinearOrder A)
    {x y z : A} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    BallotPrefers (betweenBallot r hxy hxz hyz) x y := by
  simp [betweenBallot, betweenKey, Ne.symm hxy]

private theorem betweenBallot_yz [Fintype A] (r : LinearOrder A)
    {x y z : A} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    BallotPrefers (betweenBallot r hxy hxz hyz) y z := by
  simp [betweenBallot, betweenKey, Ne.symm hxy, Ne.symm hxz, Ne.symm hyz]

private theorem betweenBallot_xz [Fintype A] (r : LinearOrder A)
    {x y z : A} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    BallotPrefers (betweenBallot r hxy hxz hyz) x z := by
  simp [betweenBallot, betweenKey, Ne.symm hxz, Ne.symm hyz]

private noncomputable def topKey [Fintype A] (r : LinearOrder A) (y a : A) : Nat :=
  if a = y then 0 else rank r a + 1

private theorem topKey_injective [Fintype A] (r : LinearOrder A) (y : A) :
    Function.Injective (topKey r y) := by
  classical
  intro a b h
  unfold topKey at h
  by_cases hay : a = y <;> by_cases hby : b = y
  · simp_all
  · simp_all
  · simp_all
  · simp_all
    exact rank_injective r (by omega)

private noncomputable def topBallot [Fintype A] (r : LinearOrder A) (y : A) :
    LinearOrder A :=
  ballotFromInjective (inferInstance : LinearOrder Nat) (topKey r y)
    (topKey_injective r y)

private theorem topBallot_top [Fintype A] (r : LinearOrder A) {y a : A}
    (h : a ≠ y) : BallotPrefers (topBallot r y) y a := by
  simp [topBallot, topKey, h]

private theorem topBallot_preserves [Fintype A] (r : LinearOrder A) {y a b : A}
    (ha : a ≠ y) (hb : b ≠ y) :
    BallotPrefers (topBallot r y) a b ↔ BallotPrefers r a b := by
  simp [topBallot, topKey, ha, hb, rank_lt_iff]

private noncomputable def bottomKey [Fintype A] (r : LinearOrder A) (y a : A) : Nat :=
  if a = y then Fintype.card A + 1 else rank r a

private theorem bottomKey_injective [Fintype A] (r : LinearOrder A) (y : A) :
    Function.Injective (bottomKey r y) := by
  classical
  intro a b h
  unfold bottomKey at h
  by_cases hay : a = y <;> by_cases hby : b = y
  · simp_all
  · simp_all
    have hb := rank_lt_card r b
    omega
  · simp_all
    have ha := rank_lt_card r a
    omega
  · simp_all
    exact rank_injective r h

private noncomputable def bottomBallot [Fintype A] (r : LinearOrder A) (y : A) :
    LinearOrder A :=
  ballotFromInjective (inferInstance : LinearOrder Nat) (bottomKey r y)
    (bottomKey_injective r y)

private theorem bottomBallot_bottom [Fintype A] (r : LinearOrder A) {y a : A}
    (h : a ≠ y) : BallotPrefers (bottomBallot r y) a y := by
  simp [bottomBallot, bottomKey, h]
  have ha := rank_lt_card r a
  omega

private theorem bottomBallot_preserves [Fintype A] (r : LinearOrder A) {y a b : A}
    (ha : a ≠ y) (hb : b ≠ y) :
    BallotPrefers (bottomBallot r y) a b ↔ BallotPrefers r a b := by
  simp [bottomBallot, bottomKey, ha, hb, rank_lt_iff]

private noncomputable def modifiedForwardProfile [Fintype N] [Fintype A]
    (P : Profile N A) (C : Set N) (x y z : A)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) : Profile N A := by
  classical
  exact
    { pref := fun i =>
        if i ∈ C then
          betweenBallot (P.pref i) hxy hxz hyz
        else
          topBallot (P.pref i) y }

private theorem modifiedForwardProfile_spec [Fintype N] [Fintype A]
    (P : Profile N A) (C : Set N)
    {x y z : A} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hC : ∀ i ∈ C, Prefers P i x z) :
    ∀ i,
      (Prefers P i x z ↔ Prefers (modifiedForwardProfile P C x y z hxy hxz hyz) i x z) ∧
      (Prefers P i z x ↔ Prefers (modifiedForwardProfile P C x y z hxy hxz hyz) i z x) ∧
      (i ∈ C → Prefers (modifiedForwardProfile P C x y z hxy hxz hyz) i x y ∧
          Prefers (modifiedForwardProfile P C x y z hxy hxz hyz) i y z) ∧
      (i ∉ C → Prefers (modifiedForwardProfile P C x y z hxy hxz hyz) i y x ∧
          Prefers (modifiedForwardProfile P C x y z hxy hxz hyz) i y z) := by
  classical
  intro i
  by_cases hi : i ∈ C
  · simp [modifiedForwardProfile, hi, Prefers]
    constructor
    · constructor
      · intro _
        exact betweenBallot_xz (P.pref i) hxy hxz hyz
      · intro _
        exact hC i hi
    constructor
    · constructor
      · intro hzxi
        exact False.elim ((Prefers.asymm P i (hC i hi)) hzxi)
      · intro hzxi
        exact False.elim
          ((BallotPrefers.asymm _ (betweenBallot_xz (P.pref i) hxy hxz hyz)) hzxi)
    exact ⟨betweenBallot_xy (P.pref i) hxy hxz hyz,
      betweenBallot_yz (P.pref i) hxy hxz hyz⟩
  · have hx_ne_y : x ≠ y := hxy
    have hz_ne_y : z ≠ y := Ne.symm hyz
    simp [modifiedForwardProfile, hi, Prefers, topBallot_preserves, hx_ne_y, hz_ne_y,
      topBallot_top]

private noncomputable def modifiedBackwardProfile [Fintype N] [Fintype A]
    (P : Profile N A) (C : Set N) (x y z : A)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) : Profile N A := by
  classical
  exact
    { pref := fun i =>
        if i ∈ C then
          betweenBallot (P.pref i) hxy hxz hyz
        else
          bottomBallot (P.pref i) y }

private theorem modifiedBackwardProfile_spec [Fintype N] [Fintype A]
    (P : Profile N A) (C : Set N)
    {x y z : A} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hC : ∀ i ∈ C, Prefers P i x z) :
    ∀ i,
      (Prefers P i x z ↔ Prefers (modifiedBackwardProfile P C x y z hxy hxz hyz) i x z) ∧
      (Prefers P i z x ↔ Prefers (modifiedBackwardProfile P C x y z hxy hxz hyz) i z x) ∧
      (i ∈ C → Prefers (modifiedBackwardProfile P C x y z hxy hxz hyz) i x y ∧
          Prefers (modifiedBackwardProfile P C x y z hxy hxz hyz) i y z) ∧
      (i ∉ C → Prefers (modifiedBackwardProfile P C x y z hxy hxz hyz) i x y ∧
          Prefers (modifiedBackwardProfile P C x y z hxy hxz hyz) i z y) := by
  classical
  intro i
  by_cases hi : i ∈ C
  · simp [modifiedBackwardProfile, hi, Prefers]
    constructor
    · constructor
      · intro _
        exact betweenBallot_xz (P.pref i) hxy hxz hyz
      · intro _
        exact hC i hi
    constructor
    · constructor
      · intro hzxi
        exact False.elim ((Prefers.asymm P i (hC i hi)) hzxi)
      · intro hzxi
        exact False.elim
          ((BallotPrefers.asymm _ (betweenBallot_xz (P.pref i) hxy hxz hyz)) hzxi)
    exact ⟨betweenBallot_xy (P.pref i) hxy hxz hyz,
      betweenBallot_yz (P.pref i) hxy hxz hyz⟩
  · have hx_ne_y : x ≠ y := hxy
    have hz_ne_y : z ≠ y := Ne.symm hyz
    simp [modifiedBackwardProfile, hi, Prefers, bottomBallot_preserves, hx_ne_y, hz_ne_y,
      bottomBallot_bottom]

private noncomputable def acyclicBallot (A : Type*) [Fintype A]
    {x y z : A} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) : LinearOrder A :=
  betweenBallot (defaultBallot A) hxy hxz hyz

private theorem acyclicBallot_spec [Fintype A]
    {x y z : A} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    BallotPrefers (acyclicBallot A hxy hxz hyz) x y ∧
      BallotPrefers (acyclicBallot A hxy hxz hyz) y z := by
  exact ⟨betweenBallot_xy (defaultBallot A) hxy hxz hyz,
    betweenBallot_yz (defaultBallot A) hxy hxz hyz⟩

private def tripartition {N : Type*} (A B C : Set N) : Prop :=
  (A ∩ B = ∅) ∧ (A ∩ C = ∅) ∧ (B ∩ C = ∅) ∧ (A ∪ B ∪ C = Set.univ)

private theorem tripartition_lemma {N : Type*} {A B C : Set N}
    (h : tripartition A B C) :
    ∀ i : N,
      i ∈ A ∪ B ∪ C ∧
      (i ∈ A ↔ i ∉ B ∧ i ∉ C) ∧
      (i ∈ B ↔ i ∉ A ∧ i ∉ C) ∧
      (i ∈ C ↔ i ∉ A ∧ i ∉ B) := by
  intro i
  by_cases hA : i ∈ A <;> by_cases hB : i ∈ B <;> by_cases hC : i ∈ C <;>
    simp_all [tripartition]
  · have := Set.mem_inter hA hB; simp_all
  · have := Set.mem_inter hA hB; simp_all
  · have := Set.mem_inter hA hC; simp_all
  · have := Set.mem_inter hB hC; simp_all
  · have hnot : i ∉ A ∪ B ∪ C := by
      intro hmem
      rcases hmem with (hmem | hmem) | hmem <;> contradiction
    rw [h.2.2.2] at hnot
    exact hnot trivial

private noncomputable def condorcetProfile [Fintype N] [Fintype A]
    (S T _U : Set N) (x y z : A)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) : Profile N A := by
  classical
  exact
    { pref := fun i =>
        if i ∈ S then
          acyclicBallot A hxy hxz hyz
        else if i ∈ T then
          acyclicBallot A hyz (Ne.symm hxy) (Ne.symm hxz)
        else
          acyclicBallot A (Ne.symm hxz) (Ne.symm hyz) hxy }

private theorem condorcetProfile_spec [Fintype N] [Fintype A]
    {S T U : Set N}
    {x y z : A} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hSTU : tripartition S T U) :
    ∀ i,
      (i ∈ S → Prefers (condorcetProfile S T U x y z hxy hxz hyz) i x y ∧
          Prefers (condorcetProfile S T U x y z hxy hxz hyz) i y z) ∧
      (i ∈ T → Prefers (condorcetProfile S T U x y z hxy hxz hyz) i y z ∧
          Prefers (condorcetProfile S T U x y z hxy hxz hyz) i z x) ∧
      (i ∈ U → Prefers (condorcetProfile S T U x y z hxy hxz hyz) i z x ∧
          Prefers (condorcetProfile S T U x y z hxy hxz hyz) i x y) := by
  classical
  intro i
  have htri := tripartition_lemma hSTU i
  by_cases hS : i ∈ S
  · constructor
    · intro _
      simpa [condorcetProfile, Prefers, hS] using acyclicBallot_spec hxy hxz hyz
    constructor
    · intro hT
      exact False.elim ((htri.2.2.1.mp hT).1 hS)
    · intro hU
      exact False.elim ((htri.2.2.2.mp hU).1 hS)
  · by_cases hT : i ∈ T
    · have hnotU : i ∉ U := (htri.2.2.1.mp hT).2
      constructor
      · intro hS'
        exact False.elim (hS hS')
      constructor
      · intro _
        simpa [condorcetProfile, Prefers, hS, hT] using
          acyclicBallot_spec hyz (Ne.symm hxy) (Ne.symm hxz)
      · intro hU'
        exact False.elim (hnotU hU')
    · have hU : i ∈ U := by
        exact (htri.2.2.2).mpr ⟨hS, hT⟩
      constructor
      · intro hS'
        exact False.elim (hS hS')
      constructor
      · intro hT'
        exact False.elim (hT hT')
      · intro _
        simpa [condorcetProfile, Prefers, hS, hT] using
          acyclicBallot_spec (Ne.symm hxz) (Ne.symm hyz) hxy

private theorem decisive_spread_forward [Fintype N] [Fintype A]
    {F : SWF N A} (hU : SWF.Unanimity F) (hIIA : SWF.IIA F)
    {C : Set N} {x y z : A} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (h : IsWeaklyDecisiveFor F C x y) :
    IsDecisiveFor F C x z := by
  classical
  intro P hP
  let Q := modifiedForwardProfile P C x y z hxy hxz hyz
  have hQ := modifiedForwardProfile_spec P C hxy hxz hyz hP
  have hxz : ∀ i, Prefers P i x z ↔ Prefers Q i x z := fun i => (hQ i).1
  have hzx : ∀ i, Prefers P i z x ↔ Prefers Q i z x := fun i => (hQ i).2.1
  rw [iia_strict hIIA hxz hzx]
  exact strict_transitive (F Q).prop.transitive
    (h Q ⟨fun i hi => (hQ i).2.2.1 hi |>.1,
      fun i hi => (hQ i).2.2.2 hi |>.1⟩)
    (hU Q y z (fun i => by
      by_cases hi : i ∈ C
      · exact (hQ i).2.2.1 hi |>.2
      · exact (hQ i).2.2.2 hi |>.2))

private theorem decisive_spread_backward [Fintype N] [Fintype A]
    {F : SWF N A} (hU : SWF.Unanimity F) (hIIA : SWF.IIA F)
    {C : Set N} {x y z : A} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (h : IsWeaklyDecisiveFor F C x y) :
    IsDecisiveFor F C z y := by
  classical
  intro P hP
  have hzx : z ≠ x := Ne.symm hxz
  have hzy : z ≠ y := Ne.symm hyz
  have hxy' : x ≠ y := hxy
  let Q := modifiedBackwardProfile P C z x y hzx hzy hxy'
  have hQ := modifiedBackwardProfile_spec P C hzx hzy hxy' hP
  have hzy_iff : ∀ i, Prefers P i z y ↔ Prefers Q i z y := fun i => (hQ i).1
  have hyz_iff : ∀ i, Prefers P i y z ↔ Prefers Q i y z := fun i => (hQ i).2.1
  rw [iia_strict hIIA hzy_iff hyz_iff]
  exact strict_transitive (F Q).prop.transitive
    (hU Q z x (fun i => by
      by_cases hi : i ∈ C
      · exact (hQ i).2.2.1 hi |>.1
      · exact (hQ i).2.2.2 hi |>.1))
    (h Q ⟨fun i hi => (hQ i).2.2.1 hi |>.2,
      fun i hi => (hQ i).2.2.2 hi |>.2⟩)

private theorem decisive_spread_symmetric [Fintype N] [Fintype A]
    {F : SWF N A} (hU : SWF.Unanimity F) (hIIA : SWF.IIA F)
    {C : Set N} {x y z : A} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (h : IsWeaklyDecisiveFor F C x y) :
    IsDecisiveFor F C y x := by
  have h1 := decisive_spread_forward hU hIIA hxy hxz hyz h
  have h2 := isWeaklyDecisiveFor_of_isDecisiveFor h1
  have h3 := decisive_spread_backward hU hIIA hxz hxy (Ne.symm hyz) h2
  have h4 := isWeaklyDecisiveFor_of_isDecisiveFor h3
  exact decisive_spread_forward hU hIIA hyz (Ne.symm hxy) (Ne.symm hxz) h4

private theorem decisive_spread_strengthen [Fintype N] [Fintype A]
    {F : SWF N A} (hU : SWF.Unanimity F) (hIIA : SWF.IIA F)
    {C : Set N} {x y z : A} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (h : IsWeaklyDecisiveFor F C x y) :
    IsDecisiveFor F C x y := by
  apply decisive_spread_symmetric hU hIIA (Ne.symm hxy) hyz hxz
  apply isWeaklyDecisiveFor_of_isDecisiveFor
  exact decisive_spread_symmetric hU hIIA hxy hxz hyz h

private theorem decisive_for_refl [Fintype N] [Fintype A]
    {F : SWF N A} {C : Set N} (hC : Set.Nonempty C) (x : A) :
    IsDecisiveFor F C x x := by
  intro P hP
  rcases hC with ⟨i, hi⟩
  exact False.elim ((Prefers.asymm P i (hP i hi)) (hP i hi))

theorem decisive_spread [Fintype N] [Fintype A]
    {F : SWF N A} (hU : SWF.Unanimity F) (hIIA : SWF.IIA F)
    {C : Set N} {x y z : A} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hC : Set.Nonempty C) (h : IsWeaklyDecisiveFor F C x y) :
    IsDecisive F C := by
  intro s t
  by_cases hst : s = t
  · subst hst
    exact decisive_for_refl hC s
  by_cases hxs : x = s <;> by_cases hxt : x = t <;>
    by_cases hys : y = s <;> by_cases hyt : y = t <;> simp_all
  · exact decisive_spread_strengthen hU hIIA hst hxz hyz h
  · exact decisive_spread_forward hU hIIA hxy hst hyt h
  · subst hxt
    subst hys
    exact decisive_spread_symmetric hU hIIA hxy hxz hyz h
  · subst hxt
    have h1 := decisive_spread_symmetric hU hIIA hxy hxz hyz h
    have h2 := isWeaklyDecisiveFor_of_isDecisiveFor h1
    exact decisive_spread_backward hU hIIA hyt hys hxs h2
  · subst hys
    have h1 := decisive_spread_symmetric hU hIIA hxs hxt hst h
    have h2 := isWeaklyDecisiveFor_of_isDecisiveFor h1
    exact decisive_spread_forward hU hIIA (fun a => hxs (Eq.symm a)) hst hxt h2
  · exact decisive_spread_backward hU hIIA hxt hxs hys h
  · have h1 := decisive_spread_forward hU hIIA hxy hxt hyt h
    have h2 := isWeaklyDecisiveFor_of_isDecisiveFor h1
    exact decisive_spread_backward hU hIIA hxt hxs (fun a => hst (Eq.symm a)) h2

def exists_nonempty_decisive_of_size [Fintype N] [Fintype A]
    (F : SWF N A) (n : Nat) : Prop :=
  ∃ C : Set N, C.Nonempty ∧ IsDecisive F C ∧ C.ncard = n

theorem exists_minimal_decisive_coalition [Fintype N] [Nonempty N] [Fintype A]
    {F : SWF N A} (hU : SWF.Unanimity F) :
    ∃ n, Minimal (exists_nonempty_decisive_of_size F) n := by
  classical
  apply exists_minimal_of_wellFoundedLT
  refine ⟨Fintype.card N, Set.univ, ?_, ?_, ?_⟩
  · exact ⟨Classical.ofNonempty, trivial⟩
  · exact unanimity_univ_isDecisive hU
  · simp [Set.ncard_univ, Nat.card_eq_fintype_card]

private theorem decisive_contraction_lemma [Fintype N] [Fintype A]
    {F : SWF N A} (hU : SWF.Unanimity F) (hIIA : SWF.IIA F)
    {x y z : A} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    {S T U : Set N} (hS_nonempty : Set.Nonempty S) (hSTU : tripartition S T U)
    {P₀ : Profile N A}
    (hS : ∀ i ∈ S, Prefers P₀ i x y ∧ Prefers P₀ i y z)
    (hT : ∀ i ∈ T, Prefers P₀ i y z ∧ Prefers P₀ i z x)
    (hUprof : ∀ i ∈ U, Prefers P₀ i z x ∧ Prefers P₀ i x y)
    (hSoc : strict (F P₀) x z) :
    IsDecisive F S := by
  apply decisive_spread hU hIIA hxz hxy (Ne.symm hyz) hS_nonempty
  intro P hP
  have hP₀xz : ∀ i ∈ S, Prefers P₀ i x z ∧ Prefers P i x z := by
    intro i hi
    exact ⟨prefers_trans P₀ i (hS i hi).1 (hS i hi).2, hP.1 i hi⟩
  have hP₀zx : ∀ i ∉ S, Prefers P₀ i z x ∧ Prefers P i z x := by
    intro i hi
    constructor
    · by_cases hit : i ∈ T
      · exact (hT i hit).2
      · have hiu : i ∈ U := (tripartition_lemma hSTU i).2.2.2.mpr ⟨hi, hit⟩
        exact (hUprof i hiu).1
    · exact hP.2 i hi
  have hiffxz : ∀ i, Prefers P₀ i x z ↔ Prefers P i x z := by
    intro i
    by_cases hi : i ∈ S
    · exact ⟨fun _ => (hP₀xz i hi).2, fun _ => (hP₀xz i hi).1⟩
    · exact ⟨fun hp => False.elim ((Prefers.asymm P₀ i (hP₀zx i hi).1) hp),
        fun hp => False.elim ((Prefers.asymm P i (hP₀zx i hi).2) hp)⟩
  have hiffzx : ∀ i, Prefers P₀ i z x ↔ Prefers P i z x := by
    intro i
    by_cases hi : i ∈ S
    · exact ⟨fun hp => False.elim ((Prefers.asymm P₀ i (hP₀xz i hi).1) hp),
        fun hp => False.elim ((Prefers.asymm P i (hP₀xz i hi).2) hp)⟩
    · exact ⟨fun _ => (hP₀zx i hi).2, fun _ => (hP₀zx i hi).1⟩
  rw [← iia_strict hIIA hiffxz hiffzx]
  exact hSoc

theorem decisive_contraction [Fintype N] [Fintype A]
    {F : SWF N A} (h0 : ∃ x y z : A, x ≠ y ∧ x ≠ z ∧ y ≠ z)
    {C : Set N} (hCdec : IsDecisive F C) (hCcard : 2 ≤ C.ncard)
    (hU : SWF.Unanimity F) (hIIA : SWF.IIA F) :
    ∃ S : Set N, S.Nonempty ∧ S < C ∧ IsDecisive F S := by
  classical
  have hC_nonempty : C.Nonempty := by
    rw [← Set.ncard_pos]
    omega
  obtain ⟨i, hiC⟩ := hC_nonempty
  have hC_one_lt : 1 < C.ncard := by omega
  obtain ⟨j, hjC, hji⟩ := Set.exists_ne_of_one_lt_ncard hC_one_lt i
  let S : Set N := {i}
  let T : Set N := C \ S
  have hS_nonempty : Set.Nonempty S := by
    exact ⟨i, by simp [S]⟩
  have hT_nonempty : Set.Nonempty T := by
    refine ⟨j, ?_⟩
    simp [T, S]
    exact ⟨hjC, hji⟩
  have hS_le_C : S ⊆ C := by
    intro k hk
    simp [S] at hk
    rw [hk]
    exact hiC
  have hS_lt_C : S < C := by
    constructor
    · exact hS_le_C
    · intro hCS
      have hjS : j ∈ S := hCS hjC
      simp [S] at hjS
      exact hji hjS
  have triS : tripartition S Cᶜ T := by
    unfold tripartition
    constructor
    · ext k
      simp [S, hiC]
    constructor
    · ext k
      simp [S, T]
    constructor
    · ext k
      constructor
      · intro hk
        exact False.elim (hk.1 hk.2.1)
      · intro hk
        cases hk
    · ext k
      by_cases hkC : k ∈ C <;> by_cases hki : k = i <;> simp [S, T, hkC, hki]
  have triT : tripartition T S Cᶜ := by
    unfold tripartition
    constructor
    · ext k
      simp [S, T]
    constructor
    · ext k
      constructor
      · intro hk
        exact False.elim (hk.2 hk.1.1)
      · intro hk
        cases hk
    constructor
    · ext k
      simp [S, hiC]
    · ext k
      by_cases hkC : k ∈ C <;> by_cases hki : k = i <;> simp [S, T, hkC, hki]
  obtain ⟨x, y, z, hxy, hxz, hyz⟩ := h0
  let P₀ := condorcetProfile S Cᶜ T x y z hxy hxz hyz
  have hP₀ := condorcetProfile_spec (S := S) (T := Cᶜ) (U := T) hxy hxz hyz triS
  let hSprof := fun i hi => (hP₀ i).1 hi
  let hCcompProf := fun i hi => (hP₀ i).2.1 hi
  let hTprof := fun i hi => (hP₀ i).2.2 hi
  by_cases hSoc : strict (F P₀) x z
  · exact ⟨S, hS_nonempty, hS_lt_C,
      decisive_contraction_lemma hU hIIA hxy hxz hyz hS_nonempty triS
        hSprof hCcompProf hTprof hSoc⟩
  · have hxysoc : strict (F P₀) x y := by
      apply hCdec
      intro k hk
      by_cases hkS : k ∈ S
      · exact (hSprof k hkS).1
      · have hkt : k ∈ T := by
          simp [T]
          exact ⟨hk, hkS⟩
        exact (hTprof k hkt).2
    have hzysoc : strict (F P₀) z y := by
      rcases hxysoc with ⟨hxyrel, hnyx⟩
      have hzxrel : F P₀ z x := by
        rcases (F P₀).prop.total x z with hxzrel | hzxrel
        · have hnotnot : ¬¬ F P₀ z x := by
            intro hnzx
            exact hSoc ⟨hxzrel, hnzx⟩
          exact not_not.mp hnotnot
        · exact hzxrel
      have hzyrel : F P₀ z y := (F P₀).prop.transitive hzxrel hxyrel
      have hnyz : ¬ F P₀ y z := by
        intro hyzrel
        have hyxrel : F P₀ y x := (F P₀).prop.transitive hyzrel hzxrel
        exact hnyx hyxrel
      exact ⟨hzyrel, hnyz⟩
    exact ⟨T, hT_nonempty, by
      constructor
      · intro k hk
        exact hk.1
      · intro hCT
        have hiT : i ∈ T := hCT hiC
        exact hiT.2 (by simp [S]), by
      exact decisive_contraction_lemma hU hIIA (Ne.symm hxz) (Ne.symm hyz) hxy
        hT_nonempty triT hTprof hSprof hCcompProf hzysoc⟩

theorem decisive_minimal [Fintype N] [Nonempty N] [Fintype A]
    (h0 : ∃ x y z : A, x ≠ y ∧ x ≠ z ∧ y ≠ z)
    {F : SWF N A} (hU : SWF.Unanimity F) (hIIA : SWF.IIA F) :
    Minimal (exists_nonempty_decisive_of_size F) 1 := by
  classical
  obtain ⟨n, hn⟩ := exists_minimal_decisive_coalition hU
  obtain ⟨C, hCnonempty, hCdec, hCcard⟩ := hn.1
  have hn_ne_zero : n ≠ 0 := by
    rcases hCnonempty with ⟨c, hc⟩
    rw [← hCcard]
    exact Set.ncard_ne_zero_of_mem hc
  have hn_lt_two : n < 2 := by
    apply Classical.not_not.mp
    intro hnot
    simp at hnot
    rw [← hCcard] at hnot
    obtain ⟨C', hC'nonempty, hC'lt, hC'dec⟩ :=
      decisive_contraction h0 hCdec hnot hU hIIA
    have hlt_C' : C'.ncard < C.ncard := Set.ncard_lt_ncard hC'lt
    have hlt : C'.ncard < n := Nat.lt_of_lt_of_eq hlt_C' hCcard
    have hprop : exists_nonempty_decisive_of_size F C'.ncard :=
      ⟨C', hC'nonempty, hC'dec, rfl⟩
    exact (Minimal.not_prop_of_lt hn hlt) hprop
  have hn_eq_one : n = 1 := by
    apply Nat.le_antisymm
    · exact Nat.le_of_lt_succ hn_lt_two
    · exact Nat.one_le_iff_ne_zero.mpr hn_ne_zero
  rw [← hn_eq_one]
  exact hn

/-- Arrow's decisive-coalitions theorem for strict finite voting profiles:
unanimity and IIA imply dictatorship. -/
theorem arrow_of_unanimity_iia [Fintype N] [Nonempty N] [Fintype A]
    (h0 : ∃ x y z : A, x ≠ y ∧ x ≠ z ∧ y ≠ z)
    {F : SWF N A} (h1 : SWF.Unanimity F) (h2 : SWF.IIA F) :
    SWF.Dictatorial F := by
  classical
  obtain ⟨hmin, _⟩ := decisive_minimal h0 h1 h2
  obtain ⟨C, hCnonempty, hCdec, hCcard⟩ := hmin
  obtain ⟨i, hCsingleton⟩ := Set.ncard_eq_one.mp hCcard
  rw [hCsingleton] at hCdec
  refine ⟨i, ?_⟩
  intro P a b hab
  exact hCdec a b P (fun j hj => by
    simp at hj
    rw [hj]
    exact hab)

end Voting
end SocialChoice
