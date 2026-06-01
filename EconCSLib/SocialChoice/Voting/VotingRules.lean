/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.SocialChoice.Voting.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# EconCSLib.SocialChoice.Voting.VotingRules

Concrete voting-rule vocabulary over strict finite profiles.

The main rules in this file are set-valued: ties are represented by multiple
winners in the returned `Finset`.

## Main definitions

* `rank`, `position` — ordinal position of an alternative in a ballot
* `margin`, `MajorityPrefers`, `CondorcetWinner`
* `scoringRule`, `plurality`, `borda`, `veto`
* `copeland`

## Main result

* `condorcet_paradox_possible` — a concrete 3-voter, 3-alternative profile with
  no Condorcet winner
-/

open Classical
open Finset
open scoped BigOperators

namespace SocialChoice
namespace Voting

variable {N A : Type*}

/-! ### Rank and position -/

/-- `rank r a` is the number of alternatives strictly above `a` in ballot `r`. -/
noncomputable def rank [Fintype A] (r : LinearOrder A) (a : A) : Nat :=
  Finset.card (Finset.univ.filter (fun b => BallotPrefers r b a))

/-- The 1-based position of `a` in ballot `r`. -/
noncomputable def position [Fintype A] (r : LinearOrder A) (a : A) : Nat :=
  rank r a + 1

theorem position_eq_rank_succ [Fintype A] (r : LinearOrder A) (a : A) :
    position r a = rank r a + 1 :=
  rfl

theorem rank_lt_card [Fintype A] (r : LinearOrder A) (a : A) :
    rank r a < Fintype.card A := by
  classical
  change (Finset.univ.filter (fun b : A => BallotPrefers r b a)).card <
    (Finset.univ : Finset A).card
  have hsubset :
      Finset.univ.filter (fun b : A => BallotPrefers r b a) ⊂ (Finset.univ : Finset A) := by
    refine (Finset.ssubset_iff_of_subset
      (Finset.filter_subset (s := (Finset.univ : Finset A))
        (p := fun b => BallotPrefers r b a))).2 ?_
    refine ⟨a, by simp, ?_⟩
    simp [BallotPrefers]
  simpa [rank] using Finset.card_lt_card hsubset

theorem position_le_card [Fintype A] (r : LinearOrder A) (a : A) :
    position r a ≤ Fintype.card A := by
  simpa [position, Nat.succ_eq_add_one] using Nat.succ_le_of_lt (rank_lt_card r a)

theorem rank_lt_of_lt [Fintype A] (r : LinearOrder A) {a b : A} (hab : BallotPrefers r a b) :
    rank r a < rank r b := by
  classical
  letI := r
  change a < b at hab
  have hsubset :
      (Finset.univ.filter (fun x : A => BallotPrefers r x a)) ⊆
        (Finset.univ.filter (fun x : A => BallotPrefers r x b)) := by
    intro x hx
    exact Finset.mem_filter.mpr
      ⟨by simp, by
        change x < b
        exact lt_trans (by simpa [BallotPrefers] using (Finset.mem_filter.mp hx).2) hab⟩
  have hssub :
      (Finset.univ.filter (fun x : A => BallotPrefers r x a)) ⊂
        (Finset.univ.filter (fun x : A => BallotPrefers r x b)) := by
    refine (Finset.ssubset_iff_of_subset hsubset).2 ?_
    refine ⟨a, ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨by simp, by simpa [BallotPrefers] using hab⟩
    · intro ha
      exact lt_irrefl a (by simpa [BallotPrefers] using (Finset.mem_filter.mp ha).2)
  simpa [rank] using Finset.card_lt_card hssub

theorem rank_lt_iff [Fintype A] (r : LinearOrder A) {a b : A} :
    rank r a < rank r b ↔ BallotPrefers r a b := by
  constructor
  · intro h
    letI := r
    by_contra hnot
    have hne : a ≠ b := by
      intro hab
      subst hab
      omega
    have hba : b < a := lt_of_le_of_ne (le_of_not_gt hnot) (Ne.symm hne)
    have hlt := rank_lt_of_lt r (by simpa [BallotPrefers] using hba)
    omega
  · exact rank_lt_of_lt r

theorem rank_injective [Fintype A] (r : LinearOrder A) :
    Function.Injective (rank r) := by
  intro a b h
  by_contra hne
  rcases BallotPrefers.total_of_ne r hne with hab | hba
  · have hlt := rank_lt_of_lt r hab
    omega
  · have hlt := rank_lt_of_lt r hba
    omega

/-! ### Pairwise majority and margins -/

/-- Voters who strictly prefer `a` to `b`. -/
noncomputable def votersPreferring [Fintype N] [Fintype A]
    (P : Profile N A) (a b : A) : Finset N :=
  Finset.univ.filter (fun i => Prefers P i a b)

/-- Pairwise majority margin: voters preferring `a` to `b` minus voters
preferring `b` to `a`. -/
noncomputable def margin [Fintype N] [Fintype A]
    (P : Profile N A) (a b : A) : Int :=
  Int.ofNat (Finset.card (votersPreferring P a b)) -
    Int.ofNat (Finset.card (votersPreferring P b a))

/-- Positive pairwise majority margin. -/
def margin_pos [Fintype N] [Fintype A] (P : Profile N A) (a b : A) : Prop :=
  0 < margin P a b

theorem margin_self [Fintype N] [Fintype A] (P : Profile N A) (a : A) :
    margin P a a = 0 := by
  simp [margin, votersPreferring, Prefers]

theorem margin_skew [Fintype N] [Fintype A] (P : Profile N A) (a b : A) :
    margin P a b = -margin P b a := by
  rw [margin, margin]
  omega

/-- Pairwise majority comparison. -/
def MajorityPrefers [Fintype N] [Fintype A] (P : Profile N A) (a b : A) : Prop :=
  margin_pos P a b

/-- `a` is a Condorcet winner if it beats every other alternative by strict
pairwise majority. -/
def CondorcetWinner [Fintype N] [Fintype A] (P : Profile N A) (a : A) : Prop :=
  ∀ b : A, b ≠ a → MajorityPrefers P a b

/-- A profile has at least one Condorcet winner. -/
def HasCondorcetWinner [Fintype N] [Fintype A] (P : Profile N A) : Prop :=
  ∃ a : A, CondorcetWinner P a

/-- A rule is Condorcet-consistent if every Condorcet winner is the unique
winner. -/
def CondorcetConsistency [Fintype N] [Fintype A] (f : VotingRule N A) : Prop :=
  ∀ (P : Profile N A) (a : A), CondorcetWinner P a → f P = {a}

/-! ### Scoring rules -/

/-- Total score for a candidate under a positional score vector. -/
noncomputable def scoreCandidate [Fintype N] [Fintype A]
    (P : Profile N A) (score : Nat → Int) (a : A) : Int :=
  ∑ i : N, score (rank (P.pref i) a)

/-- Winners with maximal score. -/
noncomputable def scoringWinners [Fintype N] [Fintype A]
    (P : Profile N A) (score : Nat → Int) : Finset A := by
  classical
  by_cases hA : (Finset.univ : Finset A).Nonempty
  · let maxScore : Int :=
      (Finset.univ.image (fun a => scoreCandidate P score a)).max' (hA.image _)
    exact Finset.univ.filter (fun a => scoreCandidate P score a = maxScore)
  · exact ∅

/-- Generic positional scoring rule. The first argument is the number of
alternatives, and the second is the zero-based rank. -/
noncomputable def scoringRule (score : Nat → Nat → Int)
    [Fintype N] [Fintype A] : VotingRule N A :=
  fun P => scoringWinners P (fun r => score (Fintype.card A) r)

theorem scoringWinners_nonempty [Fintype N] [Fintype A] [Nonempty A]
    (P : Profile N A) (score : Nat → Int) :
    (scoringWinners P score).Nonempty := by
  classical
  have hA : (Finset.univ : Finset A).Nonempty := Finset.univ_nonempty
  let scoreSet : Finset Int := Finset.univ.image (fun a => scoreCandidate P score a)
  have hScore : scoreSet.Nonempty := hA.image _
  let maxScore : Int := scoreSet.max' hScore
  have hmem : maxScore ∈ scoreSet := Finset.max'_mem scoreSet hScore
  rcases Finset.mem_image.mp hmem with ⟨a, _, ha⟩
  refine ⟨a, ?_⟩
  simp [scoringWinners, hA, scoreSet, maxScore, ha]

theorem scoringRule_isTotal (score : Nat → Nat → Int)
    [Fintype N] [Fintype A] [Nonempty A] :
    IsTotal (N := N) (A := A) (scoringRule score) := by
  intro P
  simpa [scoringRule] using scoringWinners_nonempty (P := P)
    (score := fun r => score (Fintype.card A) r)

/-- Plurality score vector. -/
def pluralityScore (_m r : Nat) : Int :=
  if r = 0 then 1 else 0

/-- Borda score vector, with top rank receiving `m - 1` points. -/
def bordaScore (m r : Nat) : Int :=
  Int.ofNat (m - 1 - r)

/-- Veto score vector: every non-last rank receives one point. -/
def vetoScore (m r : Nat) : Int :=
  if r + 1 = m then 0 else 1

/-- Plurality rule. -/
noncomputable def plurality [Fintype N] [Fintype A] : VotingRule N A :=
  scoringRule pluralityScore

/-- Borda rule. -/
noncomputable def borda [Fintype N] [Fintype A] : VotingRule N A :=
  scoringRule bordaScore

/-- Veto rule. -/
noncomputable def veto [Fintype N] [Fintype A] : VotingRule N A :=
  scoringRule vetoScore

theorem plurality_isTotal [Fintype N] [Fintype A] [Nonempty A] :
    IsTotal (N := N) (A := A) plurality :=
  scoringRule_isTotal pluralityScore

theorem borda_isTotal [Fintype N] [Fintype A] [Nonempty A] :
    IsTotal (N := N) (A := A) borda :=
  scoringRule_isTotal bordaScore

theorem veto_isTotal [Fintype N] [Fintype A] [Nonempty A] :
    IsTotal (N := N) (A := A) veto :=
  scoringRule_isTotal vetoScore

/-! ### Copeland rule -/

/-- Copeland score: pairwise majority wins minus pairwise majority losses. -/
noncomputable def copelandScore [Fintype N] [Fintype A]
    (P : Profile N A) (a : A) : Int :=
  Int.ofNat (Finset.card (Finset.univ.filter (fun b => MajorityPrefers P a b))) -
    Int.ofNat (Finset.card (Finset.univ.filter (fun b => MajorityPrefers P b a)))

/-- Copeland winners. -/
noncomputable def copeland [Fintype N] [Fintype A] : VotingRule N A := by
  intro P
  classical
  by_cases hA : (Finset.univ : Finset A).Nonempty
  · let maxScore : Int := (Finset.univ.image (fun a => copelandScore P a)).max' (hA.image _)
    exact Finset.univ.filter (fun a => copelandScore P a = maxScore)
  · exact ∅

theorem copeland_isTotal [Fintype N] [Fintype A] [Nonempty A] :
    IsTotal (N := N) (A := A) copeland := by
  intro P
  classical
  have hA : (Finset.univ : Finset A).Nonempty := Finset.univ_nonempty
  let scoreSet : Finset Int := Finset.univ.image (fun a => copelandScore P a)
  have hScore : scoreSet.Nonempty := hA.image _
  let maxScore : Int := scoreSet.max' hScore
  have hmem : maxScore ∈ scoreSet := Finset.max'_mem scoreSet hScore
  rcases Finset.mem_image.mp hmem with ⟨a, _, ha⟩
  refine ⟨a, ?_⟩
  simp [copeland, hA, scoreSet, maxScore, ha]

/-! ### Condorcet paradox -/

private noncomputable def finThreeRankOrder
    (r : Fin 3 → Nat) (hr : Function.Injective r) : LinearOrder (Fin 3) :=
  ballotFromInjective (inferInstance : LinearOrder Nat) r hr

/-- The standard Condorcet cycle profile:
voter 0 ranks `0 > 1 > 2`, voter 1 ranks `1 > 2 > 0`, and voter 2 ranks
`2 > 0 > 1`. -/
private noncomputable def condorcetCycleProfile : Profile (Fin 3) (Fin 3) where
  pref
    | 0 => finThreeRankOrder
        (fun a => if a = 0 then 0 else if a = 1 then 1 else 2)
        (by intro a b h; fin_cases a <;> fin_cases b <;> simp at h ⊢)
    | 1 => finThreeRankOrder
        (fun a => if a = 1 then 0 else if a = 2 then 1 else 2)
        (by intro a b h; fin_cases a <;> fin_cases b <;> simp at h ⊢)
    | 2 => finThreeRankOrder
        (fun a => if a = 2 then 0 else if a = 0 then 1 else 2)
        (by intro a b h; fin_cases a <;> fin_cases b <;> simp at h ⊢)

private theorem not_cycle_majority_zero_over_two :
    ¬ MajorityPrefers condorcetCycleProfile 0 2 := by
  have h02 : votersPreferring condorcetCycleProfile 0 2 = ({0} : Finset (Fin 3)) := by
    ext i
    fin_cases i <;> simp [votersPreferring, Prefers, condorcetCycleProfile,
      finThreeRankOrder]
  have h20 : votersPreferring condorcetCycleProfile 2 0 = ({1, 2} : Finset (Fin 3)) := by
    ext i
    fin_cases i <;> simp [votersPreferring, Prefers, condorcetCycleProfile,
      finThreeRankOrder]
  rw [MajorityPrefers, margin_pos, margin, h02, h20]
  norm_num

private theorem not_cycle_majority_one_over_zero :
    ¬ MajorityPrefers condorcetCycleProfile 1 0 := by
  have h10 : votersPreferring condorcetCycleProfile 1 0 = ({1} : Finset (Fin 3)) := by
    ext i
    fin_cases i <;> simp [votersPreferring, Prefers, condorcetCycleProfile,
      finThreeRankOrder]
  have h01 : votersPreferring condorcetCycleProfile 0 1 = ({0, 2} : Finset (Fin 3)) := by
    ext i
    fin_cases i <;> simp [votersPreferring, Prefers, condorcetCycleProfile,
      finThreeRankOrder]
  rw [MajorityPrefers, margin_pos, margin, h10, h01]
  norm_num

private theorem not_cycle_majority_two_over_one :
    ¬ MajorityPrefers condorcetCycleProfile 2 1 := by
  have h21 : votersPreferring condorcetCycleProfile 2 1 = ({2} : Finset (Fin 3)) := by
    ext i
    fin_cases i <;> simp [votersPreferring, Prefers, condorcetCycleProfile,
      finThreeRankOrder]
  have h12 : votersPreferring condorcetCycleProfile 1 2 = ({0, 1} : Finset (Fin 3)) := by
    ext i
    fin_cases i <;> simp [votersPreferring, Prefers, condorcetCycleProfile,
      finThreeRankOrder]
  rw [MajorityPrefers, margin_pos, margin, h21, h12]
  norm_num

/-- **Condorcet paradox**: with 3 voters and 3 alternatives, pairwise majority
can cycle, so a Condorcet winner need not exist. -/
theorem condorcet_paradox_possible :
    ∃ P : Profile (Fin 3) (Fin 3), ¬ HasCondorcetWinner P := by
  refine ⟨condorcetCycleProfile, ?_⟩
  rintro ⟨a, ha⟩
  fin_cases a
  · exact not_cycle_majority_zero_over_two (ha 2 (by decide))
  · exact not_cycle_majority_one_over_zero (ha 0 (by decide))
  · exact not_cycle_majority_two_over_one (ha 1 (by decide))

end Voting
end SocialChoice
