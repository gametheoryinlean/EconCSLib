/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.SocialChoice.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.Order.Basic

/-!
# EconCSLib.SocialChoice.Voting.Basic

Voting-specific social-choice infrastructure: finite strict preference profiles,
set-valued voting rules, social welfare functions, and the core voting axioms.

The foundation-level `Pref` bundle is the library-wide weak-preference
interface. The voting layer specializes to the standard
ranked-ballot model: each voter submits a linear order over a finite set of
alternatives, and a voting rule returns a finite set of winners.
-/

namespace SocialChoice
namespace Voting

open Finset

variable {N A : Type*}

/-! ### Strict finite voting profiles -/

/-- A voting profile assigns each voter a strict linear order over alternatives. -/
structure Profile (N A : Type*) [Fintype N] [Fintype A] where
  /-- The ballot submitted by each voter. Smaller means more preferred. -/
  pref : N → LinearOrder A

/-- Constant profile where every voter submits the same ballot. -/
def constantProfile [Fintype N] [Fintype A] (r : LinearOrder A) : Profile N A where
  pref := fun _ => r

@[ext]
theorem Profile.ext [Fintype N] [Fintype A] {P Q : Profile N A}
    (h : ∀ i : N, P.pref i = Q.pref i) : P = Q := by
  cases P
  cases Q
  simp only at h
  exact congrArg Profile.mk (funext h)

/-- Ballot `r` ranks `a` strictly above `b`. -/
abbrev ballotLE (r : LinearOrder A) : LE A :=
  @Preorder.toLE A (@PartialOrder.toPreorder A (@LinearOrder.toPartialOrder A r))

/-- Ballot `r`'s strict-order instance, exposed explicitly to avoid ambient
typeclass search. -/
abbrev ballotLT (r : LinearOrder A) : LT A :=
  @Preorder.toLT A (@PartialOrder.toPreorder A (@LinearOrder.toPartialOrder A r))

/-- Ballot `r` ranks `a` strictly above `b`. -/
def BallotPrefers (r : LinearOrder A) (a b : A) : Prop := by
  exact @LT.lt A (ballotLT r) a b

/-- Pull a linear order back along an injective map, using the supplied codomain
order explicitly rather than relying on ambient typeclass search. This is the
safe constructor for ballots on types such as `Fin n`, which already carry a
default order. -/
noncomputable def ballotFromInjective {B : Type*} (rB : LinearOrder B)
    (f : A → B) (hf : Function.Injective f) : LinearOrder A where
  toPartialOrder :=
    { toPreorder :=
        { toLE := ⟨fun a b => @LE.le B (ballotLE rB) (f a) (f b)⟩
          toLT := ⟨fun a b => @LT.lt B (ballotLT rB) (f a) (f b)⟩
          le_refl := fun a => rB.le_refl (f a)
          le_trans := fun a b c hab hbc => rB.le_trans (f a) (f b) (f c) hab hbc
          lt_iff_le_not_ge := fun a b => rB.lt_iff_le_not_ge (f a) (f b) }
      le_antisymm := fun a b hab hba => hf (rB.le_antisymm (f a) (f b) hab hba) }
  toMin := ⟨fun a b =>
    if @LE.le B (ballotLE rB) (f a) (f b) then a else b⟩
  toMax := ⟨fun a b =>
    if @LE.le B (ballotLE rB) (f a) (f b) then b else a⟩
  le_total := fun a b => rB.le_total (f a) (f b)
  toDecidableLE := fun a b =>
    @LinearOrder.toDecidableLE B rB (f a) (f b)
  toDecidableEq := Classical.decEq A
  toDecidableLT := fun a b =>
    @LinearOrder.toDecidableLT B rB (f a) (f b)
  min_def := by
    intro a b
    rfl
  max_def := by
    intro a b
    rfl

@[simp]
theorem BallotPrefers_ballotFromInjective {B : Type*} (rB : LinearOrder B)
    (f : A → B) (hf : Function.Injective f) (a b : A) :
    BallotPrefers (ballotFromInjective rB f hf) a b ↔
      @LT.lt B (ballotLT rB) (f a) (f b) := by
  rfl

theorem BallotPrefers.asymm (r : LinearOrder A) {a b : A} :
    BallotPrefers r a b → ¬ BallotPrefers r b a := by
  intro hab hba
  have hle_not := (r.lt_iff_le_not_ge a b).mp hab
  have hle := (r.lt_iff_le_not_ge b a).mp hba |>.left
  exact hle_not.right hle

theorem BallotPrefers.total_of_ne (r : LinearOrder A) {a b : A} (hne : a ≠ b) :
    BallotPrefers r a b ∨ BallotPrefers r b a := by
  letI := r
  rcases lt_or_gt_of_ne hne with hab | hba
  · left
    simpa [BallotPrefers, ballotLT] using hab
  · right
    simpa [BallotPrefers, ballotLT] using hba

/-- Voter `i` strictly prefers `a` to `b` in profile `P`. -/
def Prefers [Fintype N] [Fintype A] (P : Profile N A) (i : N) (a b : A) : Prop :=
  BallotPrefers (P.pref i) a b

theorem Prefers.asymm [Fintype N] [Fintype A] (P : Profile N A) (i : N) {a b : A} :
    Prefers P i a b → ¬ Prefers P i b a :=
  BallotPrefers.asymm (P.pref i)

theorem Prefers.total_of_ne [Fintype N] [Fintype A] (P : Profile N A) (i : N)
    {a b : A} (hne : a ≠ b) : Prefers P i a b ∨ Prefers P i b a :=
  BallotPrefers.total_of_ne (P.pref i) hne

/-- Candidate `a` is top-ranked by voter `i`. -/
def TopRank [Fintype N] [Fintype A] (P : Profile N A) (i : N) (a : A) : Prop :=
  ∀ b : A, b ≠ a → Prefers P i a b

/-- Candidate `a` is bottom-ranked by voter `i`. -/
def BottomRank [Fintype N] [Fintype A] (P : Profile N A) (i : N) (a : A) : Prop :=
  ∀ b : A, b ≠ a → Prefers P i b a

/-- A linear-order ballot ranks `a` first. -/
def BallotTop (r : LinearOrder A) (a : A) : Prop :=
  ∀ b : A, b ≠ a → BallotPrefers r a b

/-- A linear-order ballot ranks `a` last. -/
def BallotBottom (r : LinearOrder A) (a : A) : Prop :=
  ∀ b : A, b ≠ a → BallotPrefers r b a

/-- The top-ranked alternative of voter `i`. -/
noncomputable def topChoice [Fintype N] [Fintype A] [Nonempty A]
    (P : Profile N A) (i : N) : A := by
  classical
  letI := P.pref i
  exact Finset.min' Finset.univ Finset.univ_nonempty

theorem topChoice_topRank [Fintype N] [Fintype A] [Nonempty A]
    (P : Profile N A) (i : N) : TopRank P i (topChoice P i) := by
  classical
  intro b hb
  unfold topChoice Prefers
  letI := P.pref i
  exact lt_of_le_of_ne (Finset.min'_le Finset.univ b (by simp)) (Ne.symm hb)

theorem topRank_eq_topChoice [Fintype N] [Fintype A] [Nonempty A]
    (P : Profile N A) (i : N) (a : A) (ha : TopRank P i a) :
    a = topChoice P i := by
  by_contra hne
  have h₁ := ha (topChoice P i) (Ne.symm hne)
  have h₂ := topChoice_topRank P i a hne
  letI := P.pref i
  exact (lt_asymm h₁ h₂).elim

/-! ### Profile transformations -/

/-- Replace one voter's ballot. -/
@[reducible]
noncomputable def updateProfile [Fintype N] [Fintype A]
    (P : Profile N A) (i : N) (r : LinearOrder A) : Profile N A := by
  classical
  exact { pref := fun j => if j = i then r else P.pref j }

/-- Relabel voters by a permutation of the electorate. -/
def permuteVoters [Fintype N] [Fintype A]
    (P : Profile N A) (σ : Equiv.Perm N) : Profile N A where
  pref := fun i => P.pref (σ i)

/-- Relabel a linear order along a permutation of alternatives. -/
noncomputable def relabelBallot (r : LinearOrder A) (σ : Equiv.Perm A) : LinearOrder A := by
  classical
  exact ballotFromInjective r σ σ.injective

/-- Relabel a linear order along an equivalence of alternative types. -/
noncomputable def relabelBallotEquiv {B : Type*} (r : LinearOrder A) (e : A ≃ B) :
    LinearOrder B := by
  classical
  exact ballotFromInjective r e.symm e.symm.injective

/-- Relabel candidates by applying the inverse permutation to each ballot. -/
noncomputable def permuteCandidates [Fintype N] [Fintype A]
    (P : Profile N A) (σ : Equiv.Perm A) : Profile N A where
  pref := fun i => relabelBallot (P.pref i) σ.symm

/-- Relabel a profile along an equivalence of alternative types. -/
noncomputable def relabelProfile {B : Type*} [Fintype N] [Fintype A] [Fintype B]
    (P : Profile N A) (e : A ≃ B) : Profile N B where
  pref := fun i => relabelBallotEquiv (P.pref i) e

/-! ### Voting rules and social welfare functions -/

/-- A set-valued voting rule on fixed finite voter and candidate types. -/
abbrev VotingRule (N A : Type*) [Fintype N] [Fintype A] :=
  Profile N A → Finset A

/-- A voting rule is total if it always returns at least one winner. -/
def IsTotal [Fintype N] [Fintype A] (f : VotingRule N A) : Prop :=
  ∀ P : Profile N A, (f P).Nonempty

/-- A voting rule is resolute if it always returns exactly one winner. -/
def Resolute [Fintype N] [Fintype A] (f : VotingRule N A) : Prop :=
  ∀ P : Profile N A, Finset.card (f P) = 1

/-- A social welfare function maps strict profiles to a weak social preference. -/
abbrev SWF (N A : Type*) [Fintype N] [Fintype A] :=
  Profile N A → Pref A

namespace SWF

variable [Fintype N] [Fintype A]

/-- Unanimity/Pareto for SWFs: unanimous strict preference forces social strict
preference. -/
def Unanimity (F : SWF N A) : Prop :=
  ∀ (P : Profile N A) (a b : A),
    (∀ i : N, Prefers P i a b) → strict (F P) a b

/-- Independence of irrelevant alternatives for SWFs. -/
def IIA (F : SWF N A) : Prop :=
  ∀ (P Q : Profile N A) (a b : A),
    (∀ i : N, Prefers P i a b ↔ Prefers Q i a b) →
    (F P a b ↔ F Q a b)

/-- A SWF is dictatorial if one voter always determines every strict social
comparison. -/
def Dictatorial (F : SWF N A) : Prop :=
  ∃ i : N, ∀ (P : Profile N A) (a b : A),
    Prefers P i a b → strict (F P) a b

/-- A SWF is non-dictatorial. -/
def NonDictatorial (F : SWF N A) : Prop :=
  ¬ Dictatorial F

end SWF

/-! ### Voting-rule axioms -/

section VotingRuleAxioms

variable [Fintype N] [Fintype A]

/-- Unanimity/Pareto for set-valued voting rules: no unanimously dominated
alternative is selected. -/
def Unanimity (f : VotingRule N A) : Prop :=
  ∀ (P : Profile N A) (a b : A), (∀ i : N, Prefers P i a b) → b ∉ f P

/-- Alias for voting-rule unanimity in its weak-Pareto form. -/
abbrev ParetoEfficiency (f : VotingRule N A) : Prop :=
  Unanimity f

/-- Top unanimity follows from weak-Pareto unanimity plus totality: if every
voter ranks `a` first, then `a` is the unique winner. -/
theorem top_unanimity_of_unanimity [Nonempty A] {f : VotingRule N A}
    (hf : IsTotal f) (hU : Unanimity f) :
    ∀ (P : Profile N A) (a : A), (∀ i : N, TopRank P i a) → f P = {a} := by
  intro P a ha
  apply Finset.eq_singleton_iff_unique_mem.mpr
  refine ⟨?_, ?_⟩
  · by_contra hnot
    rcases hf P with ⟨b, hb⟩
    have hba : b = a := by
      by_contra hne
      exact hU P a b (fun i => ha i b hne) hb
    exact hnot (by simpa [hba] using hb)
  · intro b hb
    by_contra hne
    exact hU P a b (fun i => ha i b hne) hb

/-- Anonymity: relabeling voters does not change the winner set. -/
def Anonymity (f : VotingRule N A) : Prop :=
  ∀ (P : Profile N A) (σ : Equiv.Perm N), f (permuteVoters P σ) = f P

/-- Candidate renaming on winner sets. -/
noncomputable def permuteWinners (σ : Equiv.Perm A) (s : Finset A) : Finset A := by
  classical
  exact s.map σ.toEmbedding

/-- Neutrality: relabeling candidates relabels the winner set. -/
def Neutrality (f : VotingRule N A) : Prop :=
  ∀ (P : Profile N A) (σ : Equiv.Perm A),
    permuteWinners σ (f P) = f (permuteCandidates P σ)

/-- `Q` is obtained from `P` by weakly raising `a`: anything below `a` in `P`
remains below `a` in `Q`, and anything above `a` in `Q` was already above `a`
in `P`. -/
def SimpleLift (Q P : Profile N A) (a : A) : Prop :=
  ∀ i x, (Prefers P i a x → Prefers Q i a x) ∧
    (Prefers Q i x a → Prefers P i x a)

/-- Monotonicity: raising a selected alternative cannot make it unselected. -/
def Monotonicity (f : VotingRule N A) : Prop :=
  ∀ (P Q : Profile N A) (a : A), a ∈ f P → SimpleLift Q P a → a ∈ f Q

/-- Strategyproofness for resolute rules: changing one ballot cannot produce a
strictly better unique winner for the deviating voter. -/
def ResoluteStrategyproofness (f : VotingRule N A) (_hf : Resolute f) : Prop :=
  ∀ (P : Profile N A) (i : N) (r : LinearOrder A) (a b : A),
    f P = {a} →
    f (updateProfile P i r) = {b} →
    ¬ Prefers P i b a

/-- Optimist strategyproofness for set-valued rules. -/
def OptimistStrategyproofness (f : VotingRule N A) : Prop :=
  ∀ (P : Profile N A) (i : N) (r : LinearOrder A),
    ¬ ∃ b ∈ f (updateProfile P i r), ∀ a ∈ f P, Prefers P i b a

/-- Pessimist strategyproofness for set-valued rules. -/
def PessimistStrategyproofness (f : VotingRule N A) : Prop :=
  ∀ (P : Profile N A) (i : N) (r : LinearOrder A),
    ¬ ∃ a ∈ f P, ∀ b ∈ f (updateProfile P i r), Prefers P i b a

/-- A rule is dictatorial if one voter always gets their top-ranked alternative
as the unique winner. -/
def Dictatorial [Nonempty A] (f : VotingRule N A) : Prop :=
  ∃ i : N, ∀ P : Profile N A, f P = {topChoice P i}

end VotingRuleAxioms

end Voting
end SocialChoice
