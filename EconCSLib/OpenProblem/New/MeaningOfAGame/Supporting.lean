/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.OpenProblem.New.MeaningOfAGame.Problem

/-!
# MeaningOfAGame: supporting material

Auxiliary definitions and lemmas for the problem statement.
-/

section

/-!
## Intersections and disjointness of minimal attractors

Compact uniformly attracting invariant sets are closed under nonempty finite
intersection. Consequently distinct minimal attractors are disjoint. These facts do
not use, or assume, the replicator-specific pure-profile containment theorem needed
for a finite bound on the number of attractors.
-/

open Filter Topology
open scoped BigOperators

namespace EconCSLib.OpenProblem.New.EconCSBench.MeaningOfAGame

variable {Player : Type*} {Action : Player → Type*}
  [Fintype Player] [∀ i, Fintype (Action i)]

/-- The explicit finite-coordinate l1 distance is continuous in both arguments. -/
theorem continuous_mixedProfileDistance :
    Continuous (fun xy : MixedProfile Player Action × MixedProfile Player Action =>
      mixedProfileDistance xy.1 xy.2) := by
  unfold mixedProfileDistance
  apply continuous_finsetSum
  intro i _
  apply continuous_finsetSum
  intro a _
  exact ((continuous_apply a).comp (continuous_subtype_val.comp
    ((continuous_apply i).comp continuous_fst))).sub
    ((continuous_apply a).comp (continuous_subtype_val.comp
      ((continuous_apply i).comp continuous_snd))) |>.abs

/-- Each explicit metric neighborhood is open. -/
theorem isOpen_isWithinProfileSet (ε : ℝ) (A : Set (MixedProfile Player Action)) :
    IsOpen {x | IsWithinProfileSet ε A x} := by
  rw [isOpen_iff_mem_nhds]
  rintro x ⟨y, hy, hxy⟩
  have hcont : Continuous (fun z : MixedProfile Player Action => mixedProfileDistance z y) :=
    continuous_mixedProfileDistance.comp (continuous_id.prodMk continuous_const)
  exact Filter.mem_of_superset ((isOpen_lt hcont continuous_const).mem_nhds hxy)
    (fun z hz => ⟨y, hy, hz⟩)

/-- Small neighborhoods of two compact sets intersect near their intersection. -/
theorem exists_near_inter_of_compact
    {A B : Set (MixedProfile Player Action)} (hA : IsCompact A) (hB : IsCompact B)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x, IsWithinProfileSet δ A x → IsWithinProfileSet δ B x →
      IsWithinProfileSet ε (A ∩ B) x := by
  have hn : {x | IsWithinProfileSet ε (A ∩ B) x} ∈ 𝓝ˢ (A ∩ B) :=
    (isOpen_isWithinProfileSet ε (A ∩ B)).mem_nhdsSet.mpr
      (fun x hx => ⟨x, hx, by simpa using hε⟩)
  rw [hA.nhdsSet_inter_eq hB] at hn
  obtain ⟨⟨r, s⟩, ⟨hr, hs⟩, hsub⟩ :=
    ((Metric.hasBasis_nhdsSet_thickening hA).inf
      (Metric.hasBasis_nhdsSet_thickening hB)).mem_iff.mp hn
  refine ⟨min r s, lt_min hr hs, fun x hxA hxB => hsub ?_⟩
  obtain ⟨a, ha, hxa⟩ := hxA
  obtain ⟨b, hb, hxb⟩ := hxB
  exact ⟨Metric.mem_thickening_iff.mpr ⟨a, ha,
      (dist_le_mixedProfileDistance x a).trans_lt (hxa.trans_le (min_le_left _ _))⟩,
    Metric.mem_thickening_iff.mpr ⟨b, hb,
      (dist_le_mixedProfileDistance x b).trans_lt (hxb.trans_le (min_le_right _ _))⟩⟩

variable [DecidableEq Player]

/-- A nonempty intersection of two compact uniform attracting sets is attracting. -/
theorem ReplicatorSemantics.IsAttractingSet.inter
    {G : FiniteNormalFormGame Player Action} {dynamics : ReplicatorSemantics G}
    {A B : Set (MixedProfile Player Action)}
    (hA : dynamics.IsAttractingSet A) (hB : dynamics.IsAttractingSet B)
    (hne : (A ∩ B).Nonempty) : dynamics.IsAttractingSet (A ∩ B) := by
  refine ⟨hne, hA.2.1.inter hB.2.1, ?_, ?_⟩
  · intro t
    have hi : Function.Injective (fun x => dynamics.flow t x) :=
      (dynamics.flow.toHomeomorph t).injective
    rw [Set.image_inter hi, hA.2.2.1 t, hB.2.2.1 t]
  · obtain ⟨rA, hrA, htimeA⟩ := hA.2.2.2
    obtain ⟨rB, hrB, htimeB⟩ := hB.2.2.2
    refine ⟨min rA rB, lt_min hrA hrB, fun ε hε => ?_⟩
    obtain ⟨δ, hδ, hnear⟩ := exists_near_inter_of_compact hA.2.1 hB.2.1 hε
    obtain ⟨TA, hTA, hAδ⟩ := htimeA δ hδ
    obtain ⟨TB, _, hBδ⟩ := htimeB δ hδ
    refine ⟨max TA TB, hTA.trans (le_max_left _ _), fun t ht x hx => ?_⟩
    obtain ⟨y, hy, hxy⟩ := hx
    apply hnear
    · exact hAδ t ((le_max_left _ _).trans ht) x
        ⟨y, hy.1, hxy.trans_le (min_le_left _ _)⟩
    · exact hBδ t ((le_max_right _ _).trans ht) x
        ⟨y, hy.2, hxy.trans_le (min_le_right _ _)⟩

/-- Two minimal attractors that intersect are equal. -/
theorem ReplicatorSemantics.IsMinimalAttractor.eq_of_inter_nonempty
    {G : FiniteNormalFormGame Player Action} {dynamics : ReplicatorSemantics G}
    {A B : Set (MixedProfile Player Action)}
    (hA : dynamics.IsMinimalAttractor A) (hB : dynamics.IsMinimalAttractor B)
    (hne : (A ∩ B).Nonempty) : A = B := by
  have hi := hA.1.inter hB.1 hne
  exact Set.Subset.antisymm
    ((hA.2 (A ∩ B) Set.inter_subset_left hi).trans Set.inter_subset_right)
    ((hB.2 (A ∩ B) Set.inter_subset_right hi).trans Set.inter_subset_left)

/-- Distinct minimal attractors cannot share a mixed profile. -/
theorem ReplicatorSemantics.IsMinimalAttractor.disjoint_of_ne
    {G : FiniteNormalFormGame Player Action} {dynamics : ReplicatorSemantics G}
    {A B : Set (MixedProfile Player Action)}
    (hA : dynamics.IsMinimalAttractor A) (hB : dynamics.IsMinimalAttractor B)
    (hne : A ≠ B) : Disjoint A B := by
  apply Set.disjoint_left.mpr
  intro x hxA hxB
  exact hne (hA.eq_of_inter_nonempty hB ⟨x, hxA, hxB⟩)

/-- A trajectory cannot approach two different compact minimal attractors. -/
theorem ReplicatorSemantics.IsLimitAttractor.unique
    {G : FiniteNormalFormGame Player Action} {dynamics : ReplicatorSemantics G}
    {x : MixedProfile Player Action} {A B : Set (MixedProfile Player Action)}
    (hA : dynamics.IsLimitAttractor x A) (hB : dynamics.IsLimitAttractor x B) : A = B := by
  by_contra hne
  obtain ⟨δ, hδ, hdis⟩ :=
    (hA.1.disjoint_of_ne hB.1 hne).exists_thickenings hA.1.1.2.1 hB.1.1.2.1.isClosed
  obtain ⟨TA, _, hTA⟩ := hA.2 δ hδ
  obtain ⟨TB, _, hTB⟩ := hB.2 δ hδ
  obtain ⟨a, ha, hxa⟩ := hTA (max TA TB) (le_max_left _ _)
  obtain ⟨b, hb, hxb⟩ := hTB (max TA TB) (le_max_right _ _)
  exact Set.disjoint_left.mp hdis
    (Metric.mem_thickening_iff.mpr ⟨a, ha, (dist_le_mixedProfileDistance _ a).trans_lt hxa⟩)
    (Metric.mem_thickening_iff.mpr ⟨b, hb, (dist_le_mixedProfileDistance _ b).trans_lt hxb⟩)

/-- A finite witness family bounds the number of disjoint minimal attractors. The
witness-containment premise is a separate mathematical obligation. -/
theorem ReplicatorSemantics.finite_attractors_of_finite_witnesses
    {G : FiniteNormalFormGame Player Action} (dynamics : ReplicatorSemantics G)
    {Witness : Type*} [Finite Witness] (point : Witness → MixedProfile Player Action)
    (hcontains : ∀ A, dynamics.IsMinimalAttractor A → ∃ w, point w ∈ A) :
    dynamics.attractors.Finite ∧ dynamics.attractors.ncard ≤ Nat.card Witness := by
  classical
  let select : dynamics.attractors → Witness :=
    fun A => Classical.choose (hcontains A.val A.property)
  have hselect (A : dynamics.attractors) : point (select A) ∈ A.val :=
    Classical.choose_spec (hcontains A.val A.property)
  have hinj : Function.Injective select := by
    intro A B hab
    apply Subtype.ext
    apply A.property.eq_of_inter_nonempty B.property
    exact ⟨point (select A), hselect A, hab ▸ hselect B⟩
  haveI : Finite dynamics.attractors := Finite.of_injective select hinj
  exact ⟨Set.toFinite _, Nat.card_le_card_of_injective select hinj⟩

end EconCSLib.OpenProblem.New.EconCSBench.MeaningOfAGame

end


section

/-!
## Real-valued games and initial profiles without a basin promise
-/
namespace EconCSLib.OpenProblem.New.EconCSBench.MeaningOfAGame

structure RealGame where
  shape : GameShape
  game : FiniteNormalFormGame shape.Player shape.Action

structure RealStart where
  game : RealGame
  profile : game.shape.RealProfile

/-- The replicator flow of the given real game. -/
abbrev RealReplicatorModel := (G : RealGame) → ReplicatorSemantics G.game

end EconCSLib.OpenProblem.New.EconCSBench.MeaningOfAGame

end


section

/-!
## Set-valued semantic answers

These contracts have actual sets as outputs. They assert no computability. Literal
all-start prediction, basin-promised prediction, and total diagnosis are distinct. The
promise is a project correction of Conjecture 6.3. Finite-code questions and their
representation scope live in `PresentedProblem` and `Problem`.
-/
namespace EconCSLib.OpenProblem.New.EconCSBench.MeaningOfAGame

/-- A finite list of actual sets, with neither omissions nor spurious entries. -/
def RealAttractorCollectionSolution (dynamics : RealReplicatorModel)
    (G : RealGame) (output : List (Set G.shape.RealProfile)) : Prop :=
  ∀ A, A ∈ output ↔ (dynamics G).IsAttractor A

/-- An actual approached minimal attractor, with no language or decoder. -/
def RealLimitAttractorSolution (dynamics : RealReplicatorModel)
    (I : RealStart) (output : Set I.game.shape.RealProfile) : Prop :=
  (dynamics I.game).IsLimitAttractor I.profile output

/-- Exact mathematical collection correctness. -/
def IsRealAttractorComputation (dynamics : RealReplicatorModel)
    (solve : (G : RealGame) → List (Set G.shape.RealProfile)) : Prop :=
  ∀ G, RealAttractorCollectionSolution dynamics G (solve G)

/-- Literal correctness on every real start, including unstable stationary points. -/
def IsRealLimitPrediction (dynamics : RealReplicatorModel)
    (solve : (I : RealStart) → Set I.game.shape.RealProfile) : Prop :=
  ∀ I, RealLimitAttractorSolution dynamics I (solve I)

/-- Correctness only inside the union of minimal-attractor basins. No procedure for
recognizing that union is demanded. -/
def IsBasinPromisedRealLimitPrediction (dynamics : RealReplicatorModel)
    (solve : (I : RealStart) → Set I.game.shape.RealProfile) : Prop :=
  ∀ I, (dynamics I.game).HasLimitAttractor I.profile →
    RealLimitAttractorSolution dynamics I (solve I)

/-- A total semantic diagnosis. The negative case is not a failed decoding. -/
inductive LimitDiagnosisOutput (I : RealStart)
  | attractor (set : Set I.game.shape.RealProfile)
  | noApproachedAttractor

/-- A negative answer says that no minimal attractor is approached, not that the
trajectory has no omega-limit points. -/
def TotalLimitDiagnosisSolution (dynamics : RealReplicatorModel) (I : RealStart) :
    LimitDiagnosisOutput I → Prop
  | .attractor A => RealLimitAttractorSolution dynamics I A
  | .noApproachedAttractor => ¬ (dynamics I.game).HasLimitAttractor I.profile

/-- Total real diagnosis is a separate mathematical relation. -/
def IsTotalRealLimitDiagnosis (dynamics : RealReplicatorModel)
    (solve : (I : RealStart) → LimitDiagnosisOutput I) : Prop :=
  ∀ I, TotalLimitDiagnosisSolution dynamics I (solve I)

theorem RealAttractorCollectionSolution.finite (dynamics : RealReplicatorModel)
    (G : RealGame) (output : List (Set G.shape.RealProfile))
    (correct : RealAttractorCollectionSolution dynamics G output) :
    (dynamics G).attractors.Finite := by
  apply output.finite_toSet.subset
  intro A hA
  exact (correct A).mpr hA

theorem realAttractorCollectionSolution_nil_iff (dynamics : RealReplicatorModel)
    (G : RealGame) :
    RealAttractorCollectionSolution dynamics G [] ↔
      ∀ A, ¬ (dynamics G).IsAttractor A := by
  simp [RealAttractorCollectionSolution]

/-- Even unlimited mathematical output cannot repair an answerless literal input. -/
theorem IsRealLimitPrediction.hasLimitAttractor (dynamics : RealReplicatorModel)
    (solve : (I : RealStart) → Set I.game.shape.RealProfile)
    (correct : IsRealLimitPrediction dynamics solve) (I : RealStart) :
    (dynamics I.game).HasLimitAttractor I.profile := ⟨solve I, correct I⟩

theorem no_literal_predictor_of_outside_basin (dynamics : RealReplicatorModel)
    (I : RealStart) (outside : ¬ (dynamics I.game).HasLimitAttractor I.profile) :
    ¬ ∃ solve, IsRealLimitPrediction dynamics solve := by
  rintro ⟨solve, correct⟩
  exact outside (correct.hasLimitAttractor dynamics solve I)

/-- The promise removes an input obligation; it does not let an algorithm return a
negative answer on a promised input. -/
theorem no_negative_diagnosis_on_basin (dynamics : RealReplicatorModel)
    (I : RealStart) (inside : (dynamics I.game).HasLimitAttractor I.profile) :
    ¬ TotalLimitDiagnosisSolution dynamics I .noApproachedAttractor := by
  exact fun negative => negative inside

end EconCSLib.OpenProblem.New.EconCSBench.MeaningOfAGame

end


section

/-!
## Prior mass outside the minimal-attractor basins

An arbitrary initial law need not induce a probability law on attractor labels alone.
A measurable total labeling has a residual label whose mass is exactly the
outside-basin mass.
-/
namespace EconCSLib.OpenProblem.New.EconCSBench.MeaningOfAGame
open MeasureTheory
open scoped ENNReal

/-- The semantic basin union. -/
def ReplicatorSemantics.basinUnion {G : RealGame}
    (dynamics : ReplicatorSemantics G.game) : Set G.shape.RealProfile :=
  {x | dynamics.HasLimitAttractor x}

/-- The probability mass of initial profiles outside all minimal-attractor basins. -/
noncomputable def ReplicatorSemantics.residualMass {G : RealGame}
    (dynamics : ReplicatorSemantics G.game) (prior : Measure G.shape.RealProfile) : ℝ≥0∞ :=
  prior dynamics.basinUnionᶜ

/-- Basin support is an almost-sure condition, not necessarily topological support. -/
def ReplicatorSemantics.IsBasinSupported {G : RealGame}
    (dynamics : ReplicatorSemantics G.game) (prior : Measure G.shape.RealProfile) : Prop :=
  ∀ᵐ x ∂prior, dynamics.HasLimitAttractor x

theorem ReplicatorSemantics.isBasinSupported_iff_residualMass_eq_zero {G : RealGame}
    (dynamics : ReplicatorSemantics G.game) (prior : Measure G.shape.RealProfile) :
    dynamics.IsBasinSupported prior ↔ dynamics.residualMass prior = 0 := by
  rfl

/-- A prior concentrated at any answerless input has residual mass one. -/
theorem ReplicatorSemantics.residualMass_dirac_of_outside {G : RealGame}
    (dynamics : ReplicatorSemantics G.game) (x : G.shape.RealProfile)
    (outside : ¬ dynamics.HasLimitAttractor x) :
    dynamics.residualMass (Measure.dirac x) = 1 :=
  Measure.dirac_apply_of_mem outside

/-- A correct measurable diagnosis pushes exactly the outside-basin mass to the residual
label. No existence of such a labeling is assumed globally. -/
theorem ReplicatorSemantics.map_none_eq_residualMass {G : RealGame}
    (dynamics : ReplicatorSemantics G.game) (prior : Measure G.shape.RealProfile)
    {Label : Type*} [MeasurableSpace (Option Label)] [MeasurableSingletonClass (Option Label)]
    (classify : G.shape.RealProfile → Option Label) (measurable : Measurable classify)
    (negative : ∀ x, classify x = none ↔ ¬ dynamics.HasLimitAttractor x) :
    (prior.map classify) {none} = dynamics.residualMass prior := by
  rw [Measure.map_apply measurable (measurableSet_singleton none)]
  congr 1
  ext x
  exact negative x

/-- Attractor-only probability output requires the residual mass to vanish. -/
theorem ReplicatorSemantics.map_none_eq_zero_iff {G : RealGame}
    (dynamics : ReplicatorSemantics G.game) (prior : Measure G.shape.RealProfile)
    {Label : Type*} [MeasurableSpace (Option Label)] [MeasurableSingletonClass (Option Label)]
    (classify : G.shape.RealProfile → Option Label) (measurable : Measurable classify)
    (negative : ∀ x, classify x = none ↔ ¬ dynamics.HasLimitAttractor x) :
    (prior.map classify) {none} = 0 ↔ dynamics.IsBasinSupported prior := by
  rw [dynamics.map_none_eq_residualMass prior classify measurable negative,
    dynamics.isBasinSupported_iff_residualMass_eq_zero]

end EconCSLib.OpenProblem.New.EconCSBench.MeaningOfAGame

end


section

/-!
## Openness of the minimal-attractor basin union

Uniform attraction of a neighborhood and continuity of the actual flow make each basin
open. Thus the union is measurable without assuming that almost every start belongs to
it or supplying a decision procedure for membership.
-/

open Filter Topology

namespace EconCSLib.OpenProblem.New.EconCSBench.MeaningOfAGame

variable {Player : Type*} {Action : Player → Type*}
  [Fintype Player] [DecidableEq Player] [∀ i, Fintype (Action i)]

/-- Entering a uniformly attracted neighborhood suffices for convergence in distance to
the attractor. The entry time may depend on the initial point. -/
theorem ReplicatorSemantics.isLimitAttractor_of_enters_neighborhood
    {G : FiniteNormalFormGame Player Action} (dynamics : ReplicatorSemantics G)
    {A : Set (MixedProfile Player Action)} (hA : dynamics.IsAttractor A)
    {radius : ℝ}
    (attracts : ∀ ε : ℝ, 0 < ε → ∃ T : ℝ, 0 ≤ T ∧
      ∀ t, T ≤ t → ∀ x, IsWithinProfileSet radius A x →
        IsWithinProfileSet ε A (dynamics.flow t x))
    {x : MixedProfile Player Action} {entry : ℝ} (entry_nonnegative : 0 ≤ entry)
    (entered : IsWithinProfileSet radius A (dynamics.flow entry x)) :
    dynamics.IsLimitAttractor x A := by
  refine ⟨hA, fun ε hε => ?_⟩
  obtain ⟨T, hT, close⟩ := attracts ε hε
  refine ⟨T + entry, add_nonneg hT entry_nonnegative, fun t ht => ?_⟩
  have htime : T ≤ t - entry := by linarith
  have result := close (t - entry) htime (dynamics.flow entry x) entered
  simpa only [← dynamics.flow.map_add, sub_add_cancel] using result

/-- The basin of any specified minimal attractor is open; a non-attractor has an empty
basin under the same predicate. -/
theorem ReplicatorSemantics.isOpen_limitAttractor_basin
    {G : FiniteNormalFormGame Player Action} (dynamics : ReplicatorSemantics G)
    (A : Set (MixedProfile Player Action)) :
    IsOpen {x | dynamics.IsLimitAttractor x A} := by
  by_cases hA : dynamics.IsAttractor A
  · rw [isOpen_iff_mem_nhds]
    intro x hx
    obtain ⟨radius, hradius, attracts⟩ := hA.1.2.2.2
    obtain ⟨entry, hentry, enters⟩ := hx.2 radius hradius
    have openEntry : IsOpen {y | IsWithinProfileSet radius A (dynamics.flow entry y)} :=
      (isOpen_isWithinProfileSet radius A).preimage
        (dynamics.flow.continuous continuous_const continuous_id)
    exact Filter.mem_of_superset (openEntry.mem_nhds (enters entry le_rfl))
      (fun y hy => dynamics.isLimitAttractor_of_enters_neighborhood hA attracts hentry hy)
  · have empty : {x | dynamics.IsLimitAttractor x A} = ∅ := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      exact fun hx => hA hx.1
    rw [empty]
    exact isOpen_empty

/-- The basin promise defines an open set even without any finiteness theorem for the
family of minimal attractors. -/
theorem ReplicatorSemantics.isOpen_basinUnion {G : RealGame}
    (dynamics : ReplicatorSemantics G.game) : IsOpen dynamics.basinUnion := by
  have union : dynamics.basinUnion =
      ⋃ A : Set G.shape.RealProfile, {x | dynamics.IsLimitAttractor x A} := by
    ext x
    simp only [ReplicatorSemantics.basinUnion, ReplicatorSemantics.HasLimitAttractor,
      Set.mem_setOf_eq, Set.mem_iUnion]
  rw [union]
  exact isOpen_iUnion (fun A => dynamics.isOpen_limitAttractor_basin A)

/-- Outside-basin residual mass refers to a measurable event. -/
theorem ReplicatorSemantics.measurableSet_basinUnion {G : RealGame}
    (dynamics : ReplicatorSemantics G.game) : MeasurableSet dynamics.basinUnion :=
  dynamics.isOpen_basinUnion.measurableSet

theorem ReplicatorSemantics.measurableSet_outsideBasin {G : RealGame}
    (dynamics : ReplicatorSemantics G.game) : MeasurableSet dynamics.basinUnionᶜ :=
  dynamics.measurableSet_basinUnion.compl

end EconCSLib.OpenProblem.New.EconCSBench.MeaningOfAGame

end


section

/-!
## Output languages fixed before solvers

These denotation interfaces do not themselves prove effective interpretation or
succinctness. Such adequacy must be established for the selected language.
-/
namespace EconCSLib.OpenProblem.New.EconCSBench.MeaningOfAGame
open WordRAM.FiniteData

/-- Legacy schematic collection denotation. Some empty collection differs from invalid
syntax. No effectiveness follows. -/
structure AttractorCollectionLanguage where
  denotes : (shape : GameShape) → Code → Option (Set (Set shape.RealProfile))

end EconCSLib.OpenProblem.New.EconCSBench.MeaningOfAGame

end


section

/-!
## An explicit effective interpretation requirement

A fixed denotation alone can hide attractor computation. This optional distance-name
convention instead requires a fixed Word-RAM program to approximate distance to every
denoted set at every rational profile. Precision k is unary: the bound is polynomial
in k, not log k.

This is a specified representation variant. Negative certificates below are checked by
an actual fixed program; the soundness obligation cannot be replaced by a Boolean
answer decoder.
-/
namespace EconCSLib.OpenProblem.New.EconCSBench.MeaningOfAGame
open WordRAM.FiniteData

/-- Effectivity is enforced for all denoted sets. Coverage is separate. -/
def AttractorSetLanguage.HasPolynomialDistanceInterpreter
    (language : AttractorSetLanguage) : Prop :=
  ∃ interpreter : PolynomialDistanceInterpreter,
    ∀ shape description A, language.denotes shape description = some A →
      interpreter.Describes shape description A

/-- An explicit completeness obligation for a specified family of sets. -/
def AttractorSetLanguage.Covers (language : AttractorSetLanguage)
    (family : (shape : GameShape) → Set (Set shape.RealProfile)) : Prop :=
  ∀ shape A, A ∈ family shape →
    ∃ description, language.denotes shape description = some A

/-- Reuse the fixed executable certificate checker. -/
abbrev NegativePredictionVerifier := WordRAM.Certificates.Verifier

/-- Acceptance is the literal bit true produced by the fixed interpreter. No semantic
output decoder decides the negative assertion. -/
abbrev NegativePredictionVerifier.Accepts (verifier : NegativePredictionVerifier)
    (input certificate : Code) : Prop :=
  WordRAM.Certificates.Verifier.Accepts verifier input certificate

/-- Soundness links the actual checker to the mathematical negative claim. The verifier
cannot be supplied by each individual solver execution. -/
def NegativePredictionVerifier.Sound (verifier : NegativePredictionVerifier)
    (dynamics : (G : RationalGame) → ReplicatorSemantics G.toReal) : Prop :=
  ∀ I : RationalStart, ∀ certificate, verifier.Accepts I.code certificate →
    ¬ (dynamics I.game).HasLimitAttractor I.profile.toReal

/-- Existence of negative certificates is an additional representation obligation; it does
not follow from soundness or from excluded middle. -/
def NegativePredictionVerifier.Complete (verifier : NegativePredictionVerifier)
    (dynamics : (G : RationalGame) → ReplicatorSemantics G.toReal) : Prop :=
  ∀ I : RationalStart, ¬ (dynamics I.game).HasLimitAttractor I.profile.toReal →
    ∃ certificate, verifier.Accepts I.code certificate

/-- Both alternatives carry actual finite output. -/
inductive CertifiedLimitPredictionOutput
  | attractor (description : Code)
  | noApproachedAttractor (certificate : Code)
  deriving DecidableEq

def CertifiedLimitPredictionOutput.encode : CertifiedLimitPredictionOutput → Code
  | .attractor description => true :: description
  | .noApproachedAttractor certificate => false :: certificate

def CertifiedLimitPredictionOutput.decode : Code → Option CertifiedLimitPredictionOutput
  | true :: description => some (.attractor description)
  | false :: certificate => some (.noApproachedAttractor certificate)
  | [] => none

theorem CertifiedLimitPredictionOutput.decode_encode (output : CertifiedLimitPredictionOutput) :
    decode output.encode = some output := by
  cases output <;> rfl

end EconCSLib.OpenProblem.New.EconCSBench.MeaningOfAGame

end


section

/-!
## Explicit lists of set descriptions

The collection format is structural: a finite list of set descriptions. Each set uses
a fixed language. The optional effective variant adds a distance interpreter; it does
not assert that every attractor admits a short polynomial-distance description.
-/
namespace EconCSLib.OpenProblem.New.EconCSBench.MeaningOfAGame
open WordRAM.FiniteData

/-- Parse one escaped block, retaining the unconsumed suffix. -/
def readDescriptionBlock : Code → Option (Code × Code)
  | [] => none
  | false :: rest => some ([], rest)
  | true :: [] => none
  | true :: bit :: rest => do
      let (payload, suffix) ← readDescriptionBlock rest
      pure (bit :: payload, suffix)

/-- Fuel bounds the number of list cells; malformed inputs fail explicitly. -/
def readDescriptionList : ℕ → Code → Option (List Code × Code)
  | 0, _ => none
  | _ + 1, [] => none
  | _ + 1, false :: rest => some ([], rest)
  | fuel + 1, true :: rest => do
      let (description, suffix) ← readDescriptionBlock rest
      let (descriptions, tail) ← readDescriptionList fuel suffix
      pure (description :: descriptions, tail)

/-- Only a completely consumed framed list is a well-formed output. -/
def decodeDescriptionList (code : Code) : Option (List Code) := do
  let (descriptions, suffix) ← readDescriptionList (code.length + 1) code
  if suffix.isEmpty then some descriptions else none

theorem readDescriptionBlock_code (description suffix : Code) :
    readDescriptionBlock (descriptionBlock description ++ suffix) =
      some (description, suffix) := by
  induction description with
  | nil => rfl
  | cons bit rest ih => simp [descriptionBlock, readDescriptionBlock, ih]

theorem descriptionBlock_length (description : Code) :
    (descriptionBlock description).length = 2 * description.length + 1 := by
  induction description with
  | nil => rfl
  | cons bit rest ih => simp [descriptionBlock, ih]; omega

theorem descriptionListCode_length (descriptions : List Code) :
    (descriptionListCode descriptions).length =
      2 * (descriptions.map List.length).sum + 2 * descriptions.length + 1 := by
  induction descriptions with
  | nil => rfl
  | cons description rest ih =>
      simp [descriptionListCode, descriptionBlock_length, ih]
      omega

theorem readDescriptionList_code (descriptions : List Code) (suffix : Code)
    (fuel : ℕ) (enough : descriptions.length < fuel) :
    readDescriptionList fuel (descriptionListCode descriptions ++ suffix) =
      some (descriptions, suffix) := by
  induction descriptions generalizing fuel with
  | nil => cases fuel <;> simp_all [descriptionListCode, readDescriptionList]
  | cons description rest ih =>
      cases fuel with
      | zero => simp at enough
      | succ fuel =>
          have h : rest.length < fuel := by simpa using enough
          simp [descriptionListCode, readDescriptionList, List.append_assoc,
            readDescriptionBlock_code, ih fuel h]

theorem decodeDescriptionList_code (descriptions : List Code) :
    decodeDescriptionList (descriptionListCode descriptions) = some descriptions := by
  have h : descriptions.length < (descriptionListCode descriptions).length + 1 := by
    rw [descriptionListCode_length]
    omega
  have parsed := readDescriptionList_code descriptions []
    ((descriptionListCode descriptions).length + 1) h
  simp only [List.append_nil] at parsed
  simp [decodeDescriptionList, parsed]

theorem descriptionListCode_injective : Function.Injective descriptionListCode := by
  intro a b h
  have := congrArg decodeDescriptionList h
  simpa [decodeDescriptionList_code] using this

/-- Exact listed coverage entails finiteness; it is not an implicit premise that discards
games before the solver is quantified. -/
theorem DescribesAllAttractors.finite (language : AttractorSetLanguage)
    (G : RationalGame) (dynamics : ReplicatorSemantics G.toReal)
    (descriptions : List Code)
    (correct : DescribesAllAttractors language G dynamics descriptions) :
    dynamics.attractors.Finite := by
  have finiteNames := (descriptions.filterMap (language.denotes G.shape)).finite_toSet
  apply finiteNames.subset
  intro A hA
  obtain ⟨description, hmem, hdenotes⟩ := correct.2 A hA
  exact List.mem_filterMap.mpr ⟨description, hmem, hdenotes⟩

/-- An empty list is correct exactly when there is no minimal attractor. -/
theorem describesAllAttractors_nil_iff (language : AttractorSetLanguage)
    (G : RationalGame) (dynamics : ReplicatorSemantics G.toReal) :
    DescribesAllAttractors language G dynamics [] ↔
      ∀ A, ¬ dynamics.IsAttractor A := by
  simp [DescribesAttractors]

/-- An effective collection-computation question with a fixed set language. Writing every
description is charged by the original Word-RAM interpreter. -/
def EffectiveAttractorComputationQuestion
    (dynamics : (G : RationalGame) → ReplicatorSemantics G.toReal)
    (language : AttractorSetLanguage) : Prop :=
  language.HasPolynomialDistanceInterpreter ∧
    WordRAM.Search.PolynomiallySolvable
      (fun input => ∃ G : RationalGame, G.code = input)
      (ListedAttractorCollectionSolution dynamics language)

end EconCSLib.OpenProblem.New.EconCSBench.MeaningOfAGame

end


section

/-!
The original ambient extension conserves every row sum even off the simplex.
-/

open scoped BigOperators

namespace EconCSLib.OpenProblem.New.EconCSBench.MeaningOfAGame.FlowExistence

variable {Player : Type*} {Action : Player → Type*}
  [Fintype Player] [DecidableEq Player] [∀ i, Fintype (Action i)]

private def swapOwn (i : Player) :
    (Action i × (∀ j, Action j)) ≃ (Action i × (∀ j, Action j)) := by
  let swap : (Action i × (∀ j, Action j)) → (Action i × (∀ j, Action j)) :=
    fun p => (p.2 i, Function.update p.2 i p.1)
  have hinv : Function.Involutive swap := by
    rintro ⟨a, profile⟩
    apply Prod.ext
    · simp [swap]
    · funext j
      by_cases hj : j = i
      · subst j; simp [swap]
      · simp [swap, Function.update_of_ne hj]
  exact ⟨swap, swap, hinv, hinv⟩

omit [∀ i, Fintype (Action i)] in
private theorem weight_swap (x : ProfileCoordinates Player Action)
    (i : Player) (a : Action i) (profile : ∀ j, Action j) :
    x i a * (∏ j, x j (profile j)) =
      x i (profile i) * (∏ j, x j (Function.update profile i a j)) := by
  classical
  have h₀ := Fintype.prod_eq_mul_prod_compl i (fun j => x j (profile j))
  have h₁ : (∏ j, x j (Function.update profile i a j)) =
      x i a * ∏ j ∈ ({i}ᶜ : Finset Player), x j (profile j) := by
    rw [Fintype.prod_eq_mul_prod_compl i]
    simp only [Function.update_self]
    congr 1
    apply Finset.prod_congr rfl
    intro j hj
    have hji : j ≠ i := by simpa using hj
    rw [Function.update_of_ne hji]
  rw [h₀, h₁]
  ring

/-- Summing weighted deviations multiplies expected payoff by the player's own row mass,
which need not be one off the simplex. -/
theorem sum_ambient_deviation (G : FiniteNormalFormGame Player Action)
    (x : ProfileCoordinates Player Action) (i : Player) :
    (∑ a, x i a * (∑ profile : ∀ j, Action j,
      (∏ j, x j (profile j)) * G.payoff (Function.update profile i a) i)) =
      (∑ a, x i a) * (∑ profile : ∀ j, Action j,
        (∏ j, x j (profile j)) * G.payoff profile i) := by
  classical
  have h := Fintype.sum_equiv (swapOwn (Action := Action) i)
    (fun p : Action i × (∀ j, Action j) =>
      x i p.1 * ((∏ j, x j (p.2 j)) * G.payoff (Function.update p.2 i p.1) i))
    (fun p : Action i × (∀ j, Action j) =>
      x i p.1 * ((∏ j, x j (p.2 j)) * G.payoff p.2 i)) (by
        rintro ⟨a, profile⟩
        dsimp [swapOwn]
        rw [← mul_assoc, ← mul_assoc, weight_swap x i a profile])
  simp only [Fintype.sum_prod_type] at h
  simp only [Finset.mul_sum]
  rw [h]
  rw [← Finset.sum_comm]
  simp only [Finset.sum_mul]

/-- Each row derivative vanishes identically for arbitrary ambient coordinates. -/
theorem sum_ambientReplicatorVector (G : FiniteNormalFormGame Player Action)
    (x : ProfileCoordinates Player Action) (i : Player) :
    ∑ a, ambientReplicatorVector G x i a = 0 := by
  simp only [ambientReplicatorVector, mul_sub, Finset.sum_sub_distrib]
  rw [sum_ambient_deviation, ← Finset.sum_mul]
  exact sub_self _

end EconCSLib.OpenProblem.New.EconCSBench.MeaningOfAGame.FlowExistence

end


section

/-!
Two-sided sign preservation for scalar equations with a continuous coefficient.
-/

open MeasureTheory

namespace EconCSLib.OpenProblem.New.EconCSBench.MeaningOfAGame.FlowExistence.BoundedODE

/-- The integrating-factor identity is valid at positive and negative times. -/
theorem linear_solution_mul_exp_integral
    {y c : ℝ → ℝ} (hc : Continuous c)
    (hy : ∀ t, HasDerivAt y (c t * y t) t) (t : ℝ) :
    y t * Real.exp (-(∫ s in 0..t, c s)) = y 0 := by
  have hintegral (u : ℝ) :
      HasDerivAt (fun v => ∫ s in 0..v, c s) (c u) u :=
    intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _)
      hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  have hderiv (u : ℝ) : HasDerivAt
      (fun v => y v * Real.exp (-(∫ s in 0..v, c s))) 0 u := by
    convert (hy u).mul (hintegral u).neg.exp using 1
    ring
  have hconstant := is_const_of_deriv_eq_zero
    (fun u => (hderiv u).differentiableAt) (fun u => (hderiv u).deriv) t 0
  simpa using hconstant

/-- Nonnegative initial coordinates stay nonnegative for all real times. -/
theorem linear_solution_nonneg
    {y c : ℝ → ℝ} (hc : Continuous c)
    (hy : ∀ t, HasDerivAt y (c t * y t) t) (hzero : 0 ≤ y 0) (t : ℝ) :
    0 ≤ y t := by
  have h := linear_solution_mul_exp_integral hc hy t
  exact (mul_nonneg_iff_of_pos_right (Real.exp_pos _)).mp (h.symm ▸ hzero)

/-- Initially zero coordinates remain zero for all real times. -/
theorem linear_solution_zero
    {y c : ℝ → ℝ} (hc : Continuous c)
    (hy : ∀ t, HasDerivAt y (c t * y t) t) (hzero : y 0 = 0) (t : ℝ) :
    y t = 0 := by
  have h := linear_solution_mul_exp_integral hc hy t
  rw [hzero] at h
  exact (mul_eq_zero.mp h).resolve_right (Real.exp_ne_zero _)

end EconCSLib.OpenProblem.New.EconCSBench.MeaningOfAGame.FlowExistence.BoundedODE

end


section

/-!
Boundary and support invariance for any certified replicator semantics.
-/

open scoped BigOperators

namespace EconCSLib.OpenProblem.New.EconCSBench.MeaningOfAGame

variable {Player : Type*} {Action : Player → Type*}
  [Fintype Player] [DecidableEq Player] [∀ i, Fintype (Action i)]

private theorem continuous_payoff_advantage
    (G : FiniteNormalFormGame Player Action) (i : Player) (a : Action i) :
    Continuous (fun x : MixedProfile Player Action =>
      pureDeviationPayoff G x i a - mixedExpectedPayoff G x i) := by
  have hcoord (j : Player) (b : Action j) :
      Continuous (fun x : MixedProfile Player Action => (x j).val b) :=
    (continuous_apply b).comp (continuous_subtype_val.comp (continuous_apply j))
  have hprod (profile : ∀ j, Action j) :
      Continuous (fun x : MixedProfile Player Action => ∏ j, (x j).val (profile j)) :=
    continuous_finsetProd _ fun j _ => hcoord j (profile j)
  exact (continuous_finsetSum _ fun profile _ => (hprod profile).mul continuous_const).sub
    (continuous_finsetSum _ fun profile _ => (hprod profile).mul continuous_const)

variable {G : FiniteNormalFormGame Player Action} (dynamics : ReplicatorSemantics G)

/-- An initially absent action stays absent at every positive or negative time. -/
theorem ReplicatorSemantics.coordinate_zero_of_zero
    (x : MixedProfile Player Action) (i : Player) (a : Action i)
    (hx : (x i).val a = 0) (t : ℝ) : ((dynamics.flow t x) i).val a = 0 := by
  have hc := (continuous_payoff_advantage G i a).comp
    (dynamics.flow.continuous continuous_id continuous_const (f := fun _ : ℝ => x))
  refine EconCSLib.OpenProblem.New.EconCSBench.MeaningOfAGame.FlowExistence.BoundedODE.linear_solution_zero
    (y := fun s => ((dynamics.flow s x) i).val a) hc ?_ ?_ t
  · intro s
    convert dynamics.solvesODE x i a s using 1
    simp only [replicatorVector, Function.comp_apply, id_eq]
    ring
  · simpa using hx

/-- Positive coordinates stay positive at every positive or negative time. -/
theorem ReplicatorSemantics.coordinate_pos_of_pos
    (x : MixedProfile Player Action) (i : Player) (a : Action i)
    (hx : 0 < (x i).val a) (t : ℝ) : 0 < ((dynamics.flow t x) i).val a := by
  have hc := (continuous_payoff_advantage G i a).comp
    (dynamics.flow.continuous continuous_id continuous_const (f := fun _ : ℝ => x))
  have hy (s : ℝ) : HasDerivAt (fun u => ((dynamics.flow u x) i).val a)
      ((pureDeviationPayoff G (dynamics.flow s x) i a -
        mixedExpectedPayoff G (dynamics.flow s x) i) * ((dynamics.flow s x) i).val a) s := by
    convert dynamics.solvesODE x i a s using 1
    simp only [replicatorVector]
    ring
  have h := EconCSLib.OpenProblem.New.EconCSBench.MeaningOfAGame.FlowExistence.BoundedODE.linear_solution_mul_exp_integral hc hy t
  have hpositive : 0 < ((dynamics.flow 0 x) i).val a := by simpa using hx
  exact (mul_pos_iff_of_pos_right (Real.exp_pos _)).mp (h.symm ▸ hpositive)

/-- Backward flow gives the converse, so the support is exactly invariant. -/
theorem ReplicatorSemantics.coordinate_zero_iff
    (x : MixedProfile Player Action) (i : Player) (a : Action i) (t : ℝ) :
    ((dynamics.flow t x) i).val a = 0 ↔ (x i).val a = 0 := by
  constructor
  · intro h
    have hz := dynamics.coordinate_zero_of_zero (dynamics.flow t x) i a h (-t)
    simpa only [← dynamics.flow.map_add, neg_add_cancel, Flow.map_zero_apply] using hz
  · exact fun h => dynamics.coordinate_zero_of_zero x i a h t

end EconCSLib.OpenProblem.New.EconCSBench.MeaningOfAGame

end


section

/-!
A compactly supported smooth extension of the replicator vector field.
-/

open scoped BigOperators
open Set Metric

namespace EconCSLib.OpenProblem.New.EconCSBench.MeaningOfAGame.FlowExistence

variable {Player : Type*} {Action : Player → Type*}
  [Fintype Player] [DecidableEq Player] [∀ i, Fintype (Action i)]

noncomputable def ambientCutoff :
    ContDiffBump (0 : ProfileCoordinates Player Action) :=
  ⟨1, 2, zero_lt_one, one_lt_two⟩

noncomputable def boundedReplicatorVector (G : FiniteNormalFormGame Player Action)
    (x : ProfileCoordinates Player Action) : ProfileCoordinates Player Action :=
  (ambientCutoff (Player := Player) (Action := Action) :
    ProfileCoordinates Player Action → ℝ) x • ambientReplicatorVector G x

theorem boundedReplicatorVector_eq (G : FiniteNormalFormGame Player Action)
    (x : MixedProfile Player Action) :
    boundedReplicatorVector G (mixedProfileCoordinates x) = replicatorVector G x := by
  unfold boundedReplicatorVector
  rw [(ambientCutoff (Player := Player) (Action := Action)).one_of_mem_closedBall
    (mixedProfileCoordinates_mem_closedBall x)]
  simp only [one_smul, ambientReplicatorVector_coordinates]

theorem contDiff_boundedReplicatorVector (G : FiniteNormalFormGame Player Action) :
    ContDiff ℝ 1 (boundedReplicatorVector G) :=
  (ambientCutoff (Player := Player) (Action := Action)).contDiff.smul
    (contDiff_ambientReplicatorVector G)

theorem compactSupport_boundedReplicatorVector (G : FiniteNormalFormGame Player Action) :
    HasCompactSupport (boundedReplicatorVector G) := by
  have hbump : HasCompactSupport
      (ambientCutoff (Player := Player) (Action := Action) :
        ProfileCoordinates Player Action → ℝ) :=
    (ambientCutoff (Player := Player) (Action := Action)).hasCompactSupport
  have h := HasCompactSupport.smul_right (f' := ambientReplicatorVector G) hbump
  simpa only [Pi.smul_apply', boundedReplicatorVector] using h

theorem lipschitz_boundedReplicatorVector (G : FiniteNormalFormGame Player Action) :
    ∃ K, LipschitzWith K (boundedReplicatorVector G) :=
  ContDiff.lipschitzWith_of_hasCompactSupport (compactSupport_boundedReplicatorVector G)
    (contDiff_boundedReplicatorVector G) (by norm_num)

theorem norm_boundedReplicatorVector (G : FiniteNormalFormGame Player Action) :
    ∃ L : ℝ, ∀ x, ‖boundedReplicatorVector G x‖ ≤ L :=
  (compactSupport_boundedReplicatorVector G).exists_bound_of_continuous
    (contDiff_boundedReplicatorVector G).continuous

theorem local_ambient_existence (G : FiniteNormalFormGame Player Action)
    (x : ProfileCoordinates Player Action) (t₀ : ℝ) :
    ∃ curve : ℝ → ProfileCoordinates Player Action, curve t₀ = x ∧
      ∃ ε > (0 : ℝ), ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε),
        HasDerivAt curve (ambientReplicatorVector G (curve t)) t :=
  ContDiffAt.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀
    ((contDiff_ambientReplicatorVector G).contDiffAt (x := x)) t₀

end EconCSLib.OpenProblem.New.EconCSBench.MeaningOfAGame.FlowExistence

end


section

/-!
Global bounded ODE flows from native Picard--Lindelöf and uniqueness.
-/

open Set Metric Filter
open scoped Topology NNReal

namespace EconCSLib.OpenProblem.New.EconCSBench.MeaningOfAGame.FlowExistence.BoundedODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {f : E → E} {L K : ℝ≥0}

/-- Global norm and Lipschitz bounds give a solution on every finite time interval. -/
theorem exists_solution_on_interval
    (hbound : ∀ x, ‖f x‖ ≤ L) (hlip : LipschitzWith K f)
    (x : E) (T : ℝ) (hT : 0 < T) :
    ∃ curve : ℝ → E, curve 0 = x ∧
      ∀ t ∈ Ioo (-T) T, HasDerivAt curve (f (curve t)) t := by
  let a : ℝ≥0 := ⟨L * T, mul_nonneg L.coe_nonneg hT.le⟩
  have hpl : IsPicardLindelof (fun _ : ℝ => f)
      (tmin := -T) (tmax := T) ⟨0, by constructor <;> linarith⟩ x a 0 L K :=
    IsPicardLindelof.of_time_independent (fun y _ => hbound y)
      hlip.lipschitzOnWith (by
        change (L : ℝ) * max (T - 0) (0 - -T) ≤ (L : ℝ) * T - 0
        simp)
  obtain ⟨curve, hzero, hderiv⟩ := hpl.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  exact ⟨curve, hzero, fun t ht =>
    (hderiv t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)⟩

omit [CompleteSpace E] in
/-- Two local solutions with the same initial value agree on their overlap. -/
theorem interval_solutions_agree (hlip : LipschitzWith K f)
    {left right : ℝ → E} {R S : ℝ} (hR : 0 < R) (hS : 0 < S)
    (hleft : ∀ t ∈ Ioo (-R) R, HasDerivAt left (f (left t)) t)
    (hright : ∀ t ∈ Ioo (-S) S, HasDerivAt right (f (right t)) t)
    (hzero : left 0 = right 0) {t : ℝ}
    (htR : t ∈ Ioo (-R) R) (htS : t ∈ Ioo (-S) S) : left t = right t := by
  have hpositive : 0 < min R S := lt_min hR hS
  have hsubR : Ioo (-(min R S)) (min R S) ⊆ Ioo (-R) R :=
    Ioo_subset_Ioo (neg_le_neg (min_le_left _ _)) (min_le_left _ _)
  have hsubS : Ioo (-(min R S)) (min R S) ⊆ Ioo (-S) S :=
    Ioo_subset_Ioo (neg_le_neg (min_le_right _ _)) (min_le_right _ _)
  have heq := ODE_solution_unique_of_mem_Ioo
    (s := fun _ : ℝ => (Set.univ : Set E)) (v := fun _ : ℝ => f)
    (t₀ := 0) (fun _ _ => hlip.lipschitzOnWith)
    (show 0 ∈ Ioo (-(min R S)) (min R S) from ⟨by linarith, hpositive⟩)
    (fun t ht => ⟨hleft t (hsubR ht), Set.mem_univ _⟩)
    (fun t ht => ⟨hright t (hsubS ht), Set.mem_univ _⟩) hzero
  apply heq
  constructor
  · have hmin : -t < min R S := lt_min (by linarith [htR.1]) (by linarith [htS.1])
    linarith
  · exact lt_min htR.2 htS.2

/-- A bounded globally Lipschitz autonomous field has a global solution through every
initial point. This theorem does not yet construct a jointly continuous flow. -/
theorem exists_global_solution
    (hbound : ∀ x, ‖f x‖ ≤ L) (hlip : LipschitzWith K f) (x : E) :
    ∃ curve : ℝ → E, curve 0 = x ∧ ∀ t, HasDerivAt curve (f (curve t)) t := by
  classical
  have hlocal := fun r : ℝ =>
    exists_solution_on_interval hbound hlip x (|r| + 1) (by positivity)
  choose localCurve hzero hderiv using hlocal
  let curve : ℝ → E := fun t => localCurve t t
  have hself (t : ℝ) : t ∈ Ioo (-(|t| + 1)) (|t| + 1) :=
    abs_lt.mp (by linarith : |t| < |t| + 1)
  have hagree (r t : ℝ) (ht : t ∈ Ioo (-(|r| + 1)) (|r| + 1)) :
      curve t = localCurve r t :=
    interval_solutions_agree hlip (by positivity) (by positivity)
      (hderiv t) (hderiv r) ((hzero t).trans (hzero r).symm) (hself t) ht
  refine ⟨curve, hzero 0, ?_⟩
  intro t
  have hevent : curve =ᶠ[𝓝 t] localCurve t := by
    filter_upwards [Ioo_mem_nhds (hself t).1 (hself t).2] with s hs
    exact hagree t s hs
  have hd := hderiv t t (hself t)
  simpa only [curve] using hd.congr_of_eventuallyEq hevent

/-- Bounded globally Lipschitz autonomous fields generate jointly continuous two-sided
flows. Joint continuity is proved from the local family theorem, not inferred from
choosing one curve at each initial point. -/
theorem exists_global_flow
    (hbound : ∀ x, ‖f x‖ ≤ L) (hlip : LipschitzWith K f) :
    ∃ dynamics : Flow ℝ E, ∀ x t, HasDerivAt (fun s => dynamics s x)
      (f (dynamics t x)) t := by
  classical
  choose curve hzero hderiv using fun x => exists_global_solution hbound hlip x
  have hcontinuous : Continuous (fun p : E × ℝ => curve p.1 p.2) := by
    apply continuous_iff_continuousAt.mpr
    intro p
    let T : ℝ := |p.2| + 1
    have hT : 0 < T := by dsimp [T]; positivity
    have hpT : p.2 ∈ Ioo (-T) T := abs_lt.mp (by dsimp [T]; linarith)
    let a : ℝ≥0 := ⟨L * T + 1, by positivity⟩
    have hpl : IsPicardLindelof (fun _ : ℝ => f)
        (tmin := -T) (tmax := T) ⟨0, by constructor <;> linarith⟩ p.1 a 1 L K :=
      IsPicardLindelof.of_time_independent (fun y _ => hbound y)
        hlip.lipschitzOnWith (by
          change (L : ℝ) * max (T - 0) (0 - -T) ≤ (L : ℝ) * T + 1 - 1
          simp)
    obtain ⟨localCurve, hlocal, hcont⟩ :=
      hpl.exists_forall_mem_closedBall_eq_hasDerivWithinAt_continuousOn
    have hcontAt : ContinuousAt localCurve p :=
      hcont.continuousAt (prod_mem_nhds (closedBall_mem_nhds p.1 (by norm_num))
        (Icc_mem_nhds hpT.1 hpT.2))
    apply hcontAt.congr_of_eventuallyEq
    filter_upwards [prod_mem_nhds (closedBall_mem_nhds p.1 (by norm_num : (0 : ℝ) < 1))
      (Ioo_mem_nhds hpT.1 hpT.2)] with q hq
    exact interval_solutions_agree hlip hT hT
      (fun t _ => hderiv q.1 t)
      (fun t ht => ((hlocal q.1 hq.1).2 t (Ioo_subset_Icc_self ht)).hasDerivAt
        (Icc_mem_nhds ht.1 ht.2))
      ((hzero q.1).trans (hlocal q.1 hq.1).1.symm) hq.2 hq.2
  have hadd (t₁ t₂ : ℝ) (x : E) :
      curve x (t₁ + t₂) = curve (curve x t₂) t₁ := by
    have hshift (t : ℝ) : HasDerivAt (fun s => curve x (s + t₂))
        (f (curve x (t + t₂))) t := by
      simpa only [one_smul] using
        (hderiv x (t + t₂)).scomp t ((hasDerivAt_id t).add_const t₂)
    have heq := ODE_solution_unique_univ
      (s := fun _ : ℝ => (Set.univ : Set E)) (v := fun _ : ℝ => f)
      (t₀ := 0) (fun _ => hlip.lipschitzOnWith)
      (fun t => ⟨hshift t, Set.mem_univ _⟩)
      (fun t => ⟨hderiv (curve x t₂) t, Set.mem_univ _⟩)
      (by simpa only [zero_add] using (hzero (curve x t₂)).symm)
    exact congrFun heq t₁
  refine ⟨{
    toFun := fun t x => curve x t
    cont' := hcontinuous.comp (continuous_snd.prodMk continuous_fst)
    map_add' := hadd
    map_zero' := hzero
  }, ?_⟩
  exact hderiv

end EconCSLib.OpenProblem.New.EconCSBench.MeaningOfAGame.FlowExistence.BoundedODE

end


section

/-!
A genuine global ambient flow for the cutoff field, before simplex invariance.
-/

open scoped NNReal

namespace EconCSLib.OpenProblem.New.EconCSBench.MeaningOfAGame.FlowExistence

theorem exists_global_cutoff_flow
    {Player : Type*} {Action : Player → Type*}
    [Fintype Player] [DecidableEq Player] [∀ i, Fintype (Action i)]
    (G : FiniteNormalFormGame Player Action) :
    ∃ dynamics : Flow ℝ (ProfileCoordinates Player Action), ∀ x t,
      HasDerivAt (fun s => dynamics s x) (boundedReplicatorVector G (dynamics t x)) t := by
  obtain ⟨K, hK⟩ := lipschitz_boundedReplicatorVector G
  obtain ⟨C, hC⟩ := norm_boundedReplicatorVector G
  let L : ℝ≥0 := ⟨max C 0, le_max_right _ _⟩
  apply EconCSLib.OpenProblem.New.EconCSBench.MeaningOfAGame.FlowExistence.BoundedODE.exists_global_flow (L := L) (K := K)
  · intro x
    exact (hC x).trans (le_max_left _ _)
  · exact hK

end EconCSLib.OpenProblem.New.EconCSBench.MeaningOfAGame.FlowExistence

end


section

/-!
The cutoff flow preserves every simplex constraint for all real times.
-/

open scoped BigOperators

namespace EconCSLib.OpenProblem.New.EconCSBench.MeaningOfAGame.FlowExistence

variable {Player : Type*} {Action : Player → Type*}
  [Fintype Player] [DecidableEq Player] [∀ i, Fintype (Action i)]

noncomputable def cutoffCoefficient (G : FiniteNormalFormGame Player Action)
    (i : Player) (a : Action i) (x : ProfileCoordinates Player Action) : ℝ :=
  (ambientCutoff (Player := Player) (Action := Action) :
    ProfileCoordinates Player Action → ℝ) x *
    ((∑ profile : ∀ j, Action j,
      (∏ j, x j (profile j)) * G.payoff (Function.update profile i a) i) -
     (∑ profile : ∀ j, Action j,
      (∏ j, x j (profile j)) * G.payoff profile i))

theorem continuous_cutoffCoefficient (G : FiniteNormalFormGame Player Action)
    (i : Player) (a : Action i) : Continuous (cutoffCoefficient G i a) := by
  have hcoord (j : Player) (b : Action j) :
      Continuous (fun x : ProfileCoordinates Player Action => x j b) :=
    (continuous_apply b).comp (continuous_apply j)
  have hprod (profile : ∀ j, Action j) :
      Continuous (fun x : ProfileCoordinates Player Action => ∏ j, x j (profile j)) :=
    continuous_finsetProd _ fun j _ => hcoord j (profile j)
  unfold cutoffCoefficient
  exact (ambientCutoff (Player := Player) (Action := Action)).continuous.mul
    ((continuous_finsetSum _ fun profile _ => (hprod profile).mul continuous_const).sub
      (continuous_finsetSum _ fun profile _ => (hprod profile).mul continuous_const))

theorem sum_boundedReplicatorVector (G : FiniteNormalFormGame Player Action)
    (x : ProfileCoordinates Player Action) (i : Player) :
    ∑ a, boundedReplicatorVector G x i a = 0 := by
  simp only [boundedReplicatorVector, Pi.smul_apply, smul_eq_mul]
  rw [← Finset.mul_sum, sum_ambientReplicatorVector, mul_zero]

variable {G : FiniteNormalFormGame Player Action}
    (dynamics : Flow ℝ (ProfileCoordinates Player Action))
    (hsolve : ∀ x t, HasDerivAt (fun s => dynamics s x)
      (boundedReplicatorVector G (dynamics t x)) t)

include hsolve

/-- Initially nonnegative coordinates remain nonnegative in both time directions. -/
theorem cutoff_flow_nonneg (x : MixedProfile Player Action) (t : ℝ)
    (i : Player) (a : Action i) :
    0 ≤ dynamics t (mixedProfileCoordinates x) i a := by
  let curve : ℝ → ProfileCoordinates Player Action :=
    fun s => dynamics s (mixedProfileCoordinates x)
  have hcont : Continuous curve :=
    dynamics.cont'.comp (continuous_id.prodMk continuous_const)
  have hcoord (s : ℝ) : HasDerivAt (fun u => curve u i a)
      (boundedReplicatorVector G (curve s) i a) s :=
    hasDerivAt_pi.mp (hasDerivAt_pi.mp (hsolve (mixedProfileCoordinates x) s) i) a
  refine EconCSLib.OpenProblem.New.EconCSBench.MeaningOfAGame.FlowExistence.BoundedODE.linear_solution_nonneg
    (y := fun u => curve u i a)
    ((continuous_cutoffCoefficient G i a).comp hcont) ?_ ?_ t
  · intro s
    convert hcoord s using 1
    dsimp [cutoffCoefficient, boundedReplicatorVector, ambientReplicatorVector]
    ring
  · simpa [curve, mixedProfileCoordinates] using (x i).property.1 a

/-- Row sums are preserved exactly, without assuming normalization along the curve. -/
theorem cutoff_flow_sum (x : MixedProfile Player Action) (t : ℝ) (i : Player) :
    ∑ a, dynamics t (mixedProfileCoordinates x) i a = 1 := by
  have hcoord (a : Action i) (s : ℝ) :
      HasDerivAt (fun u => dynamics u (mixedProfileCoordinates x) i a)
        (boundedReplicatorVector G (dynamics s (mixedProfileCoordinates x)) i a) s :=
    hasDerivAt_pi.mp (hasDerivAt_pi.mp (hsolve (mixedProfileCoordinates x) s) i) a
  have hrow (s : ℝ) :
      HasDerivAt (fun u => ∑ a, dynamics u (mixedProfileCoordinates x) i a) 0 s := by
    simpa only [sum_boundedReplicatorVector] using
      HasDerivAt.fun_sum (u := Finset.univ) (fun a _ => hcoord a s)
  have hconstant := is_const_of_deriv_eq_zero
    (fun s => (hrow s).differentiableAt) (fun s => (hrow s).deriv) t 0
  calc
    (∑ a, dynamics t (mixedProfileCoordinates x) i a) =
        ∑ a, dynamics 0 (mixedProfileCoordinates x) i a := hconstant
    _ = 1 := by simpa [mixedProfileCoordinates] using (x i).property.2

end EconCSLib.OpenProblem.New.EconCSBench.MeaningOfAGame.FlowExistence

end


section

/-!
Existence of the original two-sided replicator flow without extra axioms.
-/

namespace EconCSLib.OpenProblem.New.EconCSBench.MeaningOfAGame

open FlowExistence

/-- Every finite normal-form game has a globally defined, jointly continuous replicator
flow on its full product of simplices, including boundary profiles. -/
theorem nonempty_replicatorSemantics
    {Player : Type*} {Action : Player → Type*}
    [Fintype Player] [DecidableEq Player] [∀ i, Fintype (Action i)]
    (G : FiniteNormalFormGame Player Action) : Nonempty (ReplicatorSemantics G) := by
  classical
  obtain ⟨ambientFlow, hsolve⟩ := exists_global_cutoff_flow G
  let mixedFlow : ℝ → MixedProfile Player Action → MixedProfile Player Action :=
    fun t x i => ⟨ambientFlow t (mixedProfileCoordinates x) i,
      ⟨fun a => cutoff_flow_nonneg ambientFlow hsolve x t i a,
        cutoff_flow_sum ambientFlow hsolve x t i⟩⟩
  have hcoords (t : ℝ) (x : MixedProfile Player Action) :
      mixedProfileCoordinates (mixedFlow t x) =
        ambientFlow t (mixedProfileCoordinates x) := rfl
  have hcoordinates : Continuous (mixedProfileCoordinates (Player := Player) (Action := Action)) := by
    apply continuous_pi
    intro i
    exact continuous_subtype_val.comp (continuous_apply i)
  have hambient : Continuous (fun p : ℝ × MixedProfile Player Action =>
      ambientFlow p.1 (mixedProfileCoordinates p.2)) :=
    ambientFlow.continuous continuous_fst (hcoordinates.comp continuous_snd)
  have hcontinuous : Continuous (Function.uncurry mixedFlow) := by
    apply continuous_pi
    intro i
    exact ((continuous_apply i).comp hambient).subtype_mk _
  let dynamics : Flow ℝ (MixedProfile Player Action) := {
    toFun := mixedFlow
    cont' := hcontinuous
    map_add' := by
      intro t₁ t₂ x
      funext i
      apply Subtype.ext
      change ambientFlow (t₁ + t₂) (mixedProfileCoordinates x) i =
        ambientFlow t₁ (mixedProfileCoordinates (mixedFlow t₂ x)) i
      rw [hcoords, ambientFlow.map_add]
    map_zero' := by
      intro x
      funext i
      apply Subtype.ext
      change ambientFlow 0 (mixedProfileCoordinates x) i = (x i).val
      simp [mixedProfileCoordinates]
  }
  refine ⟨{ flow := dynamics, solvesODE := ?_ }⟩
  intro x i a t
  have hderiv := hasDerivAt_pi.mp
    (hasDerivAt_pi.mp (hsolve (mixedProfileCoordinates x) t) i) a
  have heq : boundedReplicatorVector G (ambientFlow t (mixedProfileCoordinates x)) =
      replicatorVector G (mixedFlow t x) := by
    rw [← hcoords]
    exact boundedReplicatorVector_eq G (mixedFlow t x)
  change HasDerivAt (fun s => ambientFlow s (mixedProfileCoordinates x) i a)
    (replicatorVector G (mixedFlow t x) i a) t
  simpa only [heq] using hderiv

end EconCSLib.OpenProblem.New.EconCSBench.MeaningOfAGame

end


section

/-!
## Description-language schemas on presented real inputs

The fixed input presentation covers only its range, not every real input. The language
is also fixed before the solver. These denotation schemas do not themselves certify
effectiveness or exclude a codebook hiding answers. A concrete computational
interpretation needs a justified syntax and interpretation; a distance-name
specialization is supplied separately.
-/
namespace EconCSLib.OpenProblem.New.EconCSBench.MeaningOfAGame
open WordRAM.FiniteData

/-- Description-level collection correctness. -/
def PresentedAttractorCollectionSolution (dynamics : RealReplicatorModel)
    (language : AttractorCollectionLanguage) (G : RealGame) (output : Code) : Prop :=
  language.denotes G.shape output = some (dynamics G).attractors

/-- A concrete collection frame around descriptions in the fixed set language. -/
def PresentedListedAttractorCollectionSolution (dynamics : RealReplicatorModel)
    (language : AttractorSetLanguage) (G : RealGame) (output : Code) : Prop :=
  ∃ descriptions, output = descriptionListCode descriptions ∧
    DescribesAttractors language G.shape (dynamics G) descriptions

def PresentedLimitAttractorSolution (dynamics : RealReplicatorModel)
    (language : AttractorSetLanguage) (I : RealStart) (output : Code) : Prop :=
  ∃ A, language.denotes I.game.shape output = some A ∧
    RealLimitAttractorSolution dynamics I A

/-- Canonically tagged finite descriptions for the separate total diagnosis. -/
inductive EncodedLimitDiagnosisOutput
  | attractor (description : Code)
  | noApproachedAttractor
  deriving DecidableEq

def EncodedLimitDiagnosisSolution (dynamics : RealReplicatorModel)
    (language : AttractorSetLanguage) (I : RealStart) :
    EncodedLimitDiagnosisOutput → Prop
  | .attractor description => PresentedLimitAttractorSolution dynamics language I description
  | .noApproachedAttractor => ¬ (dynamics I.game).HasLimitAttractor I.profile

def EncodedLimitDiagnosisOutput.encode : EncodedLimitDiagnosisOutput → Code
  | .attractor description => true :: description
  | .noApproachedAttractor => [false]

/-- Only the canonical negative tag is accepted; malformed outputs fail. -/
def EncodedLimitDiagnosisOutput.decode : Code → Option EncodedLimitDiagnosisOutput
  | true :: description => some (.attractor description)
  | [false] => some .noApproachedAttractor
  | _ => none

theorem EncodedLimitDiagnosisOutput.decode_encode (output : EncodedLimitDiagnosisOutput) :
    decode output.encode = some output := by
  cases output <;> rfl

/-- Polynomial-time computation relative to a collection-description language. -/
def PresentedCollectionDenotationAttractorComputationSchema (dynamics : RealReplicatorModel)
    (language : AttractorCollectionLanguage) (readInput : Code → Option RealGame) : Prop :=
  let presentation : ExecutionContracts.Presentation RealGame Code :=
    ⟨readInput, fun code => some code⟩
  let task := presentation.searchProblem (fun _ => True)
    (PresentedAttractorCollectionSolution dynamics language)
  WordRAM.Search.PolynomiallySolvable task.valid task.solution

/-- Fixed finite-list output, with no separate collection-denotation decoder. -/
def AttractorComputationPresentedWordRAMQuestion (dynamics : RealReplicatorModel)
    (language : AttractorSetLanguage) (readInput : Code → Option RealGame) : Prop :=
  let presentation : ExecutionContracts.Presentation RealGame Code :=
    ⟨readInput, fun code => some code⟩
  let task := presentation.searchProblem (fun _ => True)
    (PresentedListedAttractorCollectionSolution dynamics language)
  WordRAM.Search.PolynomiallySolvable task.valid task.solution

/-- Literal all-input prediction within the explicitly presented domain. -/
def LiteralLimitPredictionQuestion (dynamics : RealReplicatorModel)
    (language : AttractorSetLanguage) (readInput : Code → Option RealStart) : Prop :=
  let presentation : ExecutionContracts.Presentation RealStart Code :=
    ⟨readInput, fun code => some code⟩
  let task := presentation.searchProblem (fun _ => True)
    (PresentedLimitAttractorSolution dynamics language)
  WordRAM.Search.PolynomiallySolvable task.valid task.solution

/-- Project correction: solve inside the basin union, without deciding its membership. -/
def BasinPromisedLimitPredictionQuestion (dynamics : RealReplicatorModel)
    (language : AttractorSetLanguage) (readInput : Code → Option RealStart) : Prop :=
  let presentation : ExecutionContracts.Presentation RealStart Code :=
    ⟨readInput, fun code => some code⟩
  let task := presentation.searchProblem
    (fun I => (dynamics I.game).HasLimitAttractor I.profile)
    (PresentedLimitAttractorSolution dynamics language)
  WordRAM.Search.PolynomiallySolvable task.valid task.solution

/-- Separate extension deciding the outside-basin case as well. A bare negative tag
asserts a fact; it is not an efficiently checked certificate. -/
def TotalLimitDiagnosisQuestion (dynamics : RealReplicatorModel)
    (language : AttractorSetLanguage) (readInput : Code → Option RealStart) : Prop :=
  let presentation : ExecutionContracts.Presentation RealStart EncodedLimitDiagnosisOutput :=
    ⟨readInput, EncodedLimitDiagnosisOutput.decode⟩
  let task := presentation.searchProblem (fun _ => True)
    (EncodedLimitDiagnosisSolution dynamics language)
  WordRAM.Search.PolynomiallySolvable task.valid task.solution

/-- Compatibility names retain the original presented-domain interfaces. -/
abbrev LimitPredictionPresentedWordRAMQuestion := LiteralLimitPredictionQuestion
abbrev TotalLimitPredictionPresentedWordRAMQuestion := TotalLimitDiagnosisQuestion

/-- No description language or polynomial runtime can supply an absent attractor at an
input actually covered by the presentation. -/
theorem not_literalPrediction_of_represented_outside_basin
    (dynamics : RealReplicatorModel) (language : AttractorSetLanguage)
    (readInput : Code → Option RealStart) (I : RealStart) (code : Code)
    (represented : readInput code = some I)
    (outside : ¬ (dynamics I.game).HasLimitAttractor I.profile) :
    ¬ LiteralLimitPredictionQuestion dynamics language readInput := by
  rintro ⟨_, solver, _⟩
  obtain ⟨output, _, J, description, decoded, _, A, _, correct⟩ :=
    solver.correct code ⟨I, represented, trivial⟩
  have same : J = I := Option.some.inj (decoded.symm.trans represented)
  subst J
  exact outside ⟨A, correct⟩

end EconCSLib.OpenProblem.New.EconCSBench.MeaningOfAGame

end


section

/-!
## The all-start obstruction at the problem entry points

The strict coordination fixture is an actual full-real input. Its obstruction is
independent of runtime and output language. The computational corollary applies to
every fixed presentation that includes this input; it does not assume that a finite
presentation covers all real games or profiles.
-/
namespace EconCSLib.OpenProblem.New.EconCSBench.MeaningOfAGame
namespace CoordinationFixture
open WordRAM.FiniteData

def realGame : RealGame := ⟨shape, game⟩

noncomputable def realStart : RealStart := ⟨realGame, center⟩

/-- No full-real semantic predictor can satisfy the literal all-start contract. -/
theorem not_isRealLimitPrediction (dynamics : RealReplicatorModel) :
    ¬ ∃ solve, IsRealLimitPrediction dynamics solve :=
  no_literal_predictor_of_outside_basin dynamics realStart
    (center_has_no_limit_attractor (dynamics realGame))

/-- An implementation cannot fix a literal input for which no answer exists. -/
theorem not_literalLimitPredictionQuestion (dynamics : RealReplicatorModel)
    (language : AttractorSetLanguage) (readInput : Code → Option RealStart)
    (code : Code) (represented : readInput code = some realStart) :
    ¬ LiteralLimitPredictionQuestion dynamics language readInput :=
  not_literalPrediction_of_represented_outside_basin dynamics language readInput
    realStart code represented (center_has_no_limit_attractor (dynamics realGame))

/-- The total diagnosis has a correct negative answer at the same input. -/
theorem correct_negative_diagnosis (dynamics : RealReplicatorModel) :
    TotalLimitDiagnosisSolution dynamics realStart .noApproachedAttractor :=
  center_has_no_limit_attractor (dynamics realGame)

/-- The basin-promise explicitly excludes this interior stationary input. -/
theorem outside_basin_promise (dynamics : RealReplicatorModel) :
    ¬ (dynamics realGame).HasLimitAttractor realStart.profile :=
  center_has_no_limit_attractor (dynamics realGame)

end CoordinationFixture
end EconCSLib.OpenProblem.New.EconCSBench.MeaningOfAGame

end


section

/-!
## The semantic law of attractor labels, with residual mass

Uniqueness and open basins give a measurable, noncomputable canonical labeling. Its
labels are actual minimal attracting sets, with `none` for outside-basin starts. The
label sigma-algebra is discrete. This semantic construction gives neither an effective
attractor description nor a basin-membership algorithm.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace EconCSLib.OpenProblem.New.EconCSBench.MeaningOfAGame

/-- Actual minimal-attractor labels, with one residual label; no finite codes. -/
def AttractorLabelSpace {G : RealGame} (dynamics : ReplicatorSemantics G.game) :=
  Option dynamics.attractors

/-- Every subset of labels is measurable; this is a semantic, not effective, space. -/
instance {G : RealGame} (dynamics : ReplicatorSemantics G.game) :
    MeasurableSpace (AttractorLabelSpace dynamics) := ⊤

/-- Choose the unique approached attractor when it exists, otherwise the residual label. -/
noncomputable def ReplicatorSemantics.canonicalBasinLabel {G : RealGame}
    (dynamics : ReplicatorSemantics G.game) (x : G.shape.RealProfile) :
    AttractorLabelSpace dynamics := by
  classical
  exact if h : dynamics.HasLimitAttractor x then
    some ⟨Classical.choose h, (Classical.choose_spec h).1⟩ else none

/-- Residual labeling is exactly failure of the basin promise. -/
theorem ReplicatorSemantics.canonicalBasinLabel_none_iff {G : RealGame}
    (dynamics : ReplicatorSemantics G.game) (x : G.shape.RealProfile) :
    dynamics.canonicalBasinLabel x = none ↔ ¬ dynamics.HasLimitAttractor x := by
  classical
  by_cases h : dynamics.HasLimitAttractor x <;> simp [canonicalBasinLabel, h]

/-- The chosen label is characterized by the exact dynamical relation, not its choice
witness. -/
theorem ReplicatorSemantics.canonicalBasinLabel_some_iff {G : RealGame}
    (dynamics : ReplicatorSemantics G.game) (x : G.shape.RealProfile)
    (A : dynamics.attractors) :
    dynamics.canonicalBasinLabel x = some A ↔ dynamics.IsLimitAttractor x A.val := by
  classical
  change @Eq (Option dynamics.attractors) _ (some A) ↔ _
  by_cases h : dynamics.HasLimitAttractor x
  · simp only [canonicalBasinLabel, dif_pos h, Option.some.injEq, Subtype.ext_iff]
    constructor
    · intro heq
      simpa only [heq] using Classical.choose_spec h
    · intro hA
      exact (Classical.choose_spec h).unique hA
  · simp only [canonicalBasinLabel, dif_neg h, reduceCtorEq, false_iff]
    exact fun hA => h ⟨A.val, hA⟩

/-- Open individual basins make every collection of positive labels measurable. -/
theorem ReplicatorSemantics.measurable_canonicalBasinLabel {G : RealGame}
    (dynamics : ReplicatorSemantics G.game) : Measurable dynamics.canonicalBasinLabel := by
  classical
  intro S _
  let positive : Set G.shape.RealProfile :=
    ⋃ A : dynamics.attractors, ⋃ (_ : (some A : AttractorLabelSpace dynamics) ∈ S),
      {x | dynamics.IsLimitAttractor x A.val}
  have hpositive : IsOpen positive :=
    isOpen_iUnion fun A => isOpen_iUnion fun _ => dynamics.isOpen_limitAttractor_basin A.val
  by_cases hnone : (none : AttractorLabelSpace dynamics) ∈ S
  · have hpre : dynamics.canonicalBasinLabel ⁻¹' S = positive ∪ dynamics.basinUnionᶜ := by
      ext x
      simp only [Set.mem_preimage, Set.mem_union, positive, Set.mem_iUnion,
        Set.mem_setOf_eq, Set.mem_compl_iff, ReplicatorSemantics.basinUnion]
      cases heq : dynamics.canonicalBasinLabel x with
      | none =>
        have hx := (dynamics.canonicalBasinLabel_none_iff x).mp heq
        exact ⟨fun _ => Or.inr hx, fun _ => hnone⟩
      | some A =>
        have hx := (dynamics.canonicalBasinLabel_some_iff x A).mp heq
        constructor
        · intro hA
          exact Or.inl ⟨A, hA, hx⟩
        · rintro (⟨B, hB, hxB⟩ | hbad)
          · have heqAB : A = B := Subtype.ext (hx.unique hxB)
            simpa only [heqAB] using hB
          · exact (hbad ⟨A.val, hx⟩).elim
    rw [hpre]
    exact hpositive.measurableSet.union dynamics.measurableSet_outsideBasin
  · have hpre : dynamics.canonicalBasinLabel ⁻¹' S = positive := by
      ext x
      simp only [Set.mem_preimage, positive, Set.mem_iUnion, Set.mem_setOf_eq]
      constructor
      · intro hx
        cases heq : dynamics.canonicalBasinLabel x with
        | none => exact (hnone (heq ▸ hx)).elim
        | some A =>
          exact ⟨A, heq ▸ hx, (dynamics.canonicalBasinLabel_some_iff x A).mp heq⟩
      · rintro ⟨A, hA, hxA⟩
        rw [(dynamics.canonicalBasinLabel_some_iff x A).mpr hxA]
        exact hA
    rw [hpre]
    exact hpositive.measurableSet

/-- The full semantic meaning law; arbitrary priors retain their outside-basin mass. -/
noncomputable def ReplicatorSemantics.canonicalPriorLaw {G : RealGame}
    (dynamics : ReplicatorSemantics G.game) (prior : Measure G.shape.RealProfile) :
    Measure (AttractorLabelSpace dynamics) := prior.map dynamics.canonicalBasinLabel

/-- Probability mass is preserved without a full-basin hypothesis. -/
instance {G : RealGame} (dynamics : ReplicatorSemantics G.game)
    (prior : Measure G.shape.RealProfile) [IsProbabilityMeasure prior] :
    IsProbabilityMeasure (dynamics.canonicalPriorLaw prior) :=
  Measure.isProbabilityMeasure_map dynamics.measurable_canonicalBasinLabel.aemeasurable

/-- The semantic residual label has exactly the outside-basin mass. -/
theorem ReplicatorSemantics.canonicalPriorLaw_none {G : RealGame}
    (dynamics : ReplicatorSemantics G.game) (prior : Measure G.shape.RealProfile) :
    dynamics.canonicalPriorLaw prior {none} = dynamics.residualMass prior := by
  rw [canonicalPriorLaw, Measure.map_apply dynamics.measurable_canonicalBasinLabel
    (show MeasurableSet ({none} : Set (AttractorLabelSpace dynamics)) from trivial)]
  congr 1
  ext x
  exact dynamics.canonicalBasinLabel_none_iff x

/-- Each positive label receives exactly the initial mass of its basin. -/
theorem ReplicatorSemantics.canonicalPriorLaw_some {G : RealGame}
    (dynamics : ReplicatorSemantics G.game) (prior : Measure G.shape.RealProfile)
    (A : dynamics.attractors) :
    dynamics.canonicalPriorLaw prior {some A} =
      prior {x | dynamics.IsLimitAttractor x A.val} := by
  rw [canonicalPriorLaw, Measure.map_apply dynamics.measurable_canonicalBasinLabel
    (show MeasurableSet ({some A} : Set (AttractorLabelSpace dynamics)) from trivial)]
  congr 1
  ext x
  exact dynamics.canonicalBasinLabel_some_iff x A

/-- Attractor-only output preserves all mass precisely on basin-supported priors. -/
theorem ReplicatorSemantics.canonicalPriorLaw_none_eq_zero_iff {G : RealGame}
    (dynamics : ReplicatorSemantics G.game) (prior : Measure G.shape.RealProfile) :
    dynamics.canonicalPriorLaw prior {none} = 0 ↔ dynamics.IsBasinSupported prior := by
  rw [dynamics.canonicalPriorLaw_none prior,
    dynamics.isBasinSupported_iff_residualMass_eq_zero]

end EconCSLib.OpenProblem.New.EconCSBench.MeaningOfAGame

end


section

/-!
## Computing and predicting minimal attractors

The questions follow Biggar--Papadimitriou--Piliouras, Conjectures 6.2--6.3
(arXiv:2602.16016v2). Rational games and initial profiles have fixed encodings; set
descriptions are interpreted by a fixed output language.

The targets are computing all minimal attractors, predicting an attractor from an
initial profile in its basin, and classifying arbitrary initial profiles. The
distance-language variant represents each attractor by a program that approximates its
distance function at rational profiles.
-/
namespace EconCSLib.OpenProblem.New.EconCSBench.MeaningOfAGame
open WordRAM.FiniteData

/-- The output describes exactly all minimal attractors of this game. -/
def AttractorCollectionSolution (dynamics : ReplicatorModel)
    (language : AttractorCollectionLanguage) (input output : Code) : Prop :=
  ∃ G : RationalGame, G.code = input ∧
    language.denotes G.shape output = some (dynamics G).attractors

/-- Polynomial-time computation relative to a collection-description language. -/
def CollectionDenotationAttractorComputationSchema (dynamics : ReplicatorModel)
    (language : AttractorCollectionLanguage) : Prop :=
  WordRAM.Search.PolynomiallySolvable ValidGameInput
    (AttractorCollectionSolution dynamics language)

/-- The all-start and basin-promised prediction questions. -/
abbrev LiteralLimitPredictionRationalWordRAMQuestion := LimitPredictionRationalWordRAMQuestion

/-- The all-start rational question under the explicitly chosen polynomial distance-name
convention. -/
def DistanceNameLimitPredictionRationalWordRAMQuestion (dynamics : ReplicatorModel)
    (language : AttractorSetLanguage) : Prop :=
  language.HasPolynomialDistanceInterpreter ∧
    LimitPredictionRationalWordRAMQuestion dynamics language

/-- A represented prediction either names an approached minimal attractor or supplies a
certificate accepted by the fixed negative checker. -/
def CertifiedLimitPredictionSolution (dynamics : ReplicatorModel)
    (language : AttractorSetLanguage) (verifier : NegativePredictionVerifier)
    (input output : Code) : Prop :=
  ∃ I : RationalStart, I.code = input ∧
    ∃ answer, CertifiedLimitPredictionOutput.decode output = some answer ∧
      match answer with
      | .attractor description =>
          ∃ A, language.denotes I.game.shape description = some A ∧
            (dynamics I.game).IsLimitAttractor I.profile.toReal A
      | .noApproachedAttractor certificate => verifier.Accepts input certificate

/-- Explicit total alternative with effective positive descriptions and sound, complete
negative certificates. -/
def CertifiedTotalPredictionRationalWordRAMQuestion (dynamics : ReplicatorModel)
    (language : AttractorSetLanguage) (verifier : NegativePredictionVerifier) : Prop :=
  language.HasPolynomialDistanceInterpreter ∧ verifier.Sound dynamics ∧
    verifier.Complete dynamics ∧
      WordRAM.Search.PolynomiallySolvable ValidStartInput
        (CertifiedLimitPredictionSolution dynamics language verifier)

/-- Explicit stronger distance-name variant. -/
abbrev DistanceNameAttractorComputationQuestion := EffectiveAttractorComputationQuestion

end EconCSLib.OpenProblem.New.EconCSBench.MeaningOfAGame

end
