/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.OpenProblem.New.InformationalSubstitutesComplements.Problem

/-!
# InformationalSubstitutesComplements: supporting material

Auxiliary definitions and lemmas for the problem statement.
-/

section

/-!
## Correctness contracts for proposed characterizations

These predicates check a supplied concrete criterion. They do not use the tautological
existence claim that some arbitrary predicate equals the target. Structural,
geometric, sufficient/necessary and special-case directions remain independent, with
scope fixed before the criterion.
-/

namespace EconCSLib.OpenProblem.New.EconCSBench.InformationalSubstitutesComplements

open scoped BigOperators
open MeasureTheory ProbabilityTheory

/-- A supporting vector on the face containing q's support, without requiring a finite
global gradient at the boundary. -/
def IsSubgradientOnFace {State : Type*} [Fintype State]
    (G : SimplexExpectedScore State)
    (q : {p : State → ℝ // IsProbabilityVector p}) (g : State → ℝ) : Prop :=
  ∀ p : {p : State → ℝ // IsProbabilityVector p},
    (∀ e, q.1 e = 0 → p.1 e = 0) →
      G q + (∑ e, g e * (p.1 e - q.1 e)) ≤ G p

/-- Pointwise Bregman divergence for a supporting vector on the relevant face. The basic
expected-divergence identity is already in Chen--Waggoner Section 2.4; that identity
alone is not a new operational characterization. -/
def bregmanDivergenceOnFace {State : Type*} [Fintype State]
    (G : SimplexExpectedScore State)
    (p q : {p : State → ℝ // IsProbabilityVector p}) (g : State → ℝ)
    (_support : ∀ e, q.1 e = 0 → p.1 e = 0)
    (_supporting : IsSubgradientOnFace G q g) : ℝ :=
  G p - G q - ∑ e, g e * (p.1 e - q.1 e)

/-- Expected logarithmic score, with `0 * log 0 = 0` at the boundary. -/
noncomputable def logExpectedScore
    {State : Type*} [Fintype State] (p : State → ℝ) : ℝ :=
  ∑ e, p e * Real.log (p e)

/-- Expected optimal quadratic (Brier) score, up to an irrelevant affine normalization. -/
noncomputable def quadraticExpectedScore
    {State : Type*} [Fintype State] (p : State → ℝ) : ℝ :=
  ∑ e, (p e) ^ 2

/-- One joint assignment to the state and all signal variables. -/
abbrev InformationOutcome
    (State : Type*) {SignalIndex : Type*} (Signal : SignalIndex → Type*) :=
  State × SignalProfile SignalIndex Signal

/-- Agreement of two joint assignments at one information-graph node. -/
def SameAtInformationNode
    {State SignalIndex : Type*} {Signal : SignalIndex → Type*}
    (node : Option SignalIndex)
    (x y : InformationOutcome State Signal) : Prop :=
  match node with
  | none => x.1 = y.1
  | some i => x.2 i = y.2 i

/-- Agreement on all nodes in a finite parent set. -/
def SameOnInformationNodes
    {State SignalIndex : Type*} {Signal : SignalIndex → Type*}
    (nodes : Finset (Option SignalIndex))
    (x y : InformationOutcome State Signal) : Prop :=
  ∀ node, node ∈ nodes → SameAtInformationNode node x y

/-- A finite Bayesian-network factorization of the joint information source. Each local
conditional mass may depend only on the node's realized value and the realized values
of its listed parents, the parent relation is acyclic, and the product of the local
conditional masses equals the given joint prior. -/
structure BayesianNetworkRepresentation
    {State SignalIndex : Type*} {Signal : SignalIndex → Type*}
    [Fintype State] [Fintype SignalIndex] [DecidableEq SignalIndex]
    [∀ i, Fintype (Signal i)] [∀ i, DecidableEq (Signal i)]
    (source : FiniteBayesianInformation State SignalIndex Signal) where
  parents : Option SignalIndex → Finset (Option SignalIndex)
  localProbability :
    Option SignalIndex → InformationOutcome State Signal → ℝ
  nonnegative :
    ∀ node (outcome : InformationOutcome State Signal),
      0 ≤ localProbability node outcome
  normalized :
    ∀ node (outcome : InformationOutcome State Signal),
      match node with
      | none =>
          ∑ e : State, localProbability none (e, outcome.2) = 1
      | some i =>
          ∑ value : Signal i,
            localProbability (some i)
              (outcome.1, Function.update outcome.2 i value) = 1
  depends_only_on_node_and_parents :
    ∀ node (x y : InformationOutcome State Signal),
      SameAtInformationNode node x y →
        SameOnInformationNodes (parents node) x y →
        localProbability node x = localProbability node y
  acyclic :
    ∃ rank : Option SignalIndex → ℕ,
      ∀ node parent, parent ∈ parents node → rank parent < rank node
  factorizes :
    ∀ e input,
      source.jointPrior.val (e, input) =
        ∏ node : Option SignalIndex,
          localProbability node (e, input)

/-- A sufficient-condition contract; usefulness and a sharp converse require additional
concrete mathematical content. -/
def SufficientConditionQuestion (scope : SourceScope)
    (property : InformationalProperty) (criterion : StructuralCriterion) : Prop :=
  ∀ (State SignalIndex : Type) (Signal : SignalIndex → Type)
      [Fintype State] [Nonempty State]
      [Fintype SignalIndex] [DecidableEq SignalIndex]
      [∀ i, Fintype (Signal i)] [∀ i, Nonempty (Signal i)]
      [∀ i, DecidableEq (Signal i)]
      (source : FiniteBayesianInformation State SignalIndex Signal),
    scope State SignalIndex Signal source →
      criterion State SignalIndex Signal source.jointPrior
        (fun p => source.score p.1) → HasInformationalProperty source property

/-- A necessary-condition contract to accompany a proposed sufficient condition. -/
def NecessaryConditionQuestion (scope : SourceScope)
    (property : InformationalProperty) (criterion : StructuralCriterion) : Prop :=
  ∀ (State SignalIndex : Type) (Signal : SignalIndex → Type)
      [Fintype State] [Nonempty State]
      [Fintype SignalIndex] [DecidableEq SignalIndex]
      [∀ i, Fintype (Signal i)] [∀ i, Nonempty (Signal i)]
      [∀ i, DecidableEq (Signal i)]
      (source : FiniteBayesianInformation State SignalIndex Signal),
    scope State SignalIndex Signal source → HasInformationalProperty source property →
      criterion State SignalIndex Signal source.jointPrior (fun p => source.score p.1)

/-- Example special-case domains, still allowing every valid prior. -/
def binaryStateTwoSignals : SourceScope := fun State SignalIndex _ => fun _ =>
  Fintype.card State = 2 ∧ Fintype.card SignalIndex = 2

def binaryStateBinarySignals : SourceScope := fun State _ Signal => fun _ =>
  Fintype.card State = 2 ∧ ∀ i, Fintype.card (Signal i) = 2

def logarithmicScoreSources : SourceScope := fun _ _ _ => fun source =>
  ScoresAgreeOnSimplex source.score logExpectedScore

def quadraticScoreSources : SourceScope := fun _ _ _ => fun source =>
  ScoresAgreeOnSimplex source.score quadraticExpectedScore

/-- The graph is fixed before the source. Existence of an unrestricted DAG would be
vacuous as a special-case restriction. -/
def HasGraphicalFactorization
    {State SignalIndex : Type*} {Signal : SignalIndex → Type*}
    [Fintype State] [Fintype SignalIndex] [DecidableEq SignalIndex]
    [∀ i, Fintype (Signal i)] [∀ i, DecidableEq (Signal i)]
    (parents : Option SignalIndex → Finset (Option SignalIndex))
    (source : FiniteBayesianInformation State SignalIndex Signal) : Prop :=
  ∃ net : BayesianNetworkRepresentation source, net.parents = parents

end EconCSLib.OpenProblem.New.EconCSBench.InformationalSubstitutesComplements

end


section

/-!
## Every finite-valued convex score is bounded on the finite simplex

No continuity or boundary subgradient is assumed. Jensen bounds the score above by its
vertex values. Reflecting about the uniform posterior bounds it below.
-/
namespace EconCSLib.OpenProblem.New.EconCSBench.InformationalSubstitutesComplements
open scoped BigOperators
noncomputable section

/-- The source's two-point convexity is Mathlib convexity on the simplex. -/
theorem FiniteBayesianInformation.convexOn_score
    {State Index : Type*} {Signal : Index → Type*}
    [Fintype State] [Fintype Index] [DecidableEq Index]
    [∀ i, Fintype (Signal i)] [∀ i, DecidableEq (Signal i)]
    (source : FiniteBayesianInformation State Index Signal) :
    ConvexOn ℝ (stdSimplex ℝ State) source.score := by
  refine ⟨convex_stdSimplex ℝ State, ?_⟩
  intro p hp q hq a b ha hb hab
  have hb' : b = 1 - a := by linarith
  subst b
  exact source.score_convex p q hp hq a ha (by linarith)

/-- Finite convex scores admit global real lower and upper bounds on the simplex. -/
theorem convexScore_bounded {State : Type*} [Fintype State] [Nonempty State]
    (G : (State → ℝ) → ℝ) (convex : ConvexOn ℝ (stdSimplex ℝ State) G) :
    ∃ lower upper : ℝ, ∀ p, IsProbabilityVector p → lower ≤ G p ∧ G p ≤ upper := by
  classical
  let vertex : State → State → ℝ := fun e => Pi.single e 1
  let upper : ℝ := ∑ e, |G (vertex e)|
  have vertex_le (e : State) : G (vertex e) ≤ upper :=
    (le_abs_self _).trans
      (Finset.single_le_sum (f := fun e => |G (vertex e)|)
        (fun _ _ => abs_nonneg _) (Finset.mem_univ e))
  have upper_bound (p : State → ℝ) (hp : IsProbabilityVector p) : G p ≤ upper := by
    have barycenter : (∑ e, p e • vertex e) = p := by
      funext e
      simp [vertex, Finset.sum_apply, Pi.smul_apply, Pi.single_apply, mul_ite]
    have jensen := convex.map_sum_le (t := Finset.univ) (w := p) (p := vertex)
      (fun e _ => hp.1 e) hp.2 (fun e _ => single_mem_stdSimplex ℝ e)
    rw [barycenter] at jensen
    calc
      G p ≤ ∑ e, p e * G (vertex e) := jensen
      _ ≤ ∑ e, p e * upper := Finset.sum_le_sum fun e _ =>
        mul_le_mul_of_nonneg_left (vertex_le e) (hp.1 e)
      _ = upper := by rw [← Finset.sum_mul, hp.2, one_mul]
  let n : ℝ := Fintype.card State
  have hn : 1 ≤ n := by
    have hcard : 1 ≤ Fintype.card State := Fintype.card_pos
    change (1 : ℝ) ≤ (Fintype.card State : ℝ)
    exact_mod_cast hcard
  have hn0 : 0 < n := lt_of_lt_of_le zero_lt_one hn
  have hd : 0 < 2 * n - 1 := by linarith
  have hd2 : 0 < 2 * n := by positivity
  let uniform : State → ℝ := fun _ => 1 / n
  refine ⟨2 * n * G uniform - (2 * n - 1) * upper, upper, fun p hp => ⟨?_, upper_bound p hp⟩⟩
  let reflected : State → ℝ := fun e => (2 - p e) / (2 * n - 1)
  have reflected_probability : IsProbabilityVector reflected := by
    refine ⟨fun e => div_nonneg ?_ hd.le, ?_⟩
    · have pe_le : p e ≤ 1 := (mem_Icc_of_mem_stdSimplex hp e).2
      linarith
    · change (∑ e, (2 - p e) / (2 * n - 1)) = 1
      rw [← Finset.sum_div, Finset.sum_sub_distrib, hp.2]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      change (n * 2 - 1) / (2 * n - 1) = 1
      rw [mul_comm n 2, div_self hd.ne']
  have alpha_nonneg : 0 ≤ 1 / (2 * n) := by positivity
  have beta_nonneg : 0 ≤ 1 - 1 / (2 * n) := by
    have : 1 / (2 * n) ≤ 1 := (div_le_one hd2).mpr (by linarith)
    linarith
  have reconstruct :
      (1 / (2 * n)) • p + (1 - 1 / (2 * n)) • reflected = uniform := by
    funext e
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, reflected, uniform]
    field_simp
    ring
  have hc := convex.2 hp reflected_probability alpha_nonneg beta_nonneg
    (show 1 / (2 * n) + (1 - 1 / (2 * n)) = 1 by ring)
  rw [reconstruct] at hc
  have comparison : G uniform ≤ G p / (2 * n) + (1 - 1 / (2 * n)) * upper := by
    calc
      G uniform ≤ (1 / (2 * n)) * G p + (1 - 1 / (2 * n)) * G reflected := hc
      _ ≤ (1 / (2 * n)) * G p + (1 - 1 / (2 * n)) * upper :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left
          (upper_bound reflected reflected_probability) beta_nonneg)
      _ = _ := by ring
  have fraction : G p / (2 * n) + (1 - 1 / (2 * n)) * upper =
      (G p + (2 * n - 1) * upper) / (2 * n) := by
    field_simp
  rw [fraction] at comparison
  have cleared := (le_div_iff₀ hd2).mp comparison
  linarith

end
end EconCSLib.OpenProblem.New.EconCSBench.InformationalSubstitutesComplements

end


section

/-!
## Measurability of finite-valued convex scores on the simplex

Convex scores need not be continuous at the simplex boundary. The proof works on each
positive support face and then uses the finite face partition.
-/
namespace EconCSLib.OpenProblem.New.EconCSBench.InformationalSubstitutesComplements
open scoped BigOperators
open Set
noncomputable section

private def simplexProjection {E : Type*} [Fintype E] (x : E → ℝ) : E → ℝ :=
  fun i => x i + (1 - ∑ j, x j) / Fintype.card E

private theorem simplexProjection_eq {E : Type*} [Fintype E]
    (x : E → ℝ) (normalized : ∑ i, x i = 1) : simplexProjection x = x := by
  funext i
  simp [simplexProjection, normalized]

private theorem simplexProjection_sum {E : Type*} [Fintype E] [Nonempty E]
    (x : E → ℝ) : ∑ i, simplexProjection x i = 1 := by
  have nonzero : (Fintype.card E : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [simplexProjection, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]
  field_simp
  ring

private theorem simplexProjection_combo {E : Type*} [Fintype E]
    (x y : E → ℝ) (a b : ℝ) (weights : a + b = 1) :
    simplexProjection (a • x + b • y) = a • simplexProjection x + b • simplexProjection y := by
  funext i
  simp only [simplexProjection, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Finset.sum_add_distrib, ← Finset.mul_sum]
  have hb : b = 1 - a := by linarith
  subst b
  ring

/-- Convexity gives continuity on the strictly positive part of the simplex, without
imposing any regularity at its boundary. -/
theorem convexScore_continuousOn_positive {E : Type*} [Fintype E] [Nonempty E]
    (G : (E → ℝ) → ℝ) (convex : ConvexOn ℝ (stdSimplex ℝ E) G) :
    ContinuousOn G {p | IsProbabilityVector p ∧ ∀ e, 0 < p e} := by
  let C : Set (E → ℝ) := {x | ∀ i, 0 < simplexProjection x i}
  have projection_continuous : Continuous (simplexProjection (E := E)) := by
    unfold simplexProjection
    fun_prop
  have C_open : IsOpen C := by
    simpa only [C, setOf_forall] using isOpen_iInter_of_finite
      (fun i : E => isOpen_lt continuous_const ((continuous_apply i).comp projection_continuous))
  have C_convex : Convex ℝ C := by
    intro x hx y hy a b ha hb hab i
    rw [simplexProjection_combo x y a b hab]
    change 0 < a * simplexProjection x i + b * simplexProjection y i
    rcases eq_or_lt_of_le ha with ha0 | ha0
    · have hb1 : b = 1 := by linarith
      simpa [← ha0, hb1] using hy i
    · exact add_pos_of_pos_of_nonneg (mul_pos ha0 (hx i)) (mul_nonneg hb (hy i).le)
  have projection_probability (x : E → ℝ) (hx : x ∈ C) :
      simplexProjection x ∈ stdSimplex ℝ E :=
    ⟨fun i => (hx i).le, simplexProjection_sum x⟩
  have composite_convex : ConvexOn ℝ C (fun x => G (simplexProjection x)) := by
    refine ⟨C_convex, ?_⟩
    intro x hx y hy a b ha hb hab
    dsimp only
    rw [simplexProjection_combo x y a b hab]
    exact convex.2 (projection_probability x hx) (projection_probability y hy) ha hb hab
  have continuous : ContinuousOn (fun x => G (simplexProjection x)) C :=
    composite_convex.continuousOn C_open
  apply continuous.congr_mono
  · intro p hp
    dsimp only
    rw [simplexProjection_eq p hp.1.2]
  · intro p hp
    change ∀ i, 0 < simplexProjection p i
    rw [simplexProjection_eq p hp.1.2]
    exact hp.2

private def faceEmbed {E : Type*} [Fintype E] (s : Finset E) :
    (s → ℝ) →ₗ[ℝ] (E → ℝ) := FunOnFinite.linearMap ℝ ℝ (Subtype.val : s → E)

private theorem faceEmbed_sum {E : Type*} [Fintype E]
    (s : Finset E) (x : s → ℝ) : ∑ e, faceEmbed s x e = ∑ i, x i := by
  classical
  simp only [faceEmbed, FunOnFinite.linearMap_apply_apply]
  exact Finset.sum_fiberwise Finset.univ Subtype.val x

private theorem faceEmbed_at {E : Type*} [Fintype E]
    (s : Finset E) (x : s → ℝ) (i : s) : faceEmbed s x i.val = x i := by
  classical
  simp [faceEmbed, FunOnFinite.linearMap_apply_apply, Subtype.val_injective.eq_iff,
    Finset.sum_filter]

private theorem faceEmbed_outside {E : Type*} [Fintype E]
    (s : Finset E) (x : s → ℝ) (e : E) (outside : e ∉ s) : faceEmbed s x e = 0 := by
  classical
  have different (i : s) : i.val ≠ e := by
    intro eq
    exact outside (eq ▸ i.property)
  simp [faceEmbed, FunOnFinite.linearMap_apply_apply, different]

private def supportFace {E : Type*} [Fintype E] (s : Finset E) : Set (E → ℝ) :=
  {p | IsProbabilityVector p ∧ ∀ e, e ∈ s ↔ 0 < p e}

private theorem faceEmbed_restrict {E : Type*} [Fintype E]
    (s : Finset E) (p : E → ℝ) (hp : p ∈ supportFace s) :
    faceEmbed s (fun i : s => p i.val) = p := by
  classical
  funext e
  by_cases inside : e ∈ s
  · exact faceEmbed_at s _ ⟨e, inside⟩
  · rw [faceEmbed_outside s _ e inside]
    have nonpositive : ¬ 0 < p e := fun positive => inside ((hp.2 e).mpr positive)
    exact (le_antisymm (le_of_not_gt nonpositive) (hp.1.1 e)).symm

private theorem supportFace_restrict {E : Type*} [Fintype E]
    (s : Finset E) (p : E → ℝ) (hp : p ∈ supportFace s) :
    IsProbabilityVector (fun i : s => p i.val) ∧ ∀ i : s, 0 < p i.val := by
  refine ⟨⟨fun i => hp.1.1 i.val, ?_⟩, fun i => (hp.2 i.val).mp i.property⟩
  rw [← faceEmbed_sum s (fun i : s => p i.val), faceEmbed_restrict s p hp]
  exact hp.1.2

/-- On each exact support face a finite convex score is continuous. -/
theorem convexScore_continuousOn_supportFace {E : Type*} [Fintype E]
    (G : (E → ℝ) → ℝ) (convex : ConvexOn ℝ (stdSimplex ℝ E) G) (s : Finset E) :
    ContinuousOn G {p | IsProbabilityVector p ∧ ∀ e, e ∈ s ↔ 0 < p e} := by
  classical
  change ContinuousOn G (supportFace s)
  by_cases nonempty : s.Nonempty
  · letI : Nonempty s := nonempty.to_subtype
    have face_convex : ConvexOn ℝ (stdSimplex ℝ s) (fun x => G (faceEmbed s x)) := by
      apply (convex.comp_linearMap (faceEmbed s)).subset
      · intro x hx
        exact stdSimplex.image_linearMap (Subtype.val : s → E) ⟨x, hx, rfl⟩
      · exact convex_stdSimplex ℝ s
    have continuous := convexScore_continuousOn_positive _ face_convex
    have restriction_continuous : Continuous (fun p : E → ℝ => fun i : s => p i.val) := by
      fun_prop
    have on_face := continuous.comp restriction_continuous.continuousOn
      (fun p hp => supportFace_restrict s p hp)
    apply on_face.congr
    intro p hp
    exact congrArg G (faceEmbed_restrict s p hp).symm
  · have empty : supportFace s = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro p hp
      have zero (e : E) : p e = 0 := by
        have no_positive : ¬ 0 < p e := fun positive =>
          nonempty ⟨e, (hp.2 e).mpr positive⟩
        exact le_antisymm (le_of_not_gt no_positive) (hp.1.1 e)
      have sum_zero : ∑ e, p e = 0 := by simp [zero]
      linarith [hp.1.2]
    rw [empty]
    exact continuousOn_empty G

private theorem supportFace_measurableSet {E : Type*} [Fintype E]
    (s : Finset E) : MeasurableSet (supportFace s) := by
  classical
  have simplex_measurable : MeasurableSet {p : E → ℝ | IsProbabilityVector p} :=
    (isClosed_stdSimplex ℝ E).measurableSet
  apply simplex_measurable.inter
  have each (e : E) : MeasurableSet {p : E → ℝ | e ∈ s ↔ 0 < p e} := by
    by_cases inside : e ∈ s
    · simp only [inside, true_iff]
      exact (isOpen_lt continuous_const (continuous_apply e)).measurableSet
    · simp only [inside, false_iff, not_lt]
      exact (isClosed_le (continuous_apply e) continuous_const).measurableSet
  convert MeasurableSet.iInter each using 1
  ext p
  simp
  rfl

/-- A finite convex score, set to zero off the simplex, is Borel measurable. Arbitrary
off-simplex values of the original total function are not constrained. -/
theorem convexScore_measurable_on_simplex {E : Type*} [Fintype E]
    (G : (E → ℝ) → ℝ) (convex : ConvexOn ℝ (stdSimplex ℝ E) G) :
    Measurable ((stdSimplex ℝ E).indicator G) := by
  classical
  let piece (s : Finset E) : (E → ℝ) → ℝ := (supportFace s).piecewise G (fun _ => 0)
  have piece_measurable (s : Finset E) : Measurable (piece s) := by
    dsimp only [piece]
    convert (convexScore_continuousOn_supportFace G convex s).measurable_piecewise
      (g := fun _ => (0 : ℝ)) continuous_const.continuousOn (supportFace_measurableSet s)
      using 1
    funext p
    simp [Set.piecewise, supportFace]
  have decomposition (p : E → ℝ) :
      (∑ s : Finset E, piece s p) = (stdSimplex ℝ E).indicator G p := by
    change (∑ s : Finset E, piece s p) = if IsProbabilityVector p then G p else 0
    by_cases probability : IsProbabilityVector p
    · rw [if_pos probability]
      let support : Finset E := Finset.univ.filter (fun e => 0 < p e)
      have belongs : p ∈ supportFace support := ⟨probability, fun e => by simp [support]⟩
      have unique (s : Finset E) (inside : p ∈ supportFace s) : s = support := by
        ext e
        simpa only [support, Finset.mem_filter, Finset.mem_univ, true_and] using inside.2 e
      rw [Finset.sum_eq_single support]
      · exact Set.piecewise_eq_of_mem (supportFace support) G (fun _ => 0) belongs
      · intro other _ different
        exact Set.piecewise_eq_of_notMem (supportFace other) G (fun _ => 0)
          (fun inside => different (unique other inside))
      · intro not_in
        exact False.elim (not_in (Finset.mem_univ support))
    · rw [if_neg probability]
      apply Finset.sum_eq_zero
      intro s _
      exact Set.piecewise_eq_of_notMem (supportFace s) G (fun _ => 0)
        (fun inside => probability inside.1)
  have sum_measurable := Finset.measurable_fun_sum Finset.univ
    (fun s (_ : s ∈ (Finset.univ : Finset (Finset E))) => piece_measurable s)
  simpa only [decomposition] using sum_measurable

end
end EconCSLib.OpenProblem.New.EconCSBench.InformationalSubstitutesComplements

end


section

/-!
## Finite report labels have no informational content

Renaming a finite report alphabet preserves every posterior and both value
expressions. The construction reuses Mathlib's pushforward on `stdSimplex`.
-/
namespace EconCSLib.OpenProblem.New.EconCSBench.InformationalSubstitutesComplements

open scoped BigOperators
noncomputable section
universe u v w

variable {Index : Type u} {Signal : Index → Type v}
  [Fintype Index] [DecidableEq Index]
  [∀ i, Fintype (Signal i)] [∀ i, DecidableEq (Signal i)]

/-- Relabel a finite disclosure using the native simplex pushforward. -/
def SignalDisclosure.relabel (d : SignalDisclosure Index Signal)
    {Y : Type (max u v)} [Fintype Y] [DecidableEq Y] (labels : d.Output ≃ Y) :
    SignalDisclosure Index Signal where
  Output := Y
  kernel := fun input => stdSimplex.map labels (d.kernel input)

/-- The renamed report has exactly the original conditional probability. -/
theorem SignalDisclosure.relabel_kernel (d : SignalDisclosure Index Signal)
    {Y : Type (max u v)} [Fintype Y] [DecidableEq Y] (labels : d.Output ≃ Y)
    (input : SignalProfile Index Signal) (output : d.Output) :
    ((d.relabel labels).kernel input).val (labels output) = (d.kernel input).val output := by
  classical
  change FunOnFinite.linearMap ℝ ℝ labels (d.kernel input).val (labels output) = _
  simp [FunOnFinite.linearMap_apply_apply, labels.injective.eq_iff, Finset.sum_filter]

variable {State : Type w} [Fintype State]
  (source : FiniteBayesianInformation State Index Signal)

/-- State/report probabilities are invariant under renaming. -/
theorem disclosureJointMass_relabel (d : SignalDisclosure Index Signal)
    {Y : Type (max u v)} [Fintype Y] [DecidableEq Y] (labels : d.Output ≃ Y)
    (e : State) (output : d.Output) :
    disclosureJointMass source (d.relabel labels) e (labels output) =
      disclosureJointMass source d e output := by
  simp only [disclosureJointMass, SignalDisclosure.relabel_kernel]

/-- Report probabilities are invariant under renaming. -/
theorem disclosureProbability_relabel (d : SignalDisclosure Index Signal)
    {Y : Type (max u v)} [Fintype Y] [DecidableEq Y] (labels : d.Output ≃ Y)
    (output : d.Output) :
    disclosureProbability source (d.relabel labels) (labels output) =
      disclosureProbability source d output := by
  simp only [disclosureProbability, disclosureJointMass_relabel]

/-- Posterior vectors are unchanged, including the chosen null-report convention. -/
theorem disclosurePosterior_relabel (d : SignalDisclosure Index Signal)
    {Y : Type (max u v)} [Fintype Y] [DecidableEq Y] (labels : d.Output ≃ Y)
    (output : d.Output) :
    disclosurePosterior source (d.relabel labels) (labels output) =
      disclosurePosterior source d output := by
  funext e
  simp only [disclosurePosterior, disclosureJointMass_relabel, disclosureProbability_relabel]

/-- Renaming finite reports preserves expected score. -/
theorem disclosureValue_relabel (d : SignalDisclosure Index Signal)
    {Y : Type (max u v)} [Fintype Y] [DecidableEq Y] (labels : d.Output ≃ Y) :
    disclosureValue source (d.relabel labels) = disclosureValue source d := by
  apply (Fintype.sum_equiv labels.symm _ _ ?_)
  intro output
  obtain ⟨old, rfl⟩ := labels.surjective output
  simp only [labels.symm_apply_apply, disclosureProbability_relabel, disclosurePosterior_relabel]

/-- Joint state/report/whole-observation probabilities are unchanged. -/
theorem disclosureWithWholeJointMass_relabel [∀ i, Nonempty (Signal i)]
    (B : Finset Index) (d : SignalDisclosure Index Signal)
    {Y : Type (max u v)} [Fintype Y] [DecidableEq Y] (labels : d.Output ≃ Y)
    (e : State) (observed : SignalProfile Index Signal) (output : d.Output) :
    disclosureWithWholeJointMass source B (d.relabel labels) e (observed, labels output) =
      disclosureWithWholeJointMass source B d e (observed, output) := by
  classical
  simp only [disclosureWithWholeJointMass, SignalDisclosure.relabel_kernel]

/-- The joint value used in each marginal comparison is likewise label-invariant. -/
theorem disclosureWithWholeValue_relabel [∀ i, Nonempty (Signal i)]
    (B : Finset Index) (d : SignalDisclosure Index Signal)
    {Y : Type (max u v)} [Fintype Y] [DecidableEq Y] (labels : d.Output ≃ Y) :
    disclosureWithWholeValue source B (d.relabel labels) =
      disclosureWithWholeValue source B d := by
  classical
  unfold disclosureWithWholeValue
  apply Fintype.sum_equiv (Equiv.prodCongr (Equiv.refl _) labels.symm) _ _
  rintro ⟨observed, output⟩
  obtain ⟨old, rfl⟩ := labels.surjective output
  change disclosureWithWholeProbability source B (d.relabel labels) (observed, labels old) *
      source.score (disclosureWithWholePosterior source B (d.relabel labels) (observed, labels old)) =
    disclosureWithWholeProbability source B d (observed, labels.symm (labels old)) *
      source.score (disclosureWithWholePosterior source B d (observed, labels.symm (labels old)))
  rw [labels.symm_apply_apply]
  unfold disclosureWithWholePosterior disclosureWithWholeProbability
  simp only [disclosureWithWholeJointMass_relabel]

end
end EconCSLib.OpenProblem.New.EconCSBench.InformationalSubstitutesComplements

end


section

/-!
## Soundness of finite counterexamples for general disclosures

Finite lotteries embed through Mathlib's probability-mass-function measure. Blackwell
post-processing and expected scores retain their actual semantics. The Radon--Nikodym
calculation ignores only zero-mass reports; no regularity assumption on the score is
needed for a finite report alphabet.
-/
namespace EconCSLib.OpenProblem.New.EconCSBench.InformationalSubstitutesComplements

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
noncomputable section

/-- Native finite PMF associated with a real lottery. -/
def lotteryPMF {X : Type*} [Fintype X] (p : Lottery ℝ X) : PMF X :=
  PMF.ofFintype (fun x => ENNReal.ofReal (p.val x)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun x _ => p.property.1 x), p.property.2]
    simp)

/-- The native measure associated with the lottery's PMF. -/
def lotteryMeasure {X : Type*} [Fintype X] [MeasurableSpace X]
    (p : Lottery ℝ X) : Measure X := (lotteryPMF p).toMeasure

instance lotteryMeasure_isProbability {X : Type*} [Fintype X] [MeasurableSpace X]
    (p : Lottery ℝ X) : IsProbabilityMeasure (lotteryMeasure p) := by
  unfold lotteryMeasure
  infer_instance

/-- Each point has exactly the encoded probability mass. -/
theorem lotteryMeasure_singleton {X : Type*} [Fintype X] [MeasurableSpace X]
    [MeasurableSingletonClass X] (p : Lottery ℝ X) (x : X) :
    lotteryMeasure p {x} = ENNReal.ofReal (p.val x) := by
  exact PMF.toMeasure_apply_singleton (lotteryPMF p) x (measurableSet_singleton x)

instance SignalDisclosure.discreteMeasurableSpace
    {SignalIndex : Type*} {Signal : SignalIndex → Type*}
    [Fintype SignalIndex] [DecidableEq SignalIndex]
    [∀ i, Fintype (Signal i)] [∀ i, DecidableEq (Signal i)]
    (d : SignalDisclosure SignalIndex Signal) : MeasurableSpace d.Output := ⊤

instance SignalDisclosure.discreteMeasurableSingleton
    {SignalIndex : Type*} {Signal : SignalIndex → Type*}
    [Fintype SignalIndex] [DecidableEq SignalIndex]
    [∀ i, Fintype (Signal i)] [∀ i, DecidableEq (Signal i)]
    (d : SignalDisclosure SignalIndex Signal) : MeasurableSingletonClass d.Output := by
  change @MeasurableSingletonClass d.Output ⊤
  infer_instance

/-- A finite disclosure is a general disclosure on the discrete measurable space. -/
abbrev SignalDisclosure.toGeneral
    {SignalIndex : Type*} {Signal : SignalIndex → Type*}
    [Fintype SignalIndex] [DecidableEq SignalIndex]
    [∀ i, Fintype (Signal i)] [∀ i, DecidableEq (Signal i)]
    (d : SignalDisclosure SignalIndex Signal) : GeneralSignalDisclosure SignalIndex Signal :=
  { Output := d.Output
    kernel := fun input => lotteryMeasure (d.kernel input)
    kernel_isProbability := fun _ => inferInstance }

/-- On a nonnull singleton, the RN posterior is the familiar mass ratio. -/
theorem finite_rnDeriv_toReal {X : Type*} [MeasurableSpace X]
    [MeasurableSingletonClass X] (μ ν : Measure X)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμν : μ ≪ ν)
    (x : X) (hx : ν {x} ≠ 0) :
    (μ.rnDeriv ν x).toReal = (μ {x}).toReal / (ν {x}).toReal := by
  have h := Measure.setLIntegral_rnDeriv hμν {x}
  rw [lintegral_singleton] at h
  have hr := congrArg ENNReal.toReal h
  rw [ENNReal.toReal_mul] at hr
  exact (eq_div_iff (ENNReal.toReal_ne_zero.mpr ⟨hx, measure_ne_top ν {x}⟩)).mpr hr

/-- Any score on a finite posterior alphabet integrates to its finite weighted sum. -/
theorem finite_posterior_integral {State X : Type*} [Fintype State] [Fintype X]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    (μ : State → Measure X) [∀ e, IsFiniteMeasure (μ e)]
    (score : (State → ℝ) → ℝ) :
    (∫ x, score (fun e => ((μ e).rnDeriv (∑ e, μ e) x).toReal) ∂(∑ e, μ e)) =
      ∑ x, ((∑ e, μ e) {x}).toReal *
        score (fun e => ((μ e) {x}).toReal / ((∑ e, μ e) {x}).toReal) := by
  classical
  rw [integral_fintype Integrable.of_finite]
  apply Finset.sum_congr rfl
  intro x _
  change ((∑ e, μ e) {x}).toReal * _ = _
  by_cases hx : (∑ e, μ e) {x} = 0
  · simp [hx]
  · congr 2
    funext e
    apply finite_rnDeriv_toReal _ _ _ x hx
    apply Measure.absolutelyContinuous_of_le
    exact Finset.single_le_sum (fun _ _ => bot_le) (Finset.mem_univ e)

/-- A pure lottery gives the corresponding Dirac law. -/
theorem lotteryMeasure_pure {X : Type*} [Fintype X] [DecidableEq X]
    [MeasurableSpace X] [MeasurableSingletonClass X] (x : X) :
    lotteryMeasure (Lottery.pure (𝕜 := ℝ) x) = Measure.dirac x := by
  apply Measure.ext_of_singleton
  intro y
  rw [lotteryMeasure_singleton]
  by_cases h : x = y
  · subst y
    simp [Lottery.pure, stdSimplex.pure_apply]
  · simp [Lottery.pure, stdSimplex.pure_apply, h, Ne.symm h]

section Information
variable {State SignalIndex : Type*} {Signal : SignalIndex → Type*}
  [Fintype State] [Fintype SignalIndex] [DecidableEq SignalIndex]
  [∀ i, Fintype (Signal i)] [∀ i, DecidableEq (Signal i)]

/-- The whole-signal embedding agrees with the original general Dirac disclosure. -/
theorem wholeSignalDisclosure_toGeneral [∀ i, Nonempty (Signal i)]
    (S : Finset SignalIndex) :
    (wholeSignalDisclosure (Signal := Signal) S).toGeneral =
      generalWholeSignalDisclosure S := by
  classical
  letI : MeasurableSpace (SignalProfile SignalIndex Signal) := ⊤
  unfold wholeSignalDisclosure SignalDisclosure.toGeneral generalWholeSignalDisclosure
  congr 1
  funext input
  exact lotteryMeasure_pure _

/-- Finite stochastic post-processing is a genuine Markov post-processing. -/
theorem IsBlackwellBelowOn.toGeneral
    {source : FiniteBayesianInformation State SignalIndex Signal}
    {less more : SignalDisclosure SignalIndex Signal}
    (h : IsBlackwellBelowOn source less more) :
    IsGeneralBlackwellBelowOn source less.toGeneral more.toGeneral := by
  classical
  letI : MeasurableSpace less.Output := ⊤
  letI : MeasurableSpace more.Output := ⊤
  obtain ⟨garbling, hgarbling⟩ := h
  let K : Kernel more.Output less.Output :=
    Kernel.ofFunOfCountable (fun middle => lotteryMeasure (garbling middle))
  refine ⟨K, ⟨fun _ => inferInstanceAs (IsProbabilityMeasure (lotteryMeasure _))⟩, ?_⟩
  intro input hinput
  apply Measure.ext_of_singleton
  intro output
  change lotteryMeasure (less.kernel input) {output} =
    (K ∘ₘ lotteryMeasure (more.kernel input)) {output}
  rw [lotteryMeasure_singleton, Measure.bind_apply (measurableSet_singleton output) K.aemeasurable,
    lintegral_fintype]
  simp only [K, Kernel.ofFunOfCountable, lotteryMeasure_singleton]
  rw [hgarbling input hinput output, ENNReal.ofReal_sum_of_nonneg
    (fun middle _ => mul_nonneg ((more.kernel input).property.1 middle)
      ((garbling middle).property.1 output))]
  apply Finset.sum_congr rfl
  intro middle _
  change ENNReal.ofReal ((more.kernel input).val middle * (garbling middle).val output) =
    lotteryMeasure (garbling middle) {output} * ENNReal.ofReal ((more.kernel input).val middle)
  rw [lotteryMeasure_singleton, ENNReal.ofReal_mul ((more.kernel input).property.1 middle), mul_comm]

/-- Each state-output law is finite, even for a continuous report alphabet. -/
instance generalDisclosureStateMeasure_isFinite
    (source : FiniteBayesianInformation State SignalIndex Signal)
    (d : GeneralSignalDisclosure SignalIndex Signal) (e : State) :
    IsFiniteMeasure (generalDisclosureStateMeasure source d e) := by
  letI : ∀ input, IsProbabilityMeasure (d.kernel input) := d.kernel_isProbability
  constructor
  simp [generalDisclosureStateMeasure, Measure.finsetSum_apply, Measure.smul_apply,
    ENNReal.sum_lt_top]

/-- The marginal output law is finite. -/
instance generalDisclosureMeasure_isFinite
    (source : FiniteBayesianInformation State SignalIndex Signal)
    (d : GeneralSignalDisclosure SignalIndex Signal) :
    IsFiniteMeasure (generalDisclosureMeasure source d) := by
  unfold generalDisclosureMeasure
  infer_instance

/-- Fixing a whole-signal observation leaves a finite state-output law. -/
instance generalDisclosureWithWholeStateMeasure_isFinite [∀ i, Nonempty (Signal i)]
    (source : FiniteBayesianInformation State SignalIndex Signal) (B : Finset SignalIndex)
    (d : GeneralSignalDisclosure SignalIndex Signal) (observed : SignalProfile SignalIndex Signal)
    (e : State) : IsFiniteMeasure (generalDisclosureWithWholeStateMeasure source B d observed e) := by
  classical
  letI : ∀ input, IsProbabilityMeasure (d.kernel input) := d.kernel_isProbability
  constructor
  simp only [generalDisclosureWithWholeStateMeasure, Measure.finsetSum_apply]
  apply ENNReal.sum_lt_top.mpr
  intro input _
  split_ifs <;> simp [Measure.smul_apply]

/-- The joint report/whole-observation law is finite. -/
instance generalDisclosureWithWholeMeasure_isFinite [∀ i, Nonempty (Signal i)]
    (source : FiniteBayesianInformation State SignalIndex Signal) (B : Finset SignalIndex)
    (d : GeneralSignalDisclosure SignalIndex Signal) (observed : SignalProfile SignalIndex Signal) :
    IsFiniteMeasure (generalDisclosureWithWholeMeasure source B d observed) := by
  unfold generalDisclosureWithWholeMeasure
  infer_instance

/-- The embedded state's singleton mass is exactly the finite joint mass. -/
theorem generalDisclosureStateMeasure_toGeneral_singleton
    (source : FiniteBayesianInformation State SignalIndex Signal)
    (d : SignalDisclosure SignalIndex Signal) (e : State) (output : d.Output) :
    generalDisclosureStateMeasure source d.toGeneral e {output} =
      ENNReal.ofReal (disclosureJointMass source d e output) := by
  classical
  letI : MeasurableSpace d.Output := ⊤
  simp only [generalDisclosureStateMeasure, SignalDisclosure.toGeneral,
    Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul, lotteryMeasure_singleton]
  rw [disclosureJointMass, ENNReal.ofReal_sum_of_nonneg
    (fun input _ => mul_nonneg (source.jointPrior.property.1 (e, input))
      ((d.kernel input).property.1 output))]
  apply Finset.sum_congr rfl
  intro input _
  exact (ENNReal.ofReal_mul (source.jointPrior.property.1 (e, input))).symm

/-- Finite joint masses are nonnegative. -/
theorem disclosureJointMass_nonnegative
    (source : FiniteBayesianInformation State SignalIndex Signal)
    (d : SignalDisclosure SignalIndex Signal) (e : State) (output : d.Output) :
    0 ≤ disclosureJointMass source d e output := by
  exact Finset.sum_nonneg fun input _ =>
    mul_nonneg (source.jointPrior.property.1 (e, input)) ((d.kernel input).property.1 output)

/-- The embedded marginal singleton mass agrees with the finite output probability. -/
theorem generalDisclosureMeasure_toGeneral_singleton
    (source : FiniteBayesianInformation State SignalIndex Signal)
    (d : SignalDisclosure SignalIndex Signal) (output : d.Output) :
    generalDisclosureMeasure source d.toGeneral {output} =
      ENNReal.ofReal (disclosureProbability source d output) := by
  classical
  rw [generalDisclosureMeasure, Measure.finsetSum_apply]
  calc
    _ = ∑ e, ENNReal.ofReal (disclosureJointMass source d e output) := by
      apply Finset.sum_congr rfl
      intro e _
      exact generalDisclosureStateMeasure_toGeneral_singleton source d e output
    _ = _ := (ENNReal.ofReal_sum_of_nonneg
      (fun e _ => disclosureJointMass_nonnegative source d e output)).symm

/-- Finite disclosure value is unchanged by embedding into the general model. -/
theorem generalDisclosureValue_toGeneral
    (source : FiniteBayesianInformation State SignalIndex Signal)
    (d : SignalDisclosure SignalIndex Signal) :
    generalDisclosureValue source d.toGeneral = disclosureValue source d := by
  classical
  letI : MeasurableSpace d.Output := ⊤
  letI : ∀ e, IsFiniteMeasure (generalDisclosureStateMeasure source d.toGeneral e) :=
    fun e => generalDisclosureStateMeasure_isFinite source d.toGeneral e
  unfold generalDisclosureValue generalDisclosurePosterior generalDisclosureMeasure
  rw [finite_posterior_integral]
  change (∑ output, (generalDisclosureMeasure source d.toGeneral {output}).toReal *
    source.score (fun e => (generalDisclosureStateMeasure source d.toGeneral e {output}).toReal /
      (generalDisclosureMeasure source d.toGeneral {output}).toReal)) = _
  simp only [generalDisclosureMeasure_toGeneral_singleton source d,
    generalDisclosureStateMeasure_toGeneral_singleton source d,
    disclosureProbability,
    ENNReal.toReal_ofReal (disclosureJointMass_nonnegative source d _ _),
    ENNReal.toReal_ofReal (Finset.sum_nonneg
      (fun e _ => disclosureJointMass_nonnegative source d e _))]
  rfl

/-- Finite joint masses remain nonnegative after fixing a whole-signal observation. -/
theorem disclosureWithWholeJointMass_nonnegative [∀ i, Nonempty (Signal i)]
    (source : FiniteBayesianInformation State SignalIndex Signal) (B : Finset SignalIndex)
    (d : SignalDisclosure SignalIndex Signal) (e : State)
    (output : SignalProfile SignalIndex Signal × d.Output) :
    0 ≤ disclosureWithWholeJointMass source B d e output := by
  classical
  apply Finset.sum_nonneg
  intro input _
  apply mul_nonneg (source.jointPrior.property.1 (e, input))
  split_ifs
  · exact (d.kernel input).property.1 output.2
  · exact le_refl 0

/-- The embedded joint singleton mass agrees with its finite counterpart. -/
theorem generalDisclosureWithWholeStateMeasure_toGeneral_singleton [∀ i, Nonempty (Signal i)]
    (source : FiniteBayesianInformation State SignalIndex Signal) (B : Finset SignalIndex)
    (d : SignalDisclosure SignalIndex Signal) (observed : SignalProfile SignalIndex Signal)
    (e : State) (output : d.Output) :
    generalDisclosureWithWholeStateMeasure source B d.toGeneral observed e {output} =
      ENNReal.ofReal (disclosureWithWholeJointMass source B d e (observed, output)) := by
  classical
  letI : MeasurableSpace d.Output := ⊤
  simp only [generalDisclosureWithWholeStateMeasure, Measure.finsetSum_apply]
  rw [disclosureWithWholeJointMass, ENNReal.ofReal_sum_of_nonneg (fun input _ =>
    mul_nonneg (source.jointPrior.property.1 (e, input))
      (by split_ifs; exact (d.kernel input).property.1 output; exact le_rfl))]
  apply Finset.sum_congr rfl
  intro input _
  by_cases h : maskedSignalProfile B input = observed
  · simp [h, Measure.smul_apply, lotteryMeasure_singleton,
      ENNReal.ofReal_mul (source.jointPrior.property.1 (e, input))]
  · simp [h]

/-- Marginal masses also agree after fixing the whole-signal observation. -/
theorem generalDisclosureWithWholeMeasure_toGeneral_singleton [∀ i, Nonempty (Signal i)]
    (source : FiniteBayesianInformation State SignalIndex Signal) (B : Finset SignalIndex)
    (d : SignalDisclosure SignalIndex Signal) (observed : SignalProfile SignalIndex Signal)
    (output : d.Output) :
    generalDisclosureWithWholeMeasure source B d.toGeneral observed {output} =
      ENNReal.ofReal (disclosureWithWholeProbability source B d (observed, output)) := by
  classical
  rw [generalDisclosureWithWholeMeasure, Measure.finsetSum_apply]
  calc
    _ = ∑ e, ENNReal.ofReal (disclosureWithWholeJointMass source B d e (observed, output)) := by
      apply Finset.sum_congr rfl
      intro e _
      exact generalDisclosureWithWholeStateMeasure_toGeneral_singleton source B d observed e output
    _ = _ := (ENNReal.ofReal_sum_of_nonneg
      (fun e _ => disclosureWithWholeJointMass_nonnegative source B d e (observed, output))).symm

/-- Jointly revealing whole signals preserves the finite value under embedding. -/
theorem generalDisclosureWithWholeValue_toGeneral [∀ i, Nonempty (Signal i)]
    (source : FiniteBayesianInformation State SignalIndex Signal) (B : Finset SignalIndex)
    (d : SignalDisclosure SignalIndex Signal) :
    generalDisclosureWithWholeValue source B d.toGeneral =
      disclosureWithWholeValue source B d := by
  classical
  letI : MeasurableSpace d.Output := ⊤
  unfold generalDisclosureWithWholeValue disclosureWithWholeValue
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro observed _
  letI : ∀ e, IsFiniteMeasure
      (generalDisclosureWithWholeStateMeasure source B d.toGeneral observed e) :=
    fun e => generalDisclosureWithWholeStateMeasure_isFinite source B d.toGeneral observed e
  unfold generalDisclosureWithWholePosterior generalDisclosureWithWholeMeasure
  rw [finite_posterior_integral]
  change (∑ output,
    (generalDisclosureWithWholeMeasure source B d.toGeneral observed {output}).toReal *
    source.score (fun e =>
      (generalDisclosureWithWholeStateMeasure source B d.toGeneral observed e {output}).toReal /
      (generalDisclosureWithWholeMeasure source B d.toGeneral observed {output}).toReal)) = _
  simp only [generalDisclosureWithWholeMeasure_toGeneral_singleton source B d observed,
    generalDisclosureWithWholeStateMeasure_toGeneral_singleton source B d observed,
    disclosureWithWholeProbability,
    ENNReal.toReal_ofReal (disclosureWithWholeJointMass_nonnegative source B d _ _),
    ENNReal.toReal_ofReal (Finset.sum_nonneg
      (fun e _ => disclosureWithWholeJointMass_nonnegative source B d e _))]
  rfl

end Information

/-- Every validated encoded negative certificate rejects the actual labeled property,
including the strong properties quantified over arbitrary report spaces. -/
theorem CertificationOutput.Valid.rejects
    {I : RationalInformationInput} {property : InformationalProperty}
    {certificate : CertificationOutput I.alphabet}
    (valid : certificate.Valid I property) (negative : certificate ≠ .accept) :
    ¬ HasInformationalProperty I.source property := by
  cases certificate with
  | accept => exact False.elim (negative rfl)
  | weakViolation smaller larger added =>
      rcases valid with ⟨kind, hinter, hsub, violation⟩
      rcases kind with rfl | rfl
      · intro holds
        exact not_lt_of_ge (holds smaller larger added hinter hsub) violation
      · intro holds
        exact not_lt_of_ge (holds smaller larger added hinter hsub) violation
  | disclosureViolation A B garbling =>
      rcases valid with ⟨kind, deterministic, lower, upper, violation⟩
      rcases kind with rfl | rfl | rfl | rfl
      · intro holds
        exact not_lt_of_ge
          (holds A B garbling.disclosure (deterministic (Or.inl rfl)) lower upper) violation
      · intro holds
        exact not_lt_of_ge
          (holds A B garbling.disclosure (deterministic (Or.inr rfl)) lower upper) violation
      · intro holds
        have hlo := lower.toGeneral
        have hup := upper.toGeneral
        rw [wholeSignalDisclosure_toGeneral] at hlo hup
        have h := holds A B garbling.disclosure.toGeneral hlo hup
        rw [generalDisclosureWithWholeValue_toGeneral, generalDisclosureValue_toGeneral] at h
        exact not_lt_of_ge h violation
      · intro holds
        have hlo := lower.toGeneral
        have hup := upper.toGeneral
        rw [wholeSignalDisclosure_toGeneral] at hlo hup
        have h := holds A B garbling.disclosure.toGeneral hlo hup
        rw [generalDisclosureWithWholeValue_toGeneral, generalDisclosureValue_toGeneral] at h
        exact not_lt_of_ge h violation

end
end EconCSLib.OpenProblem.New.EconCSBench.InformationalSubstitutesComplements

end


section

/-!
## Real inputs and counterexamples

Priors and convex scores remain real. Moderate counterexamples use finite
deterministic summaries; strong counterexamples may have continuous report spaces.
Validity checks the actual witness. Finite representation, completeness and polynomial
certificate size must be established separately.
-/
namespace EconCSLib.OpenProblem.New.EconCSBench.InformationalSubstitutesComplements
open WordRAM.FiniteData

structure RealInformationInput where
  alphabet : InformationAlphabet
  source : FiniteBayesianInformation alphabet.State alphabet.Index alphabet.Signal

/-- A mathematical certificate. General disclosures are not bitstreams that a machine may
output at no cost. -/
inductive RealCertificationOutput (a : InformationAlphabet) : Type 1
  | accept
  | weakViolation (smaller larger added : Finset a.Index)
  | moderateViolation (A B : Finset a.Index)
      (disclosure : SignalDisclosure a.Index a.Signal)
  | strongViolation (A B : Finset a.Index)
      (disclosure : GeneralSignalDisclosure a.Index a.Signal)

noncomputable def RealCertificationOutput.Valid (I : RealInformationInput)
    (property : InformationalProperty) : RealCertificationOutput I.alphabet → Prop
  | .accept => HasInformationalProperty I.source property
  | .weakViolation smaller larger added =>
      (property = .weakSubstitutes ∨ property = .weakComplements) ∧
      larger ∩ added ⊆ smaller ∧ smaller ⊆ larger ∧
      ViolatesMarginal property
        (weakSignalValue I.source (added ∪ smaller) - weakSignalValue I.source smaller)
        (weakSignalValue I.source (added ∪ larger) - weakSignalValue I.source larger)
  | .moderateViolation A B disclosure =>
      (property = .moderateSubstitutes ∨ property = .moderateComplements) ∧
      SignalDisclosure.IsDeterministicOn I.source disclosure ∧
      IsBlackwellBelowOn I.source (wholeSignalDisclosure (A ∩ B)) disclosure ∧
      IsBlackwellBelowOn I.source disclosure (wholeSignalDisclosure A) ∧
      ViolatesMarginal property
        (disclosureWithWholeValue I.source B disclosure - disclosureValue I.source disclosure)
        (weakSignalValue I.source (A ∪ B) - weakSignalValue I.source A)
  | .strongViolation A B disclosure =>
      (property = .strongSubstitutes ∨ property = .strongComplements) ∧
      IsGeneralBlackwellBelowOn I.source (generalWholeSignalDisclosure (A ∩ B)) disclosure ∧
      IsGeneralBlackwellBelowOn I.source disclosure (generalWholeSignalDisclosure A) ∧
      ViolatesMarginal property
        (generalDisclosureWithWholeValue I.source B disclosure -
          generalDisclosureValue I.source disclosure)
        (weakSignalValue I.source (A ∪ B) - weakSignalValue I.source A)

/-- Full-real correctness. -/
noncomputable def IsRealCertificationCorrect (property : InformationalProperty)
    (procedure : (I : RealInformationInput) → RealCertificationOutput I.alphabet) : Prop :=
  ∀ I, (procedure I).Valid I property

/-- A validated negative output really contradicts the corresponding property; it is not
merely a false Boolean or an unrelated disclosure. -/
theorem RealCertificationOutput.Valid.rejects
    {I : RealInformationInput} {property : InformationalProperty}
    {certificate : RealCertificationOutput I.alphabet}
    (valid : certificate.Valid I property) (negative : certificate ≠ .accept) :
    ¬ HasInformationalProperty I.source property := by
  cases certificate with
  | accept => exact False.elim (negative rfl)
  | weakViolation smaller larger added =>
      rcases valid with ⟨kind, hinter, hsub, violation⟩
      rcases kind with rfl | rfl
      · intro holds
        exact not_lt_of_ge (holds smaller larger added hinter hsub) violation
      · intro holds
        exact not_lt_of_ge (holds smaller larger added hinter hsub) violation
  | moderateViolation A B disclosure =>
      rcases valid with ⟨kind, deterministic, lower, upper, violation⟩
      rcases kind with rfl | rfl
      · intro holds
        exact not_lt_of_ge (holds A B disclosure deterministic lower upper) violation
      · intro holds
        exact not_lt_of_ge (holds A B disclosure deterministic lower upper) violation
  | strongViolation A B disclosure =>
      rcases valid with ⟨kind, lower, upper, violation⟩
      rcases kind with rfl | rfl
      · intro holds
        exact not_lt_of_ge (holds A B disclosure lower upper) violation
      · intro holds
        exact not_lt_of_ge (holds A B disclosure lower upper) violation

/-- Failure has a mathematical negative witness. This classical existence statement gives
neither a code, a finite strong report alphabet nor an algorithm. -/
theorem exists_valid_real_negative_iff (I : RealInformationInput)
    (property : InformationalProperty) :
    (∃ certificate : RealCertificationOutput I.alphabet,
      certificate ≠ .accept ∧ certificate.Valid I property) ↔
        ¬ HasInformationalProperty I.source property := by
  classical
  constructor
  · rintro ⟨certificate, negative, valid⟩
    exact valid.rejects negative
  · intro fails
    cases property with
    | weakSubstitutes =>
        change ¬ IsLatticeSubmodular (weakSignalValue I.source) at fails
        simp only [IsLatticeSubmodular, not_forall, not_le] at fails
        obtain ⟨smaller, larger, added, lower, upper, violation⟩ := fails
        exact ⟨.weakViolation smaller larger added, by simp,
          Or.inl rfl, lower, upper, violation⟩
    | weakComplements =>
        change ¬ IsLatticeSupermodular (weakSignalValue I.source) at fails
        simp only [IsLatticeSupermodular, not_forall, not_le] at fails
        obtain ⟨smaller, larger, added, lower, upper, violation⟩ := fails
        exact ⟨.weakViolation smaller larger added, by simp,
          Or.inr rfl, lower, upper, violation⟩
    | moderateSubstitutes =>
        change ¬ IsModerateSubstitutes I.source at fails
        simp only [IsModerateSubstitutes, not_forall, not_le] at fails
        obtain ⟨A, B, disclosure, deterministic, lower, upper, violation⟩ := fails
        exact ⟨.moderateViolation A B disclosure, by simp,
          Or.inl rfl, deterministic, lower, upper, violation⟩
    | moderateComplements =>
        change ¬ IsModerateComplements I.source at fails
        simp only [IsModerateComplements, not_forall, not_le] at fails
        obtain ⟨A, B, disclosure, deterministic, lower, upper, violation⟩ := fails
        exact ⟨.moderateViolation A B disclosure, by simp,
          Or.inr rfl, deterministic, lower, upper, violation⟩
    | strongSubstitutes =>
        change ¬ IsStrongSubstitutes I.source at fails
        simp only [IsStrongSubstitutes, not_forall, not_le] at fails
        obtain ⟨A, B, disclosure, lower, upper, violation⟩ := fails
        exact ⟨.strongViolation A B disclosure, by simp, Or.inl rfl, lower, upper, violation⟩
    | strongComplements =>
        change ¬ IsStrongComplements I.source at fails
        simp only [IsStrongComplements, not_forall, not_le] at fails
        obtain ⟨A, B, disclosure, lower, upper, violation⟩ := fails
        exact ⟨.strongViolation A B disclosure, by simp, Or.inr rfl, lower, upper, violation⟩

/-- Decoding receives only alphabet and code. -/
abbrev RealCertificateDecoder :=
  (a : InformationAlphabet) → Code → Option (RealCertificationOutput a)

/-- Every failure in the declared domain must have a represented valid negative witness.
This is an obligation. -/
noncomputable def CertificateCompleteOn (domain : RealInformationInput → Prop)
    (decode : RealCertificateDecoder) (property : InformationalProperty) : Prop :=
  ∀ I, domain I → ¬ HasInformationalProperty I.source property →
    ∃ code certificate, decode I.alphabet code = some certificate ∧
      certificate ≠ .accept ∧ certificate.Valid I property

end EconCSLib.OpenProblem.New.EconCSBench.InformationalSubstitutesComplements

end


section

/-!
## Finite-report certificates with real coefficients

These mathematical certificates use finite report alphabets but arbitrary real kernel
coefficients and arbitrary real convex scores. Their embedding into the general-report
specification is proved sound. No completeness, bounded number of reports, rational
encoding or polynomial bit length is asserted here.
-/
namespace EconCSLib.OpenProblem.New.EconCSBench.InformationalSubstitutesComplements

/-- Certificates with a finite report alphabet and real-valued coefficients. -/
inductive FiniteRealCertificationOutput (a : InformationAlphabet) : Type 1
  | accept
  | weakViolation (smaller larger added : Finset a.Index)
  | moderateViolation (A B : Finset a.Index)
      (disclosure : SignalDisclosure a.Index a.Signal)
  | strongViolation (A B : Finset a.Index)
      (disclosure : SignalDisclosure a.Index a.Signal)

/-- Finite strong witnesses still refer to the original strong property. -/
noncomputable def FiniteRealCertificationOutput.Valid (I : RealInformationInput)
    (property : InformationalProperty) : FiniteRealCertificationOutput I.alphabet → Prop
  | .accept => HasInformationalProperty I.source property
  | .weakViolation smaller larger added =>
      (property = .weakSubstitutes ∨ property = .weakComplements) ∧
      larger ∩ added ⊆ smaller ∧ smaller ⊆ larger ∧
      ViolatesMarginal property
        (weakSignalValue I.source (added ∪ smaller) - weakSignalValue I.source smaller)
        (weakSignalValue I.source (added ∪ larger) - weakSignalValue I.source larger)
  | .moderateViolation A B disclosure =>
      (property = .moderateSubstitutes ∨ property = .moderateComplements) ∧
      SignalDisclosure.IsDeterministicOn I.source disclosure ∧
      IsBlackwellBelowOn I.source (wholeSignalDisclosure (A ∩ B)) disclosure ∧
      IsBlackwellBelowOn I.source disclosure (wholeSignalDisclosure A) ∧
      ViolatesMarginal property
        (disclosureWithWholeValue I.source B disclosure - disclosureValue I.source disclosure)
        (weakSignalValue I.source (A ∪ B) - weakSignalValue I.source A)
  | .strongViolation A B disclosure =>
      (property = .strongSubstitutes ∨ property = .strongComplements) ∧
      IsBlackwellBelowOn I.source (wholeSignalDisclosure (A ∩ B)) disclosure ∧
      IsBlackwellBelowOn I.source disclosure (wholeSignalDisclosure A) ∧
      ViolatesMarginal property
        (disclosureWithWholeValue I.source B disclosure - disclosureValue I.source disclosure)
        (weakSignalValue I.source (A ∪ B) - weakSignalValue I.source A)

/-- Preserve witness data and embed only the finite strong disclosure. -/
noncomputable def FiniteRealCertificationOutput.toReal {a : InformationAlphabet} :
    FiniteRealCertificationOutput a → RealCertificationOutput a
  | .accept => .accept
  | .weakViolation smaller larger added => .weakViolation smaller larger added
  | .moderateViolation A B disclosure => .moderateViolation A B disclosure
  | .strongViolation A B disclosure => .strongViolation A B disclosure.toGeneral

/-- The actual finite/general probability bridge validates the same strict violation. -/
theorem FiniteRealCertificationOutput.Valid.toReal
    {I : RealInformationInput} {property : InformationalProperty}
    {certificate : FiniteRealCertificationOutput I.alphabet}
    (valid : certificate.Valid I property) : certificate.toReal.Valid I property := by
  cases certificate with
  | accept => exact valid
  | weakViolation smaller larger added => exact valid
  | moderateViolation A B disclosure => exact valid
  | strongViolation A B disclosure =>
      rcases valid with ⟨kind, lower, upper, violation⟩
      have hlo := lower.toGeneral
      have hup := upper.toGeneral
      rw [wholeSignalDisclosure_toGeneral] at hlo hup
      refine ⟨kind, hlo, hup, ?_⟩
      simpa only [generalDisclosureWithWholeValue_toGeneral, generalDisclosureValue_toGeneral]
        using violation

/-- A finite-real negative certificate rejects the full six-property semantics. -/
theorem FiniteRealCertificationOutput.Valid.rejects
    {I : RealInformationInput} {property : InformationalProperty}
    {certificate : FiniteRealCertificationOutput I.alphabet}
    (valid : certificate.Valid I property) (negative : certificate ≠ .accept) :
    ¬ HasInformationalProperty I.source property := by
  apply valid.toReal.rejects
  cases certificate <;> simp_all [FiniteRealCertificationOutput.toReal]

end EconCSLib.OpenProblem.New.EconCSBench.InformationalSubstitutesComplements

end


section

/-!
## Posterior normalization and null-event invariance

The finite and Radon--Nikodym posteriors are probability vectors wherever they
contribute positive mass. Values therefore ignore the arbitrary off-simplex extension
of the expected score.
-/
namespace EconCSLib.OpenProblem.New.EconCSBench.InformationalSubstitutesComplements

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
noncomputable section

/-- Normalizing nonnegative finite masses gives a probability vector. -/
theorem probabilityVector_of_normalized_masses {State : Type*} [Fintype State]
    (mass : State → ℝ) (nonnegative : ∀ e, 0 ≤ mass e)
    (positive : 0 < ∑ e, mass e) :
    IsProbabilityVector (fun e => mass e / ∑ e, mass e) := by
  refine ⟨fun e => div_nonneg (nonnegative e) positive.le, ?_⟩
  rw [← Finset.sum_div, div_self positive.ne']

private theorem rnDeriv_finsetSum {X State : Type*} [MeasurableSpace X]
    (μ : State → Measure X) [∀ e, IsFiniteMeasure (μ e)]
    (ν : Measure X) [IsFiniteMeasure ν] (s : Finset State) :
    (∑ e ∈ s, μ e).rnDeriv ν =ᵐ[ν] fun x => ∑ e ∈ s, (μ e).rnDeriv ν x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty, Pi.zero_apply] using Measure.rnDeriv_zero ν
  | @insert e s not_mem ih =>
      simp only [Finset.sum_insert not_mem]
      filter_upwards [Measure.rnDeriv_add (μ e) (∑ e ∈ s, μ e) ν, ih] with x hadd hsum
      exact hadd.trans (congrArg (fun z => (μ e).rnDeriv ν x + z) hsum)

/-- A finite family of state-output measures has normalized RN posteriors almost
everywhere for its marginal law, even when some state laws vanish. -/
theorem rnPosterior_isProbabilityVector_ae {X State : Type*}
    [MeasurableSpace X] [Fintype State]
    (μ : State → Measure X) [∀ e, IsFiniteMeasure (μ e)] :
    ∀ᵐ x ∂(∑ e, μ e),
      IsProbabilityVector (fun e => ((μ e).rnDeriv (∑ e, μ e) x).toReal) := by
  classical
  have finite_derivatives :
      ∀ᵐ x ∂(∑ e, μ e), ∀ e, (μ e).rnDeriv (∑ e, μ e) x ≠ ∞ := by
    exact ae_all_iff.mpr fun e => Measure.rnDeriv_ne_top _ _
  filter_upwards [rnDeriv_finsetSum μ (∑ e, μ e) Finset.univ,
    (∑ e, μ e).rnDeriv_self, finite_derivatives] with x hsum hone hfinite
  refine ⟨fun _ => ENNReal.toReal_nonneg, ?_⟩
  have total : ∑ e, (μ e).rnDeriv (∑ e, μ e) x = 1 := hsum.symm.trans hone
  rw [← ENNReal.toReal_sum (fun e _ => hfinite e), total, ENNReal.toReal_one]

section Information
variable {State Index : Type*} {Signal : Index → Type*}
  [Fintype State] [Fintype Index] [DecidableEq Index]
  [∀ i, Fintype (Signal i)] [∀ i, DecidableEq (Signal i)]
  (source : FiniteBayesianInformation State Index Signal)

/-- Marginalizing a normalized prior through a Markov disclosure preserves total mass. -/
theorem generalDisclosureMeasure_isProbability (d : GeneralSignalDisclosure Index Signal) :
    IsProbabilityMeasure (generalDisclosureMeasure source d) := by
  classical
  letI : ∀ input, IsProbabilityMeasure (d.kernel input) := d.kernel_isProbability
  constructor
  simp only [generalDisclosureMeasure, generalDisclosureStateMeasure,
    Measure.finsetSum_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [← Fintype.sum_prod_type (fun pair : State × SignalProfile Index Signal =>
    ENNReal.ofReal (source.jointPrior.val pair))]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun pair _ => source.jointPrior.property.1 pair),
    source.jointPrior.property.2, ENNReal.ofReal_one]

/-- The marginal of every full signal profile is nonnegative. -/
theorem signalProfileProbability_nonnegative (input : SignalProfile Index Signal) :
    0 ≤ signalProfileProbability source input :=
  Finset.sum_nonneg fun e _ => source.jointPrior.property.1 (e, input)

/-- Every state's joint mass is bounded by the marginal profile mass. -/
theorem jointPrior_le_signalProfileProbability (e : State)
    (input : SignalProfile Index Signal) :
    source.jointPrior.val (e, input) ≤ signalProfileProbability source input := by
  apply Finset.single_le_sum (fun e _ => source.jointPrior.property.1 (e, input))
  exact Finset.mem_univ e

/-- Every state has zero joint mass at an unsupported full signal profile. -/
theorem jointPrior_eq_zero_of_not_supported (e : State)
    (input : SignalProfile Index Signal) (unsupported : ¬ 0 < signalProfileProbability source input) :
    source.jointPrior.val (e, input) = 0 :=
  le_antisymm ((jointPrior_le_signalProfileProbability source e input).trans
    (le_of_not_gt unsupported)) (source.jointPrior.property.1 (e, input))

/-- A whole observation includes the mass of each compatible full profile. -/
theorem signalProfileProbability_le_observationProbability (S : Finset Index)
    (input : SignalProfile Index Signal) :
    signalProfileProbability source input ≤ observationProbability source S input := by
  classical
  apply Finset.sum_le_sum
  intro e _
  have own : SameOn S input input := fun _ _ => rfl
  simpa only [if_pos own] using
    (Finset.single_le_sum (s := Finset.univ) (a := input)
      (f := fun b => if SameOn S input b then source.jointPrior.val (e, b) else 0)
      (fun b _ => by
        dsimp only
        split_ifs
        · exact source.jointPrior.property.1 (e, b)
        · exact le_rfl)
      (Finset.mem_univ input))

/-- Changing finite kernel rows outside the prior's support preserves every joint mass. -/
theorem disclosureJointMass_congr_on_support (d : SignalDisclosure Index Signal)
    (replacement : SignalProfile Index Signal → Lottery ℝ d.Output)
    (agree : ∀ input, 0 < signalProfileProbability source input →
      replacement input = d.kernel input) (e : State) (output : d.Output) :
    disclosureJointMass source { d with kernel := replacement } e output =
      disclosureJointMass source d e output := by
  classical
  apply Finset.sum_congr rfl
  intro input _
  by_cases supported : 0 < signalProfileProbability source input
  · change source.jointPrior.val (e, input) * (replacement input).val output = _
    rw [agree input supported]
  · simp [jointPrior_eq_zero_of_not_supported source e input supported]

/-- Unsupported finite kernel rows cannot change the disclosure's value. -/
theorem disclosureValue_congr_on_support (d : SignalDisclosure Index Signal)
    (replacement : SignalProfile Index Signal → Lottery ℝ d.Output)
    (agree : ∀ input, 0 < signalProfileProbability source input →
      replacement input = d.kernel input) :
    disclosureValue source { d with kernel := replacement } = disclosureValue source d := by
  unfold disclosureValue disclosurePosterior disclosureProbability
  simp only [disclosureJointMass_congr_on_support source d replacement agree]

/-- The same null-row invariance holds for arbitrary output measures. -/
theorem generalDisclosureStateMeasure_congr_on_support (d : GeneralSignalDisclosure Index Signal)
    (replacement : SignalProfile Index Signal → Measure d.Output)
    (probability : ∀ input, IsProbabilityMeasure (replacement input))
    (agree : ∀ input, 0 < signalProfileProbability source input →
      replacement input = d.kernel input) (e : State) :
    generalDisclosureStateMeasure source
        { d with kernel := replacement, kernel_isProbability := probability } e =
      generalDisclosureStateMeasure source d e := by
  classical
  apply Finset.sum_congr rfl
  intro input _
  by_cases supported : 0 < signalProfileProbability source input
  · change ENNReal.ofReal (source.jointPrior.val (e, input)) • replacement input = _
    rw [agree input supported]
  · simp [jointPrior_eq_zero_of_not_supported source e input supported]

/-- Null-row changes preserve the actual general-disclosure expected value. -/
theorem generalDisclosureValue_congr_on_support (d : GeneralSignalDisclosure Index Signal)
    (replacement : SignalProfile Index Signal → Measure d.Output)
    (probability : ∀ input, IsProbabilityMeasure (replacement input))
    (agree : ∀ input, 0 < signalProfileProbability source input →
      replacement input = d.kernel input) :
    generalDisclosureValue source
        { d with kernel := replacement, kernel_isProbability := probability } =
      generalDisclosureValue source d := by
  unfold generalDisclosureValue generalDisclosurePosterior generalDisclosureMeasure
  simp only [generalDisclosureStateMeasure_congr_on_support source d replacement probability agree]

/-- Null-row changes preserve joint report/whole-observation state laws. -/
theorem generalDisclosureWithWholeStateMeasure_congr_on_support
    [∀ i, Nonempty (Signal i)] (B : Finset Index)
    (d : GeneralSignalDisclosure Index Signal)
    (replacement : SignalProfile Index Signal → Measure d.Output)
    (probability : ∀ input, IsProbabilityMeasure (replacement input))
    (agree : ∀ input, 0 < signalProfileProbability source input →
      replacement input = d.kernel input) (observed : SignalProfile Index Signal) (e : State) :
    generalDisclosureWithWholeStateMeasure source B
        { d with kernel := replacement, kernel_isProbability := probability } observed e =
      generalDisclosureWithWholeStateMeasure source B d observed e := by
  classical
  apply Finset.sum_congr rfl
  intro input _
  by_cases supported : 0 < signalProfileProbability source input
  · change (if maskedSignalProfile B input = observed then
      ENNReal.ofReal (source.jointPrior.val (e, input)) • replacement input else 0) = _
    rw [agree input supported]
  · simp [jointPrior_eq_zero_of_not_supported source e input supported]

/-- Null rows cannot alter the marginal-value comparison's joint-value term. -/
theorem generalDisclosureWithWholeValue_congr_on_support
    [∀ i, Nonempty (Signal i)] (B : Finset Index)
    (d : GeneralSignalDisclosure Index Signal)
    (replacement : SignalProfile Index Signal → Measure d.Output)
    (probability : ∀ input, IsProbabilityMeasure (replacement input))
    (agree : ∀ input, 0 < signalProfileProbability source input →
      replacement input = d.kernel input) :
    generalDisclosureWithWholeValue source B
        { d with kernel := replacement, kernel_isProbability := probability } =
      generalDisclosureWithWholeValue source B d := by
  unfold generalDisclosureWithWholeValue generalDisclosureWithWholePosterior
    generalDisclosureWithWholeMeasure
  simp only [generalDisclosureWithWholeStateMeasure_congr_on_support
    source B d replacement probability agree]

/-- A nonnull whole-signal observation has a normalized Bayesian posterior. -/
theorem posterior_isProbabilityVector (S : Finset Index)
    (a : SignalProfile Index Signal) (positive : 0 < observationProbability source S a) :
    IsProbabilityVector (posterior source S a) := by
  classical
  apply probabilityVector_of_normalized_masses
  · intro e
    exact Finset.sum_nonneg fun b _ => by
      split_ifs
      · exact source.jointPrior.property.1 (e, b)
      · exact le_rfl
  · exact positive

/-- Every nonnull finite disclosure output has a normalized posterior. -/
theorem disclosurePosterior_isProbabilityVector (d : SignalDisclosure Index Signal)
    (output : d.Output) (positive : 0 < disclosureProbability source d output) :
    IsProbabilityVector (disclosurePosterior source d output) :=
  probabilityVector_of_normalized_masses _
    (fun e => disclosureJointMass_nonnegative source d e output) positive

/-- The same normalization holds after jointly observing whole signals. -/
theorem disclosureWithWholePosterior_isProbabilityVector [∀ i, Nonempty (Signal i)]
    (B : Finset Index) (d : SignalDisclosure Index Signal)
    (output : SignalProfile Index Signal × d.Output)
    (positive : 0 < disclosureWithWholeProbability source B d output) :
    IsProbabilityVector (disclosureWithWholePosterior source B d output) :=
  probabilityVector_of_normalized_masses _
    (fun e => disclosureWithWholeJointMass_nonnegative source B d e output) positive

/-- Arbitrary report spaces preserve posterior normalization almost everywhere. -/
theorem generalDisclosurePosterior_isProbabilityVector_ae
    (d : GeneralSignalDisclosure Index Signal) :
    ∀ᵐ output ∂generalDisclosureMeasure source d,
      IsProbabilityVector (generalDisclosurePosterior source d output) :=
  rnPosterior_isProbabilityVector_ae (generalDisclosureStateMeasure source d)

/-- A fixed whole-signal observation also has an almost-everywhere normalized posterior; a
zero-mass observation imposes no conditions. -/
theorem generalDisclosureWithWholePosterior_isProbabilityVector_ae
    [∀ i, Nonempty (Signal i)] (B : Finset Index)
    (d : GeneralSignalDisclosure Index Signal) (observed : SignalProfile Index Signal) :
    ∀ᵐ output ∂generalDisclosureWithWholeMeasure source B d observed,
      IsProbabilityVector (generalDisclosureWithWholePosterior source B d observed output) :=
  rnPosterior_isProbabilityVector_ae (generalDisclosureWithWholeStateMeasure source B d observed)

/-- Whole-signal values do not depend on the score outside its mathematical domain. -/
theorem weakSignalValue_score_congr (S : Finset Index)
    (score : (State → ℝ) → ℝ) (agree : ScoresAgreeOnSimplex source.score score) :
    weakSignalValue source S =
      ∑ input, signalProfileProbability source input * score (posterior source S input) := by
  apply Finset.sum_congr rfl
  intro input _
  by_cases positive : 0 < signalProfileProbability source input
  · rw [agree _ (posterior_isProbabilityVector source S input
      (positive.trans_le (signalProfileProbability_le_observationProbability source S input)))]
  · have zero : signalProfileProbability source input = 0 :=
      le_antisymm (le_of_not_gt positive) (signalProfileProbability_nonnegative source input)
    simp [zero]

/-- Finite disclosures also ignore the score's off-simplex extension. -/
theorem disclosureValue_score_congr (d : SignalDisclosure Index Signal)
    (score : (State → ℝ) → ℝ) (agree : ScoresAgreeOnSimplex source.score score) :
    disclosureValue source d =
      ∑ output, disclosureProbability source d output * score (disclosurePosterior source d output) := by
  apply Finset.sum_congr rfl
  intro output _
  by_cases positive : 0 < disclosureProbability source d output
  · rw [agree _ (disclosurePosterior_isProbabilityVector source d output positive)]
  · have zero : disclosureProbability source d output = 0 :=
      le_antisymm (le_of_not_gt positive)
        (Finset.sum_nonneg fun e _ => disclosureJointMass_nonnegative source d e output)
    simp [zero]

/-- Joint finite values require no regularity outside the simplex either. -/
theorem disclosureWithWholeValue_score_congr [∀ i, Nonempty (Signal i)]
    (B : Finset Index) (d : SignalDisclosure Index Signal)
    (score : (State → ℝ) → ℝ) (agree : ScoresAgreeOnSimplex source.score score) :
    disclosureWithWholeValue source B d =
      ∑ output, disclosureWithWholeProbability source B d output *
        score (disclosureWithWholePosterior source B d output) := by
  apply Finset.sum_congr rfl
  intro output _
  by_cases positive : 0 < disclosureWithWholeProbability source B d output
  · rw [agree _ (disclosureWithWholePosterior_isProbabilityVector source B d output positive)]
  · have zero : disclosureWithWholeProbability source B d output = 0 :=
      le_antisymm (le_of_not_gt positive)
        (Finset.sum_nonneg fun e _ => disclosureWithWholeJointMass_nonnegative source B d e output)
    simp [zero]

/-- Changing the score outside the simplex cannot change a general disclosure's value. -/
theorem generalDisclosureValue_score_congr (d : GeneralSignalDisclosure Index Signal)
    (score : (State → ℝ) → ℝ) (agree : ScoresAgreeOnSimplex source.score score) :
    generalDisclosureValue source d =
      ∫ output, score (generalDisclosurePosterior source d output)
        ∂generalDisclosureMeasure source d := by
  apply integral_congr_ae
  filter_upwards [generalDisclosurePosterior_isProbabilityVector_ae source d] with output normalized
  exact agree _ normalized

/-- The joint-disclosure value also depends only on the score on the simplex. -/
theorem generalDisclosureWithWholeValue_score_congr [∀ i, Nonempty (Signal i)]
    (B : Finset Index) (d : GeneralSignalDisclosure Index Signal)
    (score : (State → ℝ) → ℝ) (agree : ScoresAgreeOnSimplex source.score score) :
    generalDisclosureWithWholeValue source B d =
      ∑ observed, ∫ output, score (generalDisclosureWithWholePosterior source B d observed output)
        ∂generalDisclosureWithWholeMeasure source B d observed := by
  apply Finset.sum_congr rfl
  intro observed _
  apply integral_congr_ae
  filter_upwards [generalDisclosureWithWholePosterior_isProbabilityVector_ae
    source B d observed] with output normalized
  exact agree _ normalized

end Information
end
end EconCSLib.OpenProblem.New.EconCSBench.InformationalSubstitutesComplements

end


section

/-!
## General-disclosure expected scores are genuine integrals

A finite-valued convex score is Borel measurable and bounded on the simplex.
Radon--Nikodym posterior normalization gives integrability on every general report
space, without an extra regularity promise on the source.
-/
namespace EconCSLib.OpenProblem.New.EconCSBench.InformationalSubstitutesComplements
open MeasureTheory
noncomputable section

/-- Convex scores integrate against every measurable, almost surely normalized
finite-dimensional posterior under a finite measure. -/
theorem convexScore_integrable {E X : Type*} [Fintype E] [Nonempty E]
    [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (G : (E → ℝ) → ℝ) (convex : ConvexOn ℝ (stdSimplex ℝ E) G)
    (posterior : X → E → ℝ) (measurable : Measurable posterior)
    (probability : ∀ᵐ x ∂μ, IsProbabilityVector (posterior x)) :
    Integrable (fun x => G (posterior x)) μ := by
  have extended_measurable := (convexScore_measurable_on_simplex G convex).comp measurable
  have agree : (fun x => (stdSimplex ℝ E).indicator G (posterior x)) =ᵐ[μ]
      fun x => G (posterior x) := by
    filter_upwards [probability] with x hx
    exact Set.indicator_of_mem (show posterior x ∈ stdSimplex ℝ E from hx) G
  have strongly : AEStronglyMeasurable (fun x => G (posterior x)) μ :=
    extended_measurable.aestronglyMeasurable.congr agree
  obtain ⟨lower, upper, bounds⟩ := convexScore_bounded G convex
  apply Integrable.of_bound strongly (|lower| + |upper|)
  filter_upwards [probability] with x hx
  obtain ⟨below, above⟩ := bounds (posterior x) hx
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith [neg_abs_le lower, le_abs_self upper, abs_nonneg lower, abs_nonneg upper]

section Source
variable {State Index : Type*} {Signal : Index → Type*}
  [Fintype State] [Fintype Index] [DecidableEq Index]
  [∀ i, Fintype (Signal i)] [∀ i, DecidableEq (Signal i)]
  (source : FiniteBayesianInformation State Index Signal)

include source in
/-- Normalization already excludes an empty state alphabet. -/
theorem FiniteBayesianInformation.nonemptyState : Nonempty State := by
  cases isEmpty_or_nonempty State with
  | inr nonempty => exact nonempty
  | inl empty =>
      letI := empty
      have impossible := source.jointPrior.property.2
      simp at impossible

/-- General RN posteriors are measurable coordinatewise. -/
theorem generalDisclosurePosterior_measurable (d : GeneralSignalDisclosure Index Signal) :
    Measurable (generalDisclosurePosterior source d) := by
  apply measurable_pi_lambda
  intro e
  exact (Measure.measurable_rnDeriv _ _).ennreal_toReal

/-- The general-disclosure Bochner integral never falls back to a nonintegrable default. -/
theorem generalDisclosureScore_integrable (d : GeneralSignalDisclosure Index Signal) :
    Integrable (fun output => source.score (generalDisclosurePosterior source d output))
      (generalDisclosureMeasure source d) := by
  letI : Nonempty State := source.nonemptyState
  exact convexScore_integrable _ source.score source.convexOn_score _
    (generalDisclosurePosterior_measurable source d)
    (generalDisclosurePosterior_isProbabilityVector_ae source d)

/-- Joint report/whole-observation RN posteriors are also measurable. -/
theorem generalDisclosureWithWholePosterior_measurable [∀ i, Nonempty (Signal i)]
    (B : Finset Index) (d : GeneralSignalDisclosure Index Signal)
    (observed : SignalProfile Index Signal) :
    Measurable (generalDisclosureWithWholePosterior source B d observed) := by
  apply measurable_pi_lambda
  intro e
  exact (Measure.measurable_rnDeriv _ _).ennreal_toReal

/-- Every joint-observation summand is integrable, including zero-mass observations. -/
theorem generalDisclosureWithWholeScore_integrable [∀ i, Nonempty (Signal i)]
    (B : Finset Index) (d : GeneralSignalDisclosure Index Signal)
    (observed : SignalProfile Index Signal) :
    Integrable
      (fun output => source.score (generalDisclosureWithWholePosterior source B d observed output))
      (generalDisclosureWithWholeMeasure source B d observed) := by
  letI : Nonempty State := source.nonemptyState
  exact convexScore_integrable _ source.score source.convexOn_score _
    (generalDisclosureWithWholePosterior_measurable source B d observed)
    (generalDisclosureWithWholePosterior_isProbabilityVector_ae source B d observed)

end Source
end
end EconCSLib.OpenProblem.New.EconCSBench.InformationalSubstitutesComplements

end


section

/-!
## Grouped whole-signal source representation

The grouping variable is the allowed whole observation S. All conditional coefficients
are fixed by the original joint prior.
-/
namespace EconCSLib.OpenProblem.New.EconCSBench.InformationalSubstitutesComplements.FiniteWitness
open EconCSLib.OpenProblem.New.EconCSBench.InformationalSubstitutesComplements
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
noncomputable section

variable {State Index : Type*} {Signal : Index → Type*}
  [Fintype State] [Fintype Index] [DecidableEq Index]
  [∀ i, Fintype (Signal i)] [∀ i, DecidableEq (Signal i)] [∀ i, Nonempty (Signal i)]
  (source : FiniteBayesianInformation State Index Signal)

/-- Probability mass of one canonical masked S-observation. -/
def groupPriorMass (S : Finset Index) (x : SignalProfile Index Signal) : ℝ :=
  ∑ input, if maskedSignalProfile S input = x then signalProfileProbability source input else 0

/-- Joint mass of the S-observation, state, and B-observation. -/
def groupJointMass (S B : Finset Index) (x : SignalProfile Index Signal)
    (e : State) (y : SignalProfile Index Signal) : ℝ :=
  ∑ input, if maskedSignalProfile S input = x then
    if maskedSignalProfile B input = y then source.jointPrior.val (e, input) else 0 else 0

theorem groupPriorMass_nonnegative (S : Finset Index) (x : SignalProfile Index Signal) :
    0 ≤ groupPriorMass source S x := by
  apply Finset.sum_nonneg
  intro input _
  split_ifs
  · exact signalProfileProbability_nonnegative source input
  · exact le_rfl

theorem groupJointMass_nonnegative (S B : Finset Index) (x : SignalProfile Index Signal)
    (e : State) (y : SignalProfile Index Signal) : 0 ≤ groupJointMass source S B x e y := by
  apply Finset.sum_nonneg
  intro input _
  split_ifs
  · exact source.jointPrior.property.1 (e, input)
  · exact le_rfl
  · exact le_rfl

/-- The grouped prior has total mass one, including unused canonical labels at mass zero. -/
theorem sum_groupPriorMass (S : Finset Index) : (∑ x, groupPriorMass source S x) = 1 := by
  classical
  unfold groupPriorMass
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  unfold signalProfileProbability
  rw [Finset.sum_comm, ← Fintype.sum_prod_type]
  exact source.jointPrior.property.2

/-- The grouped probability distribution reuses the native finite lottery type. -/
def groupPrior (S : Finset Index) : Lottery ℝ (SignalProfile Index Signal) :=
  ⟨groupPriorMass source S, groupPriorMass_nonnegative source S, sum_groupPriorMass source S⟩

/-- Marginalizing the conditional table gives exactly the S-prior. -/
theorem sum_groupJointMass (S B : Finset Index) (x : SignalProfile Index Signal) :
    (∑ e, ∑ y, groupJointMass source S B x e y) = groupPriorMass source S x := by
  classical
  unfold groupJointMass
  have inner (e : State) :
      (∑ y, ∑ input, if maskedSignalProfile S input = x then
        if maskedSignalProfile B input = y then source.jointPrior.val (e, input) else 0 else 0) =
      ∑ input, if maskedSignalProfile S input = x then source.jointPrior.val (e, input) else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro input _
    split_ifs
    · simp only [if_true, Finset.sum_ite_eq, Finset.mem_univ]
    · simp only [Finset.sum_const_zero]
  simp_rw [inner]
  rw [Finset.sum_comm]
  unfold groupPriorMass signalProfileProbability
  apply Finset.sum_congr rfl
  intro input _
  split_ifs <;> simp_all

/-- Source-fixed conditional E,B table; a zero-prior row is the zero table. -/
def groupConditional (S B : Finset Index) (x : SignalProfile Index Signal)
    (e : State) (y : SignalProfile Index Signal) : ℝ :=
  groupJointMass source S B x e y / groupPriorMass source S x

theorem groupConditional_nonnegative (S B : Finset Index) (x : SignalProfile Index Signal)
    (e : State) (y : SignalProfile Index Signal) :
    0 ≤ groupConditional source S B x e y :=
  div_nonneg (groupJointMass_nonnegative source S B x e y) (groupPriorMass_nonnegative source S x)

/-- Positive S-prior rows are genuine conditional distributions on E×B. -/
theorem sum_groupConditional (S B : Finset Index) (x : SignalProfile Index Signal)
    (positive : 0 < groupPriorMass source S x) :
    (∑ e, ∑ y, groupConditional source S B x e y) = 1 := by
  unfold groupConditional
  simp_rw [← Finset.sum_div]
  rw [sum_groupJointMass, div_self positive.ne']

/-- The actual Markov factor supplied by the upper Blackwell witness. -/
def wholeFactorKernel (S : Finset Index) (d : GeneralSignalDisclosure Index Signal)
    (upper : IsGeneralBlackwellBelowOn source d (generalWholeSignalDisclosure S)) :
    Kernel (generalWholeSignalDisclosure (Signal := Signal) S).Output d.Output :=
  upper.choose

instance wholeFactorKernel_isMarkov (S : Finset Index) (d : GeneralSignalDisclosure Index Signal)
    (upper : IsGeneralBlackwellBelowOn source d (generalWholeSignalDisclosure S)) :
    IsMarkovKernel (wholeFactorKernel source S d upper) := upper.choose_spec.1

theorem kernel_eq_wholeFactorKernel (S : Finset Index) (d : GeneralSignalDisclosure Index Signal)
    (upper : IsGeneralBlackwellBelowOn source d (generalWholeSignalDisclosure S))
    (input : SignalProfile Index Signal) (positive : 0 < signalProfileProbability source input) :
    d.kernel input = wholeFactorKernel source S d upper (maskedSignalProfile S input) := by
  have h := upper.choose_spec.2 input positive
  exact h.trans (Measure.dirac_bind (wholeFactorKernel source S d upper).measurable _)

private theorem weightedFiber_factorization
    (S : Finset Index) (d : GeneralSignalDisclosure Index Signal)
    (upper : IsGeneralBlackwellBelowOn source d (generalWholeSignalDisclosure S))
    (a : SignalProfile Index Signal → ℝ) (nonnegative : ∀ input, 0 ≤ a input)
    (supported : ∀ input, ¬ 0 < signalProfileProbability source input → a input = 0)
    (x : SignalProfile Index Signal) :
    (∑ input, if maskedSignalProfile S input = x then ENNReal.ofReal (a input) • d.kernel input else 0) =
      ENNReal.ofReal (∑ input, if maskedSignalProfile S input = x then a input else 0) •
        wholeFactorKernel source S d upper x := by
  classical
  rw [ENNReal.ofReal_sum_of_nonneg (fun input _ => by
    split_ifs
    · exact nonnegative input
    · exact le_rfl), Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro input _
  by_cases hx : maskedSignalProfile S input = x
  · simp only [hx, if_true]
    by_cases hp : 0 < signalProfileProbability source input
    · rw [kernel_eq_wholeFactorKernel source S d upper input hp, hx]
    · simp [supported input hp]
  · simp [hx]

/-- Arbitrary prior-supported nonnegative weights factor through the allowed
S-observation. -/
theorem weightedSource_factorization
    (S : Finset Index) (d : GeneralSignalDisclosure Index Signal)
    (upper : IsGeneralBlackwellBelowOn source d (generalWholeSignalDisclosure S))
    (a : SignalProfile Index Signal → ℝ) (nonnegative : ∀ input, 0 ≤ a input)
    (supported : ∀ input, ¬ 0 < signalProfileProbability source input → a input = 0) :
    (∑ input, ENNReal.ofReal (a input) • d.kernel input) =
      ∑ x, ENNReal.ofReal (∑ input, if maskedSignalProfile S input = x then a input else 0) •
        wholeFactorKernel source S d upper x := by
  classical
  simp_rw [← weightedFiber_factorization source S d upper a nonnegative supported]
  rw [Finset.sum_comm]
  simp

/-- Joint S/report component law, indexed only by allowed whole observations. -/
def groupReportMeasure (S : Finset Index) (d : GeneralSignalDisclosure Index Signal)
    (upper : IsGeneralBlackwellBelowOn source d (generalWholeSignalDisclosure S))
    (x : SignalProfile Index Signal) : Measure d.Output :=
  ENNReal.ofReal (groupPriorMass source S x) • wholeFactorKernel source S d upper x

instance groupReportMeasure_isFinite (S : Finset Index) (d : GeneralSignalDisclosure Index Signal)
    (upper : IsGeneralBlackwellBelowOn source d (generalWholeSignalDisclosure S))
    (x : SignalProfile Index Signal) : IsFiniteMeasure (groupReportMeasure source S d upper x) := by
  constructor
  simp [groupReportMeasure, Measure.smul_apply]

/-- The grouped report laws sum to the exact original report marginal. -/
theorem sum_groupReportMeasure (S : Finset Index) (d : GeneralSignalDisclosure Index Signal)
    (upper : IsGeneralBlackwellBelowOn source d (generalWholeSignalDisclosure S)) :
    (∑ x, groupReportMeasure source S d upper x) = generalDisclosureMeasure source d := by
  have h := weightedSource_factorization source S d upper (signalProfileProbability source)
    (signalProfileProbability_nonnegative source)
    (fun input hp => le_antisymm (le_of_not_gt hp) (signalProfileProbability_nonnegative source input))
  change (∑ input, ENNReal.ofReal (signalProfileProbability source input) • d.kernel input) =
    ∑ x, groupReportMeasure source S d upper x at h
  rw [← h]
  unfold signalProfileProbability generalDisclosureMeasure generalDisclosureStateMeasure
  simp_rw [ENNReal.ofReal_sum_of_nonneg (fun e _ => source.jointPrior.property.1 (e, _)),
    Finset.sum_smul]
  exact Finset.sum_comm

/-- Each E,B report slice factors through the same upper-witness channel. -/
theorem wholeStateMeasure_grouped (S B : Finset Index) (d : GeneralSignalDisclosure Index Signal)
    (upper : IsGeneralBlackwellBelowOn source d (generalWholeSignalDisclosure S))
    (e : State) (y : SignalProfile Index Signal) :
    generalDisclosureWithWholeStateMeasure source B d y e =
      ∑ x, ENNReal.ofReal (groupJointMass source S B x e y) • wholeFactorKernel source S d upper x := by
  classical
  let a := fun input => if maskedSignalProfile B input = y then source.jointPrior.val (e, input) else 0
  have hnonnegative : ∀ input, 0 ≤ a input := by
    intro input
    dsimp [a]
    split_ifs
    · exact source.jointPrior.property.1 (e, input)
    · exact le_rfl
  have hsupported : ∀ input, ¬ 0 < signalProfileProbability source input → a input = 0 := by
    intro input hp
    simp [a, jointPrior_eq_zero_of_not_supported source e input hp]
  have h := weightedSource_factorization source S d upper a hnonnegative hsupported
  simpa [a, generalDisclosureWithWholeStateMeasure, groupJointMass, apply_ite, ite_smul] using h

/-- No entry of the grouped joint table exceeds its S-marginal. -/
theorem groupJointMass_le_prior (S B : Finset Index) (x : SignalProfile Index Signal)
    (e : State) (y : SignalProfile Index Signal) :
    groupJointMass source S B x e y ≤ groupPriorMass source S x := by
  calc
    groupJointMass source S B x e y ≤ ∑ y', groupJointMass source S B x e y' :=
      Finset.single_le_sum (fun y' _ => groupJointMass_nonnegative source S B x e y')
        (Finset.mem_univ y)
    _ ≤ ∑ e', ∑ y', groupJointMass source S B x e' y' :=
      Finset.single_le_sum
        (fun e' _ => Finset.sum_nonneg (fun y' _ => groupJointMass_nonnegative source S B x e' y'))
        (Finset.mem_univ e)
    _ = groupPriorMass source S x := sum_groupJointMass source S B x

/-- The conditional table reproduces its joint masses, even at null S-labels. -/
theorem groupConditional_mul_prior (S B : Finset Index) (x : SignalProfile Index Signal)
    (e : State) (y : SignalProfile Index Signal) :
    groupConditional source S B x e y * groupPriorMass source S x = groupJointMass source S B x e y := by
  by_cases hz : groupPriorMass source S x = 0
  · have hj : groupJointMass source S B x e y = 0 := by
      apply le_antisymm
      · simpa only [hz] using groupJointMass_le_prior source S B x e y
      · exact groupJointMass_nonnegative source S B x e y
    simp [hz, hj]
  · exact div_mul_cancel₀ _ hz

/-- State/B slices are linear mixtures of grouped source/report laws with fixed
coefficients. -/
theorem wholeStateMeasure_groupConditional (S B : Finset Index)
    (d : GeneralSignalDisclosure Index Signal)
    (upper : IsGeneralBlackwellBelowOn source d (generalWholeSignalDisclosure S))
    (e : State) (y : SignalProfile Index Signal) :
    generalDisclosureWithWholeStateMeasure source B d y e =
      ∑ x, ENNReal.ofReal (groupConditional source S B x e y) •
        groupReportMeasure source S d upper x := by
  rw [wholeStateMeasure_grouped source S B d upper e y]
  apply Finset.sum_congr rfl
  intro x _
  rw [groupReportMeasure, smul_smul, ← ENNReal.ofReal_mul
    (groupConditional_nonnegative source S B x e y), groupConditional_mul_prior]

private theorem rnDeriv_real_finsetSum {X Z : Type*} [MeasurableSpace Z]
    (μ : X → Measure Z) [∀ x, IsFiniteMeasure (μ x)]
    (ν : Measure Z) [IsFiniteMeasure ν] (t : Finset X) :
    (fun z => ((∑ x ∈ t, μ x).rnDeriv ν z).toReal) =ᵐ[ν]
      (fun z => ∑ x ∈ t, ((μ x).rnDeriv ν z).toReal) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
      filter_upwards [Measure.rnDeriv_zero ν] with z hz
      simp only [Finset.sum_empty, hz, Pi.zero_apply, ENNReal.toReal_zero]
  | @insert x t hnot ih =>
      simp only [Finset.sum_insert hnot]
      filter_upwards [Measure.rnDeriv_add (μ x) (∑ y ∈ t, μ y) ν,
        Measure.rnDeriv_ne_top (μ x) ν, Measure.rnDeriv_ne_top (∑ y ∈ t, μ y) ν,
        ih] with z hadd hx ht hsum
      rw [hadd, Pi.add_apply, ENNReal.toReal_add hx ht, hsum]

private theorem rnDeriv_real_weightedSum {X Z : Type*} [Fintype X] [MeasurableSpace Z]
    (μ : X → Measure Z) [∀ x, IsFiniteMeasure (μ x)]
    (ν : Measure Z) [IsFiniteMeasure ν] (a : X → ℝ) (nonnegative : ∀ x, 0 ≤ a x) :
    (fun z => ((∑ x, ENNReal.ofReal (a x) • μ x).rnDeriv ν z).toReal) =ᵐ[ν]
      (fun z => ∑ x, a x * ((μ x).rnDeriv ν z).toReal) := by
  letI : ∀ x, IsFiniteMeasure (ENNReal.ofReal (a x) • μ x) := fun x =>
    ⟨by simp [Measure.smul_apply, ENNReal.mul_lt_top]⟩
  have scalars : ∀ x, (ENNReal.ofReal (a x) • μ x).rnDeriv ν =ᵐ[ν]
      ENNReal.ofReal (a x) • (μ x).rnDeriv ν :=
    fun x => Measure.rnDeriv_smul_left_of_ne_top (μ x) ν ENNReal.ofReal_ne_top
  filter_upwards [rnDeriv_real_finsetSum (fun x => ENNReal.ofReal (a x) • μ x) ν Finset.univ,
    ae_all_iff.mpr scalars] with z hsum hscalar
  rw [hsum]
  apply Finset.sum_congr rfl
  intro x _
  simp only [hscalar x, Pi.smul_apply, smul_eq_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (nonnegative x)]

/-- RN posterior of the allowed whole S-observation, with no extra information in its
labels. -/
def groupPosterior (S : Finset Index) (d : GeneralSignalDisclosure Index Signal)
    (upper : IsGeneralBlackwellBelowOn source d (generalWholeSignalDisclosure S))
    (output : d.Output) (x : SignalProfile Index Signal) : ℝ :=
  ((groupReportMeasure source S d upper x).rnDeriv (generalDisclosureMeasure source d) output).toReal

/-- Grouped posterior vectors are normalized almost everywhere. -/
theorem groupPosterior_isProbabilityVector_ae (S : Finset Index)
    (d : GeneralSignalDisclosure Index Signal)
    (upper : IsGeneralBlackwellBelowOn source d (generalWholeSignalDisclosure S)) :
    ∀ᵐ output ∂generalDisclosureMeasure source d,
      IsProbabilityVector (groupPosterior source S d upper output) := by
  have h := rnPosterior_isProbabilityVector_ae (groupReportMeasure source S d upper)
  simpa only [sum_groupReportMeasure, groupPosterior] using h

/-- Null grouped-prior coordinates are null in the grouped posterior almost everywhere. -/
theorem groupPosterior_supported_ae (S : Finset Index)
    (d : GeneralSignalDisclosure Index Signal)
    (upper : IsGeneralBlackwellBelowOn source d (generalWholeSignalDisclosure S)) :
    ∀ᵐ output ∂generalDisclosureMeasure source d, ∀ x,
      groupPriorMass source S x = 0 → groupPosterior source S d upper output x = 0 := by
  apply ae_all_iff.mpr
  intro x
  by_cases hx : groupPriorMass source S x = 0
  · have hz : groupReportMeasure source S d upper x = 0 := by simp [groupReportMeasure, hx]
    unfold groupPosterior
    rw [hz]
    filter_upwards [Measure.rnDeriv_zero (generalDisclosureMeasure source d)] with output h _
    simp only [h, Pi.zero_apply, ENNReal.toReal_zero]
  · exact Filter.Eventually.of_forall (fun _ h => (hx h).elim)

/-- Bayes plausibility for the grouped S-observation. -/
theorem integral_groupPosterior (S : Finset Index) (d : GeneralSignalDisclosure Index Signal)
    (upper : IsGeneralBlackwellBelowOn source d (generalWholeSignalDisclosure S))
    (x : SignalProfile Index Signal) :
    (∫ output, groupPosterior source S d upper output x ∂generalDisclosureMeasure source d) =
      groupPriorMass source S x := by
  have hac : groupReportMeasure source S d upper x ≪ generalDisclosureMeasure source d := by
    rw [← sum_groupReportMeasure source S d upper]
    apply Measure.absolutelyContinuous_of_le
    exact Finset.single_le_sum (fun _ _ => Measure.zero_le _) (Finset.mem_univ x)
  unfold groupPosterior
  rw [Measure.integral_toReal_rnDeriv hac]
  simp [Measure.real, groupReportMeasure, Measure.smul_apply,
    ENNReal.toReal_ofReal (groupPriorMass_nonnegative source S x)]

/-- The actual E,B report density is the prior-fixed conditional table applied to q_S.
This is the source-level linearization. -/
theorem wholeStateDensity_groupConditional (S B : Finset Index)
    (d : GeneralSignalDisclosure Index Signal)
    (upper : IsGeneralBlackwellBelowOn source d (generalWholeSignalDisclosure S))
    (e : State) (y : SignalProfile Index Signal) :
    (fun output => ((generalDisclosureWithWholeStateMeasure source B d y e).rnDeriv
      (generalDisclosureMeasure source d) output).toReal) =ᵐ[generalDisclosureMeasure source d]
      (fun output => ∑ x, groupConditional source S B x e y * groupPosterior source S d upper output x) := by
  rw [wholeStateMeasure_groupConditional source S B d upper e y]
  exact rnDeriv_real_weightedSum (groupReportMeasure source S d upper) (generalDisclosureMeasure source d)
    (fun x => groupConditional source S B x e y) (fun x => groupConditional_nonnegative source S B x e y)

/-- Whole-observation/report density is the state marginal of the conditional table
mixture. -/
theorem wholeProbabilityDensity_groupConditional (S B : Finset Index)
    (d : GeneralSignalDisclosure Index Signal)
    (upper : IsGeneralBlackwellBelowOn source d (generalWholeSignalDisclosure S))
    (y : SignalProfile Index Signal) :
    (fun output => ((generalDisclosureWithWholeMeasure source B d y).rnDeriv
      (generalDisclosureMeasure source d) output).toReal) =ᵐ[generalDisclosureMeasure source d]
      (fun output => ∑ e, ∑ x,
        groupConditional source S B x e y * groupPosterior source S d upper output x) := by
  have hsum := rnDeriv_real_finsetSum (generalDisclosureWithWholeStateMeasure source B d y)
    (generalDisclosureMeasure source d) Finset.univ
  have hjoint := ae_all_iff.mpr (fun e => wholeStateDensity_groupConditional source S B d upper e y)
  filter_upwards [hsum, hjoint] with output hsum hjoint
  change ((∑ e, generalDisclosureWithWholeStateMeasure source B d y e).rnDeriv
    (generalDisclosureMeasure source d) output).toReal = _
  rw [hsum]
  exact Finset.sum_congr rfl (fun e _ => hjoint e)

/-- Marginalizing all B-observations restores the state/report measure. -/
theorem sum_wholeStateMeasure (B : Finset Index) (d : GeneralSignalDisclosure Index Signal)
    (e : State) :
    (∑ y, generalDisclosureWithWholeStateMeasure source B d y e) =
      generalDisclosureStateMeasure source d e := by
  classical
  unfold generalDisclosureWithWholeStateMeasure generalDisclosureStateMeasure
  rw [Finset.sum_comm]
  simp

/-- State/report density is the B-marginal of the same conditional table mixture. -/
theorem stateDensity_groupConditional (S B : Finset Index)
    (d : GeneralSignalDisclosure Index Signal)
    (upper : IsGeneralBlackwellBelowOn source d (generalWholeSignalDisclosure S))
    (e : State) :
    (fun output => ((generalDisclosureStateMeasure source d e).rnDeriv
      (generalDisclosureMeasure source d) output).toReal) =ᵐ[generalDisclosureMeasure source d]
      (fun output => ∑ y, ∑ x,
        groupConditional source S B x e y * groupPosterior source S d upper output x) := by
  have hsum := rnDeriv_real_finsetSum (fun y => generalDisclosureWithWholeStateMeasure source B d y e)
    (generalDisclosureMeasure source d) Finset.univ
  have hjoint := ae_all_iff.mpr (fun y => wholeStateDensity_groupConditional source S B d upper e y)
  filter_upwards [hsum, hjoint] with output hsum hjoint
  rw [← sum_wholeStateMeasure source B d e, hsum]
  exact Finset.sum_congr rfl (fun y _ => hjoint y)

end
end EconCSLib.OpenProblem.New.EconCSBench.InformationalSubstitutesComplements.FiniteWitness

end


section

/-!
## RN change-of-base lemma for posterior scores

Zero-density reports are handled by the multiplying marginal density, not by a
pointwise conditional-probability claim on null reports.
-/
namespace EconCSLib.OpenProblem.New.EconCSBench.InformationalSubstitutesComplements.FiniteWitness
open EconCSLib.OpenProblem.New.EconCSBench.InformationalSubstitutesComplements
open MeasureTheory
open scoped BigOperators ENNReal
noncomputable section

variable {E Z : Type*} [Fintype E] [MeasurableSpace Z]

/-- Finite component domination is preserved under summation. -/
theorem sum_absolutelyContinuous (ν : E → Measure Z) (μ : Measure Z)
    (dominated : ∀ e, ν e ≪ μ) : (∑ e, ν e) ≪ μ := by
  intro s hs
  simp only [Measure.finsetSum_apply, fun e => dominated e hs, Finset.sum_const_zero]

/-- Multiplication by the marginal density removes the null-report ambiguity. -/
theorem weighted_posteriorScore_congr_ae
    (ν : E → Measure Z) [∀ e, IsFiniteMeasure (ν e)]
    (μ : Measure Z) [IsFiniteMeasure μ] (dominated : ∀ e, ν e ≪ μ)
    (G : (E → ℝ) → ℝ) :
    (fun z => ((∑ e, ν e).rnDeriv μ z).toReal *
      G (fun e => ((ν e).rnDeriv (∑ e, ν e) z).toReal)) =ᵐ[μ]
      (fun z => ((∑ e, ν e).rnDeriv μ z).toReal *
        G (fun e => ((ν e).rnDeriv μ z).toReal / ((∑ e, ν e).rnDeriv μ z).toReal)) := by
  have hsum := sum_absolutelyContinuous ν μ dominated
  have ratio : ∀ᵐ z ∂(∑ e, ν e),
      (fun e => ((ν e).rnDeriv (∑ e, ν e) z).toReal) =
        (fun e => ((ν e).rnDeriv μ z).toReal / ((∑ e, ν e).rnDeriv μ z).toReal) := by
    have hall := ae_all_iff.mpr (fun e => Measure.rnDeriv_eq_div (dominated e) hsum)
    filter_upwards [hall] with z hz
    funext e
    rw [hz e, ENNReal.toReal_div]
  filter_upwards [Measure.ae_rnDeriv_ne_zero_imp_of_ae μ ratio] with z hz
  by_cases hzero : (∑ e, ν e).rnDeriv μ z = 0
  · simp only [hzero, ENNReal.toReal_zero, zero_mul]
  · rw [hz hzero]

/-- Posterior expected score can be written using a common dominating report law. No extra
score regularity or positive-density assumption is needed for this identity. -/
theorem integral_posteriorScore_density
    (ν : E → Measure Z) [∀ e, IsFiniteMeasure (ν e)]
    (μ : Measure Z) [IsFiniteMeasure μ] (dominated : ∀ e, ν e ≪ μ)
    (G : (E → ℝ) → ℝ) :
    (∫ z, G (fun e => ((ν e).rnDeriv (∑ e, ν e) z).toReal) ∂(∑ e, ν e)) =
      ∫ z, ((∑ e, ν e).rnDeriv μ z).toReal *
        G (fun e => ((ν e).rnDeriv μ z).toReal / ((∑ e, ν e).rnDeriv μ z).toReal) ∂μ := by
  rw [← integral_toReal_rnDeriv_mul (sum_absolutelyContinuous ν μ dominated)]
  exact integral_congr_ae (weighted_posteriorScore_congr_ae ν μ dominated G)

/-- Changing the density representation also preserves integrability. -/
theorem integrable_posteriorScore_density_iff
    (ν : E → Measure Z) [∀ e, IsFiniteMeasure (ν e)]
    (μ : Measure Z) [IsFiniteMeasure μ] (dominated : ∀ e, ν e ≪ μ)
    (G : (E → ℝ) → ℝ) :
    Integrable (fun z => ((∑ e, ν e).rnDeriv μ z).toReal *
      G (fun e => ((ν e).rnDeriv μ z).toReal / ((∑ e, ν e).rnDeriv μ z).toReal)) μ ↔
      Integrable (fun z => G (fun e => ((ν e).rnDeriv (∑ e, ν e) z).toReal)) (∑ e, ν e) := by
  rw [← integrable_congr (weighted_posteriorScore_congr_ae ν μ dominated G)]
  exact integrable_toReal_rnDeriv_mul_iff (sum_absolutelyContinuous ν μ dominated)

section Source
variable {State Index : Type*} {Signal : Index → Type*}
  [Fintype State] [Fintype Index] [DecidableEq Index]
  [∀ i, Fintype (Signal i)] [∀ i, DecidableEq (Signal i)] [∀ i, Nonempty (Signal i)]
  (source : FiniteBayesianInformation State Index Signal)

/-- Each joint state/whole-observation slice is dominated by the report marginal. -/
theorem wholeStateMeasure_absolutelyContinuous (B : Finset Index)
    (d : GeneralSignalDisclosure Index Signal) (observed : SignalProfile Index Signal) (e : State) :
    generalDisclosureWithWholeStateMeasure source B d observed e ≪
      generalDisclosureMeasure source d := by
  classical
  apply Measure.absolutelyContinuous_of_le
  calc
    generalDisclosureWithWholeStateMeasure source B d observed e ≤
        generalDisclosureStateMeasure source d e := by
      unfold generalDisclosureWithWholeStateMeasure generalDisclosureStateMeasure
      apply Finset.sum_le_sum
      intro input _
      split_ifs
      · exact le_rfl
      · exact Measure.zero_le _
    _ ≤ generalDisclosureMeasure source d :=
      Finset.single_le_sum (fun _ _ => Measure.zero_le _) (Finset.mem_univ e)

/-- Joint-observation score density with respect to the unsliced report marginal. -/
def wholeScoreDensity (B : Finset Index) (d : GeneralSignalDisclosure Index Signal)
    (observed : SignalProfile Index Signal) (output : d.Output) : ℝ :=
  ((generalDisclosureWithWholeMeasure source B d observed).rnDeriv
    (generalDisclosureMeasure source d) output).toReal *
  source.score (fun e => ((generalDisclosureWithWholeStateMeasure source B d observed e).rnDeriv
    (generalDisclosureMeasure source d) output).toReal /
    ((generalDisclosureWithWholeMeasure source B d observed).rnDeriv
      (generalDisclosureMeasure source d) output).toReal)

/-- The actual source's slice integral has the common-density expression. -/
theorem integral_wholeScoreDensity (B : Finset Index)
    (d : GeneralSignalDisclosure Index Signal) (observed : SignalProfile Index Signal) :
    (∫ output, source.score (generalDisclosureWithWholePosterior source B d observed output)
      ∂generalDisclosureWithWholeMeasure source B d observed) =
      ∫ output, wholeScoreDensity source B d observed output ∂generalDisclosureMeasure source d :=
  integral_posteriorScore_density (generalDisclosureWithWholeStateMeasure source B d observed)
    (generalDisclosureMeasure source d) (wholeStateMeasure_absolutelyContinuous source B d observed)
    source.score

/-- The density is integrable under the original model's arbitrary finite convex score. -/
theorem wholeScoreDensity_integrable (B : Finset Index)
    (d : GeneralSignalDisclosure Index Signal) (observed : SignalProfile Index Signal) :
    Integrable (wholeScoreDensity source B d observed) (generalDisclosureMeasure source d) :=
  (integrable_posteriorScore_density_iff
    (generalDisclosureWithWholeStateMeasure source B d observed) (generalDisclosureMeasure source d)
    (wholeStateMeasure_absolutelyContinuous source B d observed) source.score).mpr
      (generalDisclosureWithWholeScore_integrable source B d observed)

/-- Both pieces of the marginal value now use one report-law integral. -/
theorem generalDisclosureMarginal_density (B : Finset Index)
    (d : GeneralSignalDisclosure Index Signal) :
    generalDisclosureWithWholeValue source B d - generalDisclosureValue source d =
      ∫ output, (∑ observed, wholeScoreDensity source B d observed output) -
        source.score (generalDisclosurePosterior source d output)
          ∂generalDisclosureMeasure source d := by
  classical
  rw [integral_sub
    (integrable_finsetSum _ (fun observed _ => wholeScoreDensity_integrable source B d observed))
    (generalDisclosureScore_integrable source d)]
  rw [integral_finsetSum _ (fun observed _ => wholeScoreDensity_integrable source B d observed)]
  unfold generalDisclosureWithWholeValue generalDisclosureValue
  simp only [integral_wholeScoreDensity]
end Source

end
end EconCSLib.OpenProblem.New.EconCSBench.InformationalSubstitutesComplements.FiniteWitness

end


section

/-!
## Grouped posterior value identity

The functional H depends only on the prior's fixed conditional E,B table and G. It
receives the posterior of the allowed S-observation, not extra source signals.
-/
namespace EconCSLib.OpenProblem.New.EconCSBench.InformationalSubstitutesComplements.FiniteWitness
open EconCSLib.OpenProblem.New.EconCSBench.InformationalSubstitutesComplements
open MeasureTheory
open scoped BigOperators
noncomputable section

variable {State Index : Type*} {Signal : Index → Type*}
  [Fintype State] [Fintype Index] [DecidableEq Index]
  [∀ i, Fintype (Signal i)] [∀ i, DecidableEq (Signal i)] [∀ i, Nonempty (Signal i)]
  (source : FiniteBayesianInformation State Index Signal)

/-- Marginal-value functional of a posterior over the permitted S-observations. -/
def groupedMarginalFunctional (S B : Finset Index) (q : SignalProfile Index Signal → ℝ) : ℝ :=
  (∑ y, (∑ e, ∑ x, groupConditional source S B x e y * q x) *
    source.score (fun e => (∑ x, groupConditional source S B x e y * q x) /
      (∑ e', ∑ x, groupConditional source S B x e' y * q x))) -
    source.score (fun e => ∑ y, ∑ x, groupConditional source S B x e y * q x)

/-- The actual common-density integrand equals the fixed functional at q_S almost
everywhere. -/
theorem groupedMarginalFunctional_ae (S B : Finset Index)
    (d : GeneralSignalDisclosure Index Signal)
    (upper : IsGeneralBlackwellBelowOn source d (generalWholeSignalDisclosure S)) :
    (fun output => (∑ y, wholeScoreDensity source B d y output) -
      source.score (generalDisclosurePosterior source d output)) =ᵐ[generalDisclosureMeasure source d]
      (fun output => groupedMarginalFunctional source S B (groupPosterior source S d upper output)) := by
  have hjoint := ae_all_iff.mpr (fun e => ae_all_iff.mpr
    (fun y => wholeStateDensity_groupConditional source S B d upper e y))
  have hwhole := ae_all_iff.mpr (fun y => wholeProbabilityDensity_groupConditional source S B d upper y)
  have hstate := ae_all_iff.mpr (fun e => stateDensity_groupConditional source S B d upper e)
  filter_upwards [hjoint, hwhole, hstate] with output hjoint hwhole hstate
  have hpost : generalDisclosurePosterior source d output =
      (fun e => ∑ y, ∑ x, groupConditional source S B x e y *
        groupPosterior source S d upper output x) := by
    funext e
    exact hstate e
  unfold groupedMarginalFunctional
  rw [hpost]
  congr 1
  apply Finset.sum_congr rfl
  intro y _
  unfold wholeScoreDensity
  rw [hwhole y]
  congr 1
  apply congrArg source.score
  funext e
  rw [hjoint e y]

/-- The grouped functional is integrable without any new regularity premise on G. -/
theorem groupedMarginalFunctional_integrable (S B : Finset Index)
    (d : GeneralSignalDisclosure Index Signal)
    (upper : IsGeneralBlackwellBelowOn source d (generalWholeSignalDisclosure S)) :
    Integrable (fun output => groupedMarginalFunctional source S B
      (groupPosterior source S d upper output)) (generalDisclosureMeasure source d) :=
  ((integrable_finsetSum _ (fun y _ => wholeScoreDensity_integrable source B d y)).sub
    (generalDisclosureScore_integrable source d)).congr (groupedMarginalFunctional_ae source S B d upper)

/-- Exact source-level H(q_S) representation of the general-disclosure marginal value. -/
theorem generalDisclosureMarginal_grouped (S B : Finset Index)
    (d : GeneralSignalDisclosure Index Signal)
    (upper : IsGeneralBlackwellBelowOn source d (generalWholeSignalDisclosure S)) :
    generalDisclosureWithWholeValue source B d - generalDisclosureValue source d =
      ∫ output, groupedMarginalFunctional source S B (groupPosterior source S d upper output)
        ∂generalDisclosureMeasure source d := by
  rw [generalDisclosureMarginal_density]
  exact integral_congr_ae (groupedMarginalFunctional_ae source S B d upper)

end
end EconCSLib.OpenProblem.New.EconCSBench.InformationalSubstitutesComplements.FiniteWitness

end


section

/-!
## Whole-signal baseline for the grouped marginal functional
-/
namespace EconCSLib.OpenProblem.New.EconCSBench.InformationalSubstitutesComplements.FiniteWitness
open EconCSLib.OpenProblem.New.EconCSBench.InformationalSubstitutesComplements
open MeasureTheory Classical
open scoped BigOperators
noncomputable section

variable {State Index : Type*} {Signal : Index → Type*}
  [Fintype State] [Fintype Index] [DecidableEq Index]
  [∀ i, Fintype (Signal i)] [∀ i, DecidableEq (Signal i)] [∀ i, Nonempty (Signal i)]
  (source : FiniteBayesianInformation State Index Signal)

omit [∀ i, Fintype (Signal i)] [∀ i, DecidableEq (Signal i)] in
/-- Canonical masking has exactly the original SameOn equivalence classes. -/
theorem masked_eq_iff_sameOn (S : Finset Index) (a b : SignalProfile Index Signal) :
    maskedSignalProfile S b = maskedSignalProfile S a ↔ SameOn S a b := by
  constructor
  · intro h i hi
    have he := congrFun h i
    simpa only [maskedSignalProfile, hi, if_true] using he.symm
  · intro h
    funext i
    by_cases hi : i ∈ S
    · simp [maskedSignalProfile, hi, h i hi]
    · simp [maskedSignalProfile, hi]

theorem observationProbability_groupPrior (S : Finset Index) (input : SignalProfile Index Signal) :
    observationProbability source S input = groupPriorMass source S (maskedSignalProfile S input) := by
  classical
  unfold observationProbability groupPriorMass signalProfileProbability
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro other _
  simp only [masked_eq_iff_sameOn]
  by_cases h : SameOn S input other <;> simp [h]

theorem sum_groupJointMass_state (S B : Finset Index) (x : SignalProfile Index Signal) (e : State) :
    (∑ y, groupJointMass source S B x e y) =
      ∑ input, if maskedSignalProfile S input = x then source.jointPrior.val (e, input) else 0 := by
  classical
  unfold groupJointMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro input _
  split_ifs <;> simp

/-- The state marginal of R(E,B|S) is the original whole-S posterior. -/
theorem posterior_groupConditional (S B : Finset Index) (input : SignalProfile Index Signal) :
    posterior source S input =
      (fun e => ∑ y, groupConditional source S B (maskedSignalProfile S input) e y) := by
  classical
  funext e
  unfold posterior groupConditional
  rw [← Finset.sum_div, sum_groupJointMass_state, observationProbability_groupPrior]
  simp only [masked_eq_iff_sameOn]

/-- Finite pushforward expectation under the grouped S-prior. -/
theorem sum_groupPrior_mul (S : Finset Index) (f : SignalProfile Index Signal → ℝ) :
    (∑ x, groupPriorMass source S x * f x) =
      ∑ input, signalProfileProbability source input * f (maskedSignalProfile S input) := by
  classical
  unfold groupPriorMass
  simp_rw [Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  simp

/-- Exact grouped-prior expression for the original whole-S value. -/
theorem weakSignalValue_groupConditional (S B : Finset Index) :
    weakSignalValue source S =
      ∑ x, groupPriorMass source S x * source.score (fun e => ∑ y, groupConditional source S B x e y) := by
  rw [sum_groupPrior_mul]
  unfold weakSignalValue
  apply Finset.sum_congr rfl
  intro input _
  rw [posterior_groupConditional source S B input]

/-- Joint probability of the canonical S- and B-observations. -/
def groupPairMass (S B : Finset Index) (x y : SignalProfile Index Signal) : ℝ :=
  ∑ e, groupJointMass source S B x e y

theorem groupPairMass_eq (S B : Finset Index) (x y : SignalProfile Index Signal) :
    groupPairMass source S B x y =
      ∑ input, if (maskedSignalProfile S input, maskedSignalProfile B input) = (x, y)
        then signalProfileProbability source input else 0 := by
  classical
  unfold groupPairMass groupJointMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro input _
  by_cases hs : maskedSignalProfile S input = x <;>
    by_cases hb : maskedSignalProfile B input = y <;>
    simp [hs, hb, signalProfileProbability]

private theorem sum_fiber_weights {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y]
    (g : X → Y) (w : X → ℝ) (f : Y → ℝ) :
    (∑ y, (∑ x, if g x = y then w x else 0) * f y) = ∑ x, w x * f (g x) := by
  classical
  simp_rw [Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  simp

/-- Joint pushforward expectation for the original two whole observations. -/
theorem sum_groupPair_mul (S B : Finset Index)
    (f : SignalProfile Index Signal → SignalProfile Index Signal → ℝ) :
    (∑ x, ∑ y, groupPairMass source S B x y * f x y) =
      ∑ input, signalProfileProbability source input *
        f (maskedSignalProfile S input) (maskedSignalProfile B input) := by
  simp_rw [groupPairMass_eq]
  rw [← Fintype.sum_prod_type (fun pair : SignalProfile Index Signal × SignalProfile Index Signal =>
    (∑ input, if (maskedSignalProfile S input, maskedSignalProfile B input) = pair
      then signalProfileProbability source input else 0) * f pair.1 pair.2)]
  exact sum_fiber_weights (X := SignalProfile Index Signal)
    (Y := SignalProfile Index Signal × SignalProfile Index Signal)
    (fun input => (maskedSignalProfile S input, maskedSignalProfile B input))
    (signalProfileProbability source) (fun pair => f pair.1 pair.2)

omit [Fintype Index] [∀ i, Fintype (Signal i)] [∀ i, DecidableEq (Signal i)]
  [∀ i, Nonempty (Signal i)] in
theorem sameOn_union (S B : Finset Index) (a b : SignalProfile Index Signal) :
    SameOn (S ∪ B) a b ↔ SameOn S a b ∧ SameOn B a b := by
  constructor
  · intro h
    exact ⟨fun i hi => h i (Finset.mem_union_left _ hi), fun i hi => h i (Finset.mem_union_right _ hi)⟩
  · rintro ⟨hs, hb⟩ i hi
    exact (Finset.mem_union.mp hi).elim (hs i) (hb i)

theorem groupJointMass_at_observations (S B : Finset Index) (input : SignalProfile Index Signal)
    (e : State) :
    groupJointMass source S B (maskedSignalProfile S input) e (maskedSignalProfile B input) =
      ∑ other, if SameOn (S ∪ B) input other then source.jointPrior.val (e, other) else 0 := by
  classical
  simp only [groupJointMass, masked_eq_iff_sameOn, sameOn_union, ite_and]

theorem groupPairMass_at_observations (S B : Finset Index) (input : SignalProfile Index Signal) :
    groupPairMass source S B (maskedSignalProfile S input) (maskedSignalProfile B input) =
      observationProbability source (S ∪ B) input := by
  simp only [groupPairMass, groupJointMass_at_observations, observationProbability]

/-- Full S∪B value is the expected score of the grouped joint posterior. -/
theorem weakSignalValue_union_groupJoint (S B : Finset Index) :
    weakSignalValue source (S ∪ B) =
      ∑ x, ∑ y, groupPairMass source S B x y *
        source.score (fun e => groupJointMass source S B x e y / groupPairMass source S B x y) := by
  rw [sum_groupPair_mul]
  unfold weakSignalValue
  apply Finset.sum_congr rfl
  intro input _
  unfold posterior
  simp only [groupJointMass_at_observations, groupPairMass_at_observations]

/-- Multiplying the conditional score by the S-mass restores its actual joint weight. -/
theorem weighted_groupConditional_score (S B : Finset Index)
    (x y : SignalProfile Index Signal) :
    groupPriorMass source S x * ((∑ e, groupConditional source S B x e y) *
      source.score (fun e => groupConditional source S B x e y /
        (∑ e', groupConditional source S B x e' y))) =
      groupPairMass source S B x y *
        source.score (fun e => groupJointMass source S B x e y / groupPairMass source S B x y) := by
  by_cases hz : groupPriorMass source S x = 0
  · have hj : ∀ e, groupJointMass source S B x e y = 0 := by
      intro e
      apply le_antisymm
      · simpa only [hz] using groupJointMass_le_prior source S B x e y
      · exact groupJointMass_nonnegative source S B x e y
    simp [hz, groupPairMass, hj]
  · have hsum : (∑ e, groupConditional source S B x e y) =
        groupPairMass source S B x y / groupPriorMass source S x := by
      simp only [groupConditional, groupPairMass, Finset.sum_div]
    have hpost : (fun e => groupConditional source S B x e y /
        (∑ e', groupConditional source S B x e' y)) =
        (fun e => groupJointMass source S B x e y / groupPairMass source S B x y) := by
      funext e
      rw [hsum]
      exact div_div_div_cancel_right₀ hz _ _
    rw [hpost, hsum, ← mul_assoc, ← mul_div_assoc, mul_div_cancel_left₀ _ hz]

theorem groupedMarginalFunctional_pure (S B : Finset Index) (x : SignalProfile Index Signal) :
    groupedMarginalFunctional source S B (Lottery.pure (𝕜 := ℝ) x).val =
      (∑ y, (∑ e, groupConditional source S B x e y) *
        source.score (fun e => groupConditional source S B x e y /
          (∑ e', groupConditional source S B x e' y))) -
        source.score (fun e => ∑ y, groupConditional source S B x e y) := by
  classical
  simp [groupedMarginalFunctional, stdSimplex.pure]

/-- The full-S marginal in the original open problem is exactly the grouped revelation
baseline. -/
theorem weakSignalMarginal_grouped_baseline (S B : Finset Index) :
    weakSignalValue source (S ∪ B) - weakSignalValue source S =
      ∑ x, groupPriorMass source S x *
        groupedMarginalFunctional source S B (Lottery.pure (𝕜 := ℝ) x).val := by
  symm
  simp_rw [groupedMarginalFunctional_pure, mul_sub, Finset.mul_sum]
  rw [Finset.sum_sub_distrib]
  simp_rw [weighted_groupConditional_score]
  rw [← weakSignalValue_union_groupJoint, ← weakSignalValue_groupConditional source S B]

end
end EconCSLib.OpenProblem.New.EconCSBench.InformationalSubstitutesComplements.FiniteWitness

end


section

/-!
## Posterior fibers forced by Markov recovery

The conclusion follows from an actual stochastic recovery kernel, without assuming a
deterministic report decoder or finite report space.
-/
namespace EconCSLib.OpenProblem.New.EconCSBench.InformationalSubstitutesComplements.FiniteWitness
open EconCSLib.OpenProblem.New.EconCSBench.InformationalSubstitutesComplements
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
noncomputable section

variable {X Z C : Type*} [Fintype X] [MeasurableSpace Z] [MeasurableSpace C]
  [MeasurableSingletonClass C]

omit [MeasurableSingletonClass C] in
/-- A Markov recovery witness puts each nonzero posterior component in one fiber. -/
theorem posterior_single_fiber_of_recovery
    (μ : X → Measure Z) [∀ x, IsFiniteMeasure (μ x)]
    (κ : Kernel Z C) [IsMarkovKernel κ] (f : X → C)
    (recovery : ∀ x, ∀ᵐ c ∂(κ ∘ₘ μ x), c = f x) :
    ∀ᵐ z ∂(∑ x, μ x), ∃ c : C, ∀ x,
      0 < ((μ x).rnDeriv (∑ x, μ x) z).toReal → f x = c := by
  have component : ∀ x, ∀ᵐ z ∂(∑ x, μ x),
      (μ x).rnDeriv (∑ x, μ x) z ≠ 0 → ∀ᵐ c ∂κ z, c = f x :=
    fun x => Measure.ae_rnDeriv_ne_zero_imp_of_ae (∑ x, μ x)
      (Measure.ae_ae_of_ae_comp (recovery x))
  filter_upwards [ae_all_iff.mpr component, rnPosterior_isProbabilityVector_ae μ] with z hz hprob
  obtain ⟨x, hx⟩ : ∃ x, 0 < ((μ x).rnDeriv (∑ x, μ x) z).toReal := by
    by_contra hn
    push Not at hn
    have hall : ∀ x, ((μ x).rnDeriv (∑ x, μ x) z).toReal = 0 :=
      fun x => le_antisymm (hn x) (hprob.1 x)
    have hsum := hprob.2
    simp only [hall, Finset.sum_const_zero] at hsum
    norm_num at hsum
  refine ⟨f x, fun y hy => ?_⟩
  have hx' : (μ x).rnDeriv (∑ x, μ x) z ≠ 0 := by
    intro hn
    simp only [hn, ENNReal.toReal_zero, lt_self_iff_false] at hx
  have hy' : (μ y).rnDeriv (∑ x, μ x) z ≠ 0 := by
    intro hn
    simp only [hn, ENNReal.toReal_zero, lt_self_iff_false] at hy
  obtain ⟨c, hcy, hcx⟩ := ((hz y hy').and (hz x hx')).exists
  exact hcy.symm.trans hcx

/-- A scaled Dirac composition supplies the actual recovery premise. -/
theorem posterior_single_fiber_of_comp_eq_dirac
    (μ : X → Measure Z) [∀ x, IsFiniteMeasure (μ x)]
    (κ : Kernel Z C) [IsMarkovKernel κ] (f : X → C)
    (weight : X → ℝ≥0∞)
    (recovery : ∀ x, κ ∘ₘ μ x = weight x • Measure.dirac (f x)) :
    ∀ᵐ z ∂(∑ x, μ x), ∃ c : C, ∀ x,
      0 < ((μ x).rnDeriv (∑ x, μ x) z).toReal → f x = c := by
  apply posterior_single_fiber_of_recovery μ κ f
  intro x
  rw [recovery x]
  exact Measure.ae_smul_measure (by simp) (weight x)

end
end EconCSLib.OpenProblem.New.EconCSBench.InformationalSubstitutesComplements.FiniteWitness

end


section

/-!
## Recovery of the grouped posterior

The coarse C-observation is a subset of the allowed S-observation. The actual
upper/lower Blackwell witnesses are used; no deterministic decoder is assumed.
-/
namespace EconCSLib.OpenProblem.New.EconCSBench.InformationalSubstitutesComplements.FiniteWitness
open EconCSLib.OpenProblem.New.EconCSBench.InformationalSubstitutesComplements
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
noncomputable section

variable {State Index : Type*} {Signal : Index → Type*}
  [Fintype State] [Fintype Index] [DecidableEq Index]
  [∀ i, Fintype (Signal i)] [∀ i, DecidableEq (Signal i)] [∀ i, Nonempty (Signal i)]
  (source : FiniteBayesianInformation State Index Signal)

/-- Every positive grouped label has a positive-prior source realization. -/
theorem exists_supported_input_of_group_positive (S : Finset Index)
    (x : SignalProfile Index Signal) (positive : 0 < groupPriorMass source S x) :
    ∃ input, 0 < signalProfileProbability source input ∧ maskedSignalProfile S input = x := by
  classical
  have hn : ∀ input ∈ (Finset.univ : Finset (SignalProfile Index Signal)),
      0 ≤ if maskedSignalProfile S input = x then signalProfileProbability source input else 0 := by
    intro input _
    split_ifs
    · exact signalProfileProbability_nonnegative source input
    · exact le_rfl
  obtain ⟨input, _, hinput⟩ := (Finset.sum_pos_iff_of_nonneg hn).mp positive
  by_cases hx : maskedSignalProfile S input = x
  · exact ⟨input, by simpa only [hx, if_true] using hinput, hx⟩
  · simp only [hx, if_false, lt_self_iff_false] at hinput

omit [∀ i, Fintype (Signal i)] [∀ i, DecidableEq (Signal i)] in
/-- Masking by a subset after S is the same as masking the original source. -/
theorem maskedSignalProfile_subset_comp (C S : Finset Index) (subset : C ⊆ S)
    (input : SignalProfile Index Signal) :
    maskedSignalProfile C (maskedSignalProfile S input) = maskedSignalProfile C input := by
  funext i
  by_cases hi : i ∈ C
  · simp [maskedSignalProfile, hi, subset hi]
  · simp [maskedSignalProfile, hi]

/-- The grouped posterior is supported in one recovered C-fiber almost everywhere. -/
theorem groupPosterior_recovers_whole (C S : Finset Index) (subset : C ⊆ S)
    (d : GeneralSignalDisclosure Index Signal)
    (upper : IsGeneralBlackwellBelowOn source d (generalWholeSignalDisclosure S))
    (lower : IsGeneralBlackwellBelowOn source (generalWholeSignalDisclosure C) d) :
    ∀ᵐ output ∂generalDisclosureMeasure source d,
      ∃ observed : SignalProfile Index Signal, ∀ x,
        0 < groupPosterior source S d upper output x → maskedSignalProfile C x = observed := by
  classical
  letI : MeasurableSpace (SignalProfile Index Signal) := ⊤
  rcases lower with ⟨κ, hκ, h⟩
  letI := hκ
  letI : MeasurableSingletonClass (generalWholeSignalDisclosure (Signal := Signal) C).Output := by
    change @MeasurableSingletonClass (SignalProfile Index Signal) ⊤
    infer_instance
  have recovered : ∀ x,
      κ ∘ₘ groupReportMeasure source S d upper x =
        ENNReal.ofReal (groupPriorMass source S x) • Measure.dirac (maskedSignalProfile C x) := by
    intro x
    by_cases hx : 0 < groupPriorMass source S x
    · obtain ⟨input, hi, hix⟩ := exists_supported_input_of_group_positive source S x hx
      have hrow : wholeFactorKernel source S d upper x = d.kernel input := by
        rw [← hix]
        exact (kernel_eq_wholeFactorKernel source S d upper input hi).symm
      have hc : κ ∘ₘ d.kernel input = Measure.dirac (maskedSignalProfile C input) :=
        (h input hi).symm
      rw [groupReportMeasure, Measure.comp_smul, hrow, hc]
      rw [← hix, maskedSignalProfile_subset_comp C S subset input]
      rfl
    · have hz : ENNReal.ofReal (groupPriorMass source S x) = 0 :=
        ENNReal.ofReal_eq_zero.mpr (le_of_not_gt hx)
      simp [groupReportMeasure, hz]
      rfl
  have hfiber := posterior_single_fiber_of_comp_eq_dirac (groupReportMeasure source S d upper)
    κ (maskedSignalProfile C) (fun x => ENNReal.ofReal (groupPriorMass source S x)) recovered
  simpa only [sum_groupReportMeasure, groupPosterior] using hfiber

end
end EconCSLib.OpenProblem.New.EconCSBench.InformationalSubstitutesComplements.FiniteWitness

end


section

/-!
## Selecting a posterior with a strict violation

The real parameter `sign` handles either substitutes or complements. The witness is
mathematical data.
-/
namespace EconCSLib.OpenProblem.New.EconCSBench.InformationalSubstitutesComplements.FiniteWitness
open EconCSLib.OpenProblem.New.EconCSBench.InformationalSubstitutesComplements
open MeasureTheory
open scoped BigOperators
noncomputable section

variable {State Index : Type*} {Signal : Index → Type*}
  [Fintype State] [Fintype Index] [DecidableEq Index]
  [∀ i, Fintype (Signal i)] [∀ i, DecidableEq (Signal i)] [∀ i, Nonempty (Signal i)]
  (source : FiniteBayesianInformation State Index Signal)

/-- Deviation of H(q) from the revealing split associated with q. -/
def groupedDeficit (S B : Finset Index) (q : SignalProfile Index Signal → ℝ) : ℝ :=
  groupedMarginalFunctional source S B q -
    ∑ x, q x * groupedMarginalFunctional source S B (Lottery.pure (𝕜 := ℝ) x).val

/-- Integrating the posterior deficit gives the actual original marginal-value gap. -/
theorem integral_groupedDeficit (S B : Finset Index)
    (d : GeneralSignalDisclosure Index Signal)
    (upper : IsGeneralBlackwellBelowOn source d (generalWholeSignalDisclosure S)) :
    (∫ output, groupedDeficit source S B (groupPosterior source S d upper output)
      ∂generalDisclosureMeasure source d) =
      (generalDisclosureWithWholeValue source B d - generalDisclosureValue source d) -
        (weakSignalValue source (S ∪ B) - weakSignalValue source S) := by
  classical
  have hcoord (x : SignalProfile Index Signal) :
      Integrable (fun output => groupPosterior source S d upper output x)
        (generalDisclosureMeasure source d) := Measure.integrable_toReal_rnDeriv
  have hlinear : Integrable (fun output => ∑ x, groupPosterior source S d upper output x *
      groupedMarginalFunctional source S B (Lottery.pure (𝕜 := ℝ) x).val)
      (generalDisclosureMeasure source d) :=
    integrable_finsetSum _ (fun x _ => (hcoord x).mul_const _)
  unfold groupedDeficit
  rw [integral_sub (groupedMarginalFunctional_integrable source S B d upper) hlinear]
  rw [integral_finsetSum _ (fun x _ => (hcoord x).mul_const _)]
  simp_rw [integral_mul_const, integral_groupPosterior]
  rw [← generalDisclosureMarginal_grouped source S B d upper,
    ← weakSignalMarginal_grouped_baseline source S B]

/-- Every actual signed strong violation supplies one supported, recoverable strict q_S. -/
theorem exists_strict_grouped_posterior (S B : Finset Index)
    (d : GeneralSignalDisclosure Index Signal)
    (upper : IsGeneralBlackwellBelowOn source d (generalWholeSignalDisclosure S))
    (lower : IsGeneralBlackwellBelowOn source (generalWholeSignalDisclosure (S ∩ B)) d)
    (sign : ℝ)
    (strict : sign * ((generalDisclosureWithWholeValue source B d - generalDisclosureValue source d) -
      (weakSignalValue source (S ∪ B) - weakSignalValue source S)) < 0) :
    ∃ q : Lottery ℝ (SignalProfile Index Signal),
      (∀ x, groupPriorMass source S x = 0 → q.val x = 0) ∧
      (∃ c : SignalProfile Index Signal, ∀ x, 0 < q.val x → maskedSignalProfile (S ∩ B) x = c) ∧
      sign * groupedDeficit source S B q.val < 0 := by
  have hintegral : (∫ output, sign * groupedDeficit source S B
      (groupPosterior source S d upper output) ∂generalDisclosureMeasure source d) < 0 := by
    rw [integral_const_mul, integral_groupedDeficit]
    exact strict
  have good : ∀ᵐ output ∂generalDisclosureMeasure source d,
      IsProbabilityVector (groupPosterior source S d upper output) ∧
      (∀ x, groupPriorMass source S x = 0 → groupPosterior source S d upper output x = 0) ∧
      (∃ c : SignalProfile Index Signal, ∀ x,
        0 < groupPosterior source S d upper output x → maskedSignalProfile (S ∩ B) x = c) := by
    filter_upwards [groupPosterior_isProbabilityVector_ae source S d upper,
      groupPosterior_supported_ae source S d upper,
      groupPosterior_recovers_whole source (S ∩ B) S Finset.inter_subset_left d upper lower]
      with output hp hs hf using ⟨hp, hs, hf⟩
  obtain ⟨output, hg, hstrict⟩ : ∃ output,
      (IsProbabilityVector (groupPosterior source S d upper output) ∧
        (∀ x, groupPriorMass source S x = 0 → groupPosterior source S d upper output x = 0) ∧
        (∃ c : SignalProfile Index Signal, ∀ x,
          0 < groupPosterior source S d upper output x → maskedSignalProfile (S ∩ B) x = c)) ∧
      sign * groupedDeficit source S B (groupPosterior source S d upper output) < 0 := by
    by_contra hn
    have nonnegative : ∀ᵐ output ∂generalDisclosureMeasure source d,
        0 ≤ sign * groupedDeficit source S B (groupPosterior source S d upper output) := by
      filter_upwards [good] with output hg
      exact le_of_not_gt (fun hlt => hn ⟨output, hg, hlt⟩)
    exact (not_lt_of_ge (integral_nonneg_of_ae nonnegative)) hintegral
  exact ⟨⟨groupPosterior source S d upper output, hg.1⟩, hg.2.1, hg.2.2, hstrict⟩

end
end EconCSLib.OpenProblem.New.EconCSBench.InformationalSubstitutesComplements.FiniteWitness

end


section

/-!
## Finite splitting lemma

This section proves the finite construction from one supported posterior.
-/
namespace EconCSLib.OpenProblem.New.EconCSBench.InformationalSubstitutesComplements.FiniteWitness
open EconCSLib.OpenProblem.New.EconCSBench.InformationalSubstitutesComplements
open scoped BigOperators
noncomputable section

variable {X : Type*} [Fintype X]

/-- Any posterior supported by the prior can be assigned a positive report mass. -/
theorem exists_positive_split_scale (π q : Lottery ℝ X)
    (support : ∀ x, π.val x = 0 → q.val x = 0) :
    ∃ t : ℝ, 0 < t ∧ ∀ x, t * q.val x ≤ π.val x := by
  classical
  let s : Finset X := Finset.univ.filter (fun x => 0 < π.val x)
  have hs : s.Nonempty := by
    by_contra h
    have hz : ∀ x, π.val x = 0 := by
      intro x
      have : ¬ 0 < π.val x := by
        intro hx
        exact h ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩⟩
      exact le_antisymm (le_of_not_gt this) (π.property.1 x)
    have : (∑ x, π.val x) = 0 := by simp [hz]
    linarith [π.property.2]
  let t := s.inf' hs π.val
  have ht : 0 < t := (Finset.lt_inf'_iff hs).mpr fun x hx =>
    (Finset.mem_filter.mp hx).2
  refine ⟨t, ht, fun x => ?_⟩
  by_cases hx : π.val x = 0
  · simp [hx, support x hx]
  · have hpos : 0 < π.val x := lt_of_le_of_ne (π.property.1 x) (Ne.symm hx)
    calc
      t * q.val x ≤ t * 1 := mul_le_mul_of_nonneg_left (stdSimplex.le_one q x) ht.le
      _ ≤ π.val x := by
        simpa only [mul_one] using Finset.inf'_le π.val
          (Finset.mem_filter.mpr ⟨Finset.mem_univ x, hpos⟩ : x ∈ s)

/-- Chosen scale and domination needed by the actual stochastic rows. -/
structure SplitData (π q : Lottery ℝ X) where
  mass : ℝ
  positive : 0 < mass
  dominated : ∀ x, mass * q.val x ≤ π.val x

/-- Existence uses real probabilities and imposes no rationality premise. -/
theorem nonempty_splitData (π q : Lottery ℝ X)
    (support : ∀ x, π.val x = 0 → q.val x = 0) : Nonempty (SplitData π q) := by
  obtain ⟨t, ht, hdom⟩ := exists_positive_split_scale π q support
  exact ⟨⟨t, ht, hdom⟩⟩

variable {π q : Lottery ℝ X} (s : SplitData π q)

include s in
/-- Null prior coordinates are necessarily null in the selected posterior. -/
theorem SplitData.support (x : X) (hx : π.val x = 0) : q.val x = 0 := by
  have hdom := s.dominated x
  rw [hx] at hdom
  have hz : s.mass * q.val x = 0 :=
    le_antisymm hdom (mul_nonneg s.positive.le (q.property.1 x))
  exact (mul_eq_zero.mp hz).resolve_left s.positive.ne'

/-- Probability of emitting the special report; division by zero gives zero. -/
def SplitData.rate (x : X) : ℝ := s.mass * q.val x / π.val x

theorem SplitData.rate_nonneg (x : X) : 0 ≤ s.rate x :=
  div_nonneg (mul_nonneg s.positive.le (q.property.1 x)) (π.property.1 x)

theorem SplitData.rate_le_one (x : X) : s.rate x ≤ 1 := by
  by_cases hx : π.val x = 0
  · simp [SplitData.rate, hx]
  · exact (div_le_one (lt_of_le_of_ne (π.property.1 x) (Ne.symm hx))).mpr (s.dominated x)

variable [DecidableEq X]

/-- Either disclose the selected posterior or reveal the source value exactly. -/
def SplitData.kernel (x : X) : Lottery ℝ (Option X) :=
  Lottery.mix (s.rate x) (s.rate_nonneg x) (s.rate_le_one x)
    (Lottery.pure none) (Lottery.pure (some x))

theorem SplitData.kernel_none (x : X) : (s.kernel x).val none = s.rate x := by
  simp [SplitData.kernel, stdSimplex.pure]

theorem SplitData.kernel_some (x y : X) :
    (s.kernel x).val (some y) = if y = x then 1 - s.rate x else 0 := by
  simp [SplitData.kernel, stdSimplex.pure]

omit [DecidableEq X] in
theorem SplitData.prior_mul_rate (x : X) : π.val x * s.rate x = s.mass * q.val x := by
  by_cases hx : π.val x = 0
  · simp [hx, s.support x hx]
  · dsimp [SplitData.rate]
    field_simp

/-- The actual marginal report probability of the constructed finite channel. -/
def SplitData.reportMass (y : Option X) : ℝ := ∑ x, π.val x * (s.kernel x).val y

/-- The actual Bayes posterior, with the standard zero-division null convention. -/
def SplitData.posterior (y : Option X) (x : X) : ℝ :=
  π.val x * (s.kernel x).val y / s.reportMass y

theorem SplitData.joint_none (x : X) :
    π.val x * (s.kernel x).val none = s.mass * q.val x := by
  rw [s.kernel_none, s.prior_mul_rate]

theorem SplitData.joint_some (x y : X) :
    π.val x * (s.kernel x).val (some y) =
      if y = x then π.val x - s.mass * q.val x else 0 := by
  rw [s.kernel_some]
  split_ifs
  · rw [mul_sub, mul_one, s.prior_mul_rate]
  · simp

theorem SplitData.reportMass_none : s.reportMass none = s.mass := by
  simp only [SplitData.reportMass, s.joint_none, ← Finset.mul_sum, q.property.2, mul_one]

theorem SplitData.reportMass_some (x : X) :
    s.reportMass (some x) = π.val x - s.mass * q.val x := by
  simp [SplitData.reportMass, s.joint_some]

theorem SplitData.posterior_none : s.posterior none = q.val := by
  funext x
  simp only [SplitData.posterior, s.joint_none, s.reportMass_none]
  exact mul_div_cancel_left₀ _ s.positive.ne'

theorem SplitData.posterior_some (x : X) (hx : 0 < s.reportMass (some x)) :
    s.posterior (some x) = (Lottery.pure (𝕜 := ℝ) x).val := by
  funext z
  have hn : π.val x - s.mass * q.val x ≠ 0 := by
    rw [s.reportMass_some] at hx
    exact hx.ne'
  simp only [SplitData.posterior, s.joint_some, s.reportMass_some]
  by_cases h : x = z
  · subst z
    simp [stdSimplex.pure, hn]
  · simp [stdSimplex.pure, h, Ne.symm h]

/-- Expected functional of the constructed channel's true Bayes posterior. -/
def SplitData.value (H : (X → ℝ) → ℝ) : ℝ :=
  ∑ y, s.reportMass y * H (s.posterior y)

/-- Exact value, valid for arbitrary H; null reports contribute zero. -/
theorem SplitData.value_eq (H : (X → ℝ) → ℝ) :
    s.value H = s.mass * H q.val +
      ∑ x, (π.val x - s.mass * q.val x) * H (Lottery.pure (𝕜 := ℝ) x).val := by
  rw [SplitData.value, Fintype.sum_option, s.reportMass_none, s.posterior_none]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : s.reportMass (some x) = 0
  · simp only [hx, ← s.reportMass_some, zero_mul]
  · have hp : 0 < s.reportMass (some x) := by
      rw [s.reportMass_some] at hx ⊢
      exact lt_of_le_of_ne (sub_nonneg.mpr (s.dominated x)) (Ne.symm hx)
    rw [s.posterior_some x hp, s.reportMass_some]

/-- One posterior's deviation from full revelation, weighted by its report mass. -/
theorem SplitData.value_deficit (H : (X → ℝ) → ℝ) :
    s.value H - ∑ x, π.val x * H (Lottery.pure (𝕜 := ℝ) x).val =
      s.mass * (H q.val - ∑ x, q.val x * H (Lottery.pure (𝕜 := ℝ) x).val) := by
  rw [s.value_eq]
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib]
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]
  ring

/-- At most one new positive report beyond the prior's positive source values. -/
theorem SplitData.positive_report_count_le :
    (Finset.univ.filter (fun y => 0 < s.reportMass y)).card ≤
      (Finset.univ.filter (fun x => 0 < π.val x)).card + 1 := by
  rw [← Finset.card_insertNone]
  apply Finset.card_le_card
  intro y hy
  cases y with
  | none => exact Finset.none_mem_insertNone
  | some x =>
      apply Finset.some_mem_insertNone.mpr
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ x, ?_⟩
      have hp := (Finset.mem_filter.mp hy).2
      rw [s.reportMass_some] at hp
      have hq := mul_nonneg s.positive.le (q.property.1 x)
      linarith

/-- Recover a coarse observation from the split report. -/
def recover {C : Type*} (f : X → C) (c : C) : Option X → C
  | none => c
  | some x => f x

/-- A selected posterior supported in one coarse fiber preserves exact recovery. This is
an actual stochastic-composition equality, including null prior rows. -/
theorem SplitData.recovers {C : Type*} [Fintype C] [DecidableEq C]
    (f : X → C) (c : C) (fiber : ∀ x, 0 < q.val x → f x = c)
    (x : X) (observed : C) :
    (∑ y, (s.kernel x).val y *
      (Lottery.pure (𝕜 := ℝ) (recover f c y)).val observed) =
      (Lottery.pure (𝕜 := ℝ) (f x)).val observed := by
  simp only [Fintype.sum_option, s.kernel_none, s.kernel_some, recover]
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  by_cases hfc : f x = c
  · rw [hfc]
    ring
  · have hq : q.val x = 0 := by
      by_contra hq
      exact hfc (fiber x (lt_of_le_of_ne (q.property.1 x) (Ne.symm hq)))
    simp [SplitData.rate, hq]

/-- The chosen strict inequality survives compression in the substitutes direction. -/
theorem SplitData.value_lt_full (H : (X → ℝ) → ℝ)
    (strict : H q.val < ∑ x, q.val x * H (Lottery.pure (𝕜 := ℝ) x).val) :
    s.value H < ∑ x, π.val x * H (Lottery.pure (𝕜 := ℝ) x).val := by
  have h := mul_neg_of_pos_of_neg s.positive (sub_neg.mpr strict)
  rw [← s.value_deficit H] at h
  exact sub_neg.mp h

/-- The same construction preserves the reversed strict inequality for complements. -/
theorem SplitData.full_lt_value (H : (X → ℝ) → ℝ)
    (strict : (∑ x, q.val x * H (Lottery.pure (𝕜 := ℝ) x).val) < H q.val) :
    (∑ x, π.val x * H (Lottery.pure (𝕜 := ℝ) x).val) < s.value H := by
  have h := mul_pos s.positive (sub_pos.mpr strict)
  rw [← s.value_deficit H] at h
  exact sub_pos.mp h


end
end EconCSLib.OpenProblem.New.EconCSBench.InformationalSubstitutesComplements.FiniteWitness

end


section

/-!
## Constructing a finite disclosure from the grouped posterior

Residual reports reveal only the allowed S-observation. The construction uses real
coefficients; no rationality, bit-size, or effective extraction claim follows.
-/
namespace EconCSLib.OpenProblem.New.EconCSBench.InformationalSubstitutesComplements.FiniteWitness
open EconCSLib.OpenProblem.New.EconCSBench.InformationalSubstitutesComplements
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
noncomputable section

variable {State Index : Type*} {Signal : Index → Type*}
  [Fintype State] [Fintype Index] [DecidableEq Index]
  [∀ i, Fintype (Signal i)] [∀ i, DecidableEq (Signal i)] [∀ i, Nonempty (Signal i)]
  (source : FiniteBayesianInformation State Index Signal)

local instance : MeasurableSpace (Option (SignalProfile Index Signal)) := ⊤

local instance : MeasurableSingletonClass (Option (SignalProfile Index Signal)) := by
  change @MeasurableSingletonClass (Option (SignalProfile Index Signal)) ⊤
  infer_instance

/-- Feed only the permitted S-observation into the finite splitting channel. -/
def splitDisclosure (S : Finset Index) {q : Lottery ℝ (SignalProfile Index Signal)}
    (s : SplitData (groupPrior source S) q) : SignalDisclosure Index Signal where
  Output := Option (SignalProfile Index Signal)
  kernel := fun input => s.kernel (maskedSignalProfile S input)

/-- The finite disclosure has an explicit upper Blackwell witness. -/
theorem splitDisclosure_below_whole (S : Finset Index) {q : Lottery ℝ (SignalProfile Index Signal)}
    (s : SplitData (groupPrior source S) q) :
    IsBlackwellBelowOn source (splitDisclosure source S s) (wholeSignalDisclosure S) := by
  refine ⟨s.kernel, fun input _ output => ?_⟩
  change (s.kernel (maskedSignalProfile S input)).val output =
    ∑ middle, (Lottery.pure (𝕜 := ℝ) (maskedSignalProfile S input)).val middle * (s.kernel middle).val output
  simp [stdSimplex.pure]

/-- Recover the coarse observation without learning source signals outside S. -/
theorem whole_below_splitDisclosure (C S : Finset Index) (subset : C ⊆ S)
    {q : Lottery ℝ (SignalProfile Index Signal)} (s : SplitData (groupPrior source S) q)
    (c : SignalProfile Index Signal)
    (fiber : ∀ x, 0 < q.val x → maskedSignalProfile C x = c) :
    IsBlackwellBelowOn source (wholeSignalDisclosure C) (splitDisclosure source S s) := by
  refine ⟨fun output => Lottery.pure (recover (maskedSignalProfile C) c output), fun input _ observed => ?_⟩
  have h := s.recovers (maskedSignalProfile C) c fiber (maskedSignalProfile S input) observed
  rw [maskedSignalProfile_subset_comp C S subset] at h
  exact h.symm

/-- The embedded disclosure has the required original general-model upper witness. -/
theorem splitDisclosure_general_below_whole (S : Finset Index)
    {q : Lottery ℝ (SignalProfile Index Signal)} (s : SplitData (groupPrior source S) q) :
    IsGeneralBlackwellBelowOn source (splitDisclosure source S s).toGeneral (generalWholeSignalDisclosure S) := by
  have h := (splitDisclosure_below_whole source S s).toGeneral
  simpa only [wholeSignalDisclosure_toGeneral] using h

/-- Grouped component laws of the actual finite disclosure are exactly its split-channel
laws. -/
theorem splitDisclosure_groupReportMeasure (S : Finset Index)
    {q : Lottery ℝ (SignalProfile Index Signal)} (s : SplitData (groupPrior source S) q)
    (upper : IsGeneralBlackwellBelowOn source (splitDisclosure source S s).toGeneral
      (generalWholeSignalDisclosure S)) (x : SignalProfile Index Signal) :
    groupReportMeasure source S (splitDisclosure source S s).toGeneral upper x =
      ENNReal.ofReal (groupPriorMass source S x) • lotteryMeasure (s.kernel x) := by
  by_cases hx : 0 < groupPriorMass source S x
  · obtain ⟨input, hi, hix⟩ := exists_supported_input_of_group_positive source S x hx
    have hrow : wholeFactorKernel source S (splitDisclosure source S s).toGeneral upper x =
        lotteryMeasure (s.kernel x) := by
      rw [← hix]
      exact (kernel_eq_wholeFactorKernel source S (splitDisclosure source S s).toGeneral upper input hi).symm
    rw [groupReportMeasure, hrow]
    rfl
  · have hz : ENNReal.ofReal (groupPriorMass source S x) = 0 :=
      ENNReal.ofReal_eq_zero.mpr (le_of_not_gt hx)
    simp [groupReportMeasure, hz]
    rfl

/-- Original finite-disclosure marginal value equals the split expectation of H. -/
theorem splitDisclosure_marginal_value (S B : Finset Index)
    {q : Lottery ℝ (SignalProfile Index Signal)} (s : SplitData (groupPrior source S) q) :
    disclosureWithWholeValue source B (splitDisclosure source S s) -
      disclosureValue source (splitDisclosure source S s) =
      s.value (groupedMarginalFunctional source S B) := by
  classical
  let d := (splitDisclosure source S s).toGeneral
  have upper := splitDisclosure_general_below_whole source S s
  let μ := groupReportMeasure source S d upper
  letI : ∀ x, IsFiniteMeasure (groupReportMeasure source S d upper x) :=
    fun x => groupReportMeasure_isFinite source S d upper x
  letI : ∀ x, IsFiniteMeasure (μ x) :=
    fun x => groupReportMeasure_isFinite source S d upper x
  letI : Fintype d.Output := show Fintype (Option (SignalProfile Index Signal)) from inferInstance
  letI : MeasurableSingletonClass d.Output := by
    change @MeasurableSingletonClass (Option (SignalProfile Index Signal)) ⊤
    infer_instance
  have atom (x : SignalProfile Index Signal) (output : d.Output) :
      (μ x {output}).toReal = (groupPrior source S).val x * (s.kernel x).val output := by
    dsimp [μ, d]
    rw [splitDisclosure_groupReportMeasure]
    change (ENNReal.ofReal (groupPriorMass source S x) *
      (lotteryMeasure (s.kernel x) {show Option (SignalProfile Index Signal) from output})).toReal = _
    rw [lotteryMeasure_singleton (s.kernel x) output]
    simp only [ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (groupPriorMass_nonnegative source S x),
      ENNReal.toReal_ofReal ((s.kernel x).property.1 output)]
    rfl
  have mass (output : d.Output) : ((∑ x, μ x) {output}).toReal = s.reportMass output := by
    rw [Measure.finsetSum_apply, ENNReal.toReal_sum (fun x _ => measure_ne_top (μ x) {output})]
    simp only [atom, SplitData.reportMass]
  rw [← generalDisclosureWithWholeValue_toGeneral source B (splitDisclosure source S s),
    ← generalDisclosureValue_toGeneral source (splitDisclosure source S s)]
  rw [generalDisclosureMarginal_grouped source S B d upper]
  unfold groupPosterior
  rw [← sum_groupReportMeasure source S d upper]
  rw [finite_posterior_integral]
  change (∑ output : d.Output, ((∑ x, μ x) {output}).toReal *
    groupedMarginalFunctional source S B (fun x => (μ x {output}).toReal /
      ((∑ x, μ x) {output}).toReal)) = _
  simp only [mass, atom]
  rfl

/-- Actual report probabilities agree with the abstract splitting channel. -/
theorem splitDisclosure_probability (S : Finset Index)
    {q : Lottery ℝ (SignalProfile Index Signal)} (s : SplitData (groupPrior source S) q)
    (output : (splitDisclosure source S s).Output) :
    disclosureProbability source (splitDisclosure source S s) output = s.reportMass output := by
  classical
  unfold disclosureProbability disclosureJointMass
  rw [Finset.sum_comm]
  change (∑ input, ∑ e, source.jointPrior.val (e, input) *
    (s.kernel (maskedSignalProfile S input)).val output) = _
  simp_rw [← Finset.sum_mul]
  change (∑ input, signalProfileProbability source input *
    (s.kernel (maskedSignalProfile S input)).val output) = _
  rw [← sum_groupPrior_mul source S (fun x => (s.kernel x).val output)]
  rfl

/-- A genuine general-output violation has a finite real witness with at most r_S+1
positive reports. -/
theorem exists_small_finite_violation (S B : Finset Index)
    (d : GeneralSignalDisclosure Index Signal)
    (upper : IsGeneralBlackwellBelowOn source d (generalWholeSignalDisclosure S))
    (lower : IsGeneralBlackwellBelowOn source (generalWholeSignalDisclosure (S ∩ B)) d)
    (sign : ℝ)
    (strict : sign * ((generalDisclosureWithWholeValue source B d - generalDisclosureValue source d) -
      (weakSignalValue source (S ∪ B) - weakSignalValue source S)) < 0) :
    ∃ finite : SignalDisclosure Index Signal,
      IsBlackwellBelowOn source (wholeSignalDisclosure (S ∩ B)) finite ∧
      IsBlackwellBelowOn source finite (wholeSignalDisclosure S) ∧
      sign * ((disclosureWithWholeValue source B finite - disclosureValue source finite) -
        (weakSignalValue source (S ∪ B) - weakSignalValue source S)) < 0 ∧
      (Finset.univ.filter (fun output => 0 < disclosureProbability source finite output)).card ≤
        (Finset.univ.filter (fun x => 0 < groupPriorMass source S x)).card + 1 := by
  classical
  obtain ⟨q, supported, ⟨c, fiber⟩, negative⟩ :=
    exists_strict_grouped_posterior source S B d upper lower sign strict
  obtain ⟨s⟩ := nonempty_splitData (groupPrior source S) q supported
  refine ⟨splitDisclosure source S s,
    whole_below_splitDisclosure source (S ∩ B) S Finset.inter_subset_left s c fiber,
    splitDisclosure_below_whole source S s, ?_, ?_⟩
  · rw [splitDisclosure_marginal_value, weakSignalMarginal_grouped_baseline]
    change sign * (s.value (groupedMarginalFunctional source S B) -
      ∑ x, (groupPrior source S).val x * groupedMarginalFunctional source S B (Lottery.pure x).val) < 0
    rw [s.value_deficit]
    change sign * (s.mass * groupedDeficit source S B q.val) < 0
    rw [mul_left_comm sign s.mass]
    exact mul_neg_of_pos_of_neg s.positive negative
  · simp only [splitDisclosure_probability]
    exact s.positive_report_count_le

end
end EconCSLib.OpenProblem.New.EconCSBench.InformationalSubstitutesComplements.FiniteWitness

end


section

/-!
## Exact finite-real tests for the original strong properties

Finite randomized disclosures suffice semantically. Their real coefficients are not
assumed rational or encoded, and no algorithmic complexity follows.
-/
namespace EconCSLib.OpenProblem.New.EconCSBench.InformationalSubstitutesComplements.FiniteWitness
open EconCSLib.OpenProblem.New.EconCSBench.InformationalSubstitutesComplements

variable {State Index : Type*} {Signal : Index → Type*}
  [Fintype State] [Fintype Index] [DecidableEq Index]
  [∀ i, Fintype (Signal i)] [∀ i, DecidableEq (Signal i)] [∀ i, Nonempty (Signal i)]
  (source : FiniteBayesianInformation State Index Signal)

/-- Strong substitutes over arbitrary report spaces are exactly their finite-real tests. -/
theorem isStrongSubstitutes_iff_finite :
    IsStrongSubstitutes source ↔
      ∀ A B : Finset Index, ∀ d : SignalDisclosure Index Signal,
        IsBlackwellBelowOn source (wholeSignalDisclosure (A ∩ B)) d →
        IsBlackwellBelowOn source d (wholeSignalDisclosure A) →
        weakSignalValue source (A ∪ B) - weakSignalValue source A ≤
          disclosureWithWholeValue source B d - disclosureValue source d := by
  constructor
  · intro holds A B d lower upper
    have hlo := lower.toGeneral
    have hup := upper.toGeneral
    rw [wholeSignalDisclosure_toGeneral] at hlo hup
    simpa only [generalDisclosureWithWholeValue_toGeneral, generalDisclosureValue_toGeneral]
      using holds A B d.toGeneral hlo hup
  · intro finite A B d lower upper
    by_contra not_le
    have strict : (1 : ℝ) * ((generalDisclosureWithWholeValue source B d -
        generalDisclosureValue source d) -
      (weakSignalValue source (A ∪ B) - weakSignalValue source A)) < 0 := by
      simpa only [one_mul] using sub_neg.mpr (lt_of_not_ge not_le)
    obtain ⟨witness, hlo, hup, violation, _⟩ :=
      exists_small_finite_violation source A B d upper lower 1 strict
    have bound := finite A B witness hlo hup
    linarith

/-- Strong complements over arbitrary report spaces are exactly their finite-real tests. -/
theorem isStrongComplements_iff_finite :
    IsStrongComplements source ↔
      ∀ A B : Finset Index, ∀ d : SignalDisclosure Index Signal,
        IsBlackwellBelowOn source (wholeSignalDisclosure (A ∩ B)) d →
        IsBlackwellBelowOn source d (wholeSignalDisclosure A) →
        disclosureWithWholeValue source B d - disclosureValue source d ≤
          weakSignalValue source (A ∪ B) - weakSignalValue source A := by
  constructor
  · intro holds A B d lower upper
    have hlo := lower.toGeneral
    have hup := upper.toGeneral
    rw [wholeSignalDisclosure_toGeneral] at hlo hup
    simpa only [generalDisclosureWithWholeValue_toGeneral, generalDisclosureValue_toGeneral]
      using holds A B d.toGeneral hlo hup
  · intro finite A B d lower upper
    by_contra not_le
    have violation := lt_of_not_ge not_le
    have strict : (-1 : ℝ) * ((generalDisclosureWithWholeValue source B d -
        generalDisclosureValue source d) -
      (weakSignalValue source (A ∪ B) - weakSignalValue source A)) < 0 := by
      linarith
    obtain ⟨witness, hlo, hup, finiteViolation, _⟩ :=
      exists_small_finite_violation source A B d upper lower (-1) strict
    have bound := finite A B witness hlo hup
    linarith

end EconCSLib.OpenProblem.New.EconCSBench.InformationalSubstitutesComplements.FiniteWitness

end


section

/-!
## Completeness of mathematical finite-real negative certificates

Continuous strong disclosures can be replaced by finite disclosures while preserving a
strict violation. Coefficients remain arbitrary real numbers; this result supplies
neither a machine encoding nor a polynomial algorithm.
-/
namespace EconCSLib.OpenProblem.New.EconCSBench.InformationalSubstitutesComplements.FiniteWitness
open EconCSLib.OpenProblem.New.EconCSBench.InformationalSubstitutesComplements
noncomputable section

/-- All six original properties have complete finite-real negative certificates. -/
theorem exists_valid_finite_real_negative_iff (I : RealInformationInput)
    (property : InformationalProperty) :
    (∃ certificate : FiniteRealCertificationOutput I.alphabet,
      certificate ≠ .accept ∧ certificate.Valid I property) ↔
        ¬ HasInformationalProperty I.source property := by
  classical
  constructor
  · rintro ⟨certificate, negative, valid⟩
    exact valid.rejects negative
  · intro fails
    obtain ⟨certificate, negative, valid⟩ := (exists_valid_real_negative_iff I property).mpr fails
    cases certificate with
    | accept => exact False.elim (negative rfl)
    | weakViolation smaller larger added =>
        exact ⟨.weakViolation smaller larger added, by simp, valid⟩
    | moderateViolation A B disclosure =>
        exact ⟨.moderateViolation A B disclosure, by simp, valid⟩
    | strongViolation A B disclosure =>
        rcases valid with ⟨kind, lower, upper, violation⟩
        rcases kind with rfl | rfl
        · change generalDisclosureWithWholeValue I.source B disclosure -
              generalDisclosureValue I.source disclosure <
            weakSignalValue I.source (A ∪ B) - weakSignalValue I.source A at violation
          have strict : (1 : ℝ) * ((generalDisclosureWithWholeValue I.source B disclosure -
              generalDisclosureValue I.source disclosure) -
            (weakSignalValue I.source (A ∪ B) - weakSignalValue I.source A)) < 0 := by
            linarith
          obtain ⟨finite, finiteLower, finiteUpper, finiteStrict, _⟩ :=
            exists_small_finite_violation I.source A B disclosure upper lower 1 strict
          refine ⟨.strongViolation A B finite, by simp, Or.inl rfl,
            finiteLower, finiteUpper, ?_⟩
          change disclosureWithWholeValue I.source B finite - disclosureValue I.source finite <
            weakSignalValue I.source (A ∪ B) - weakSignalValue I.source A
          linarith
        · change weakSignalValue I.source (A ∪ B) - weakSignalValue I.source A <
            generalDisclosureWithWholeValue I.source B disclosure -
              generalDisclosureValue I.source disclosure at violation
          have strict : (-1 : ℝ) * ((generalDisclosureWithWholeValue I.source B disclosure -
              generalDisclosureValue I.source disclosure) -
            (weakSignalValue I.source (A ∪ B) - weakSignalValue I.source A)) < 0 := by
            linarith
          obtain ⟨finite, finiteLower, finiteUpper, finiteStrict, _⟩ :=
            exists_small_finite_violation I.source A B disclosure upper lower (-1) strict
          refine ⟨.strongViolation A B finite, by simp, Or.inr rfl,
            finiteLower, finiteUpper, ?_⟩
          change weakSignalValue I.source (A ∪ B) - weakSignalValue I.source A <
            disclosureWithWholeValue I.source B finite - disclosureValue I.source finite
          linarith

end
end EconCSLib.OpenProblem.New.EconCSBench.InformationalSubstitutesComplements.FiniteWitness

end


section

/-!
## General report labels have no informational content

A measurable equivalence of report spaces preserves posterior vectors almost
everywhere and both expected-score expressions.
-/
namespace EconCSLib.OpenProblem.New.EconCSBench.InformationalSubstitutesComplements

open MeasureTheory ProbabilityTheory
open scoped BigOperators
noncomputable section
universe u v w

variable {Index : Type u} {Signal : Index → Type v}
  [Fintype Index] [DecidableEq Index]
  [∀ i, Fintype (Signal i)] [∀ i, DecidableEq (Signal i)]

/-- Push a disclosure forward along a measurable bijection of report spaces. -/
def GeneralSignalDisclosure.relabel (d : GeneralSignalDisclosure Index Signal)
    {Y : Type (max u v)} [MeasurableSpace Y] (labels : d.Output ≃ᵐ Y) :
    GeneralSignalDisclosure Index Signal where
  Output := Y
  kernel := fun input => (d.kernel input).map labels
  kernel_isProbability := fun input => by
    letI := d.kernel_isProbability input
    exact Measure.isProbabilityMeasure_map labels.measurable.aemeasurable

private theorem relabeled_kernel_comp {A B C D : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C] [MeasurableSpace D]
    (μ : Measure A) (κ : Kernel A C) (inputLabels : A ≃ᵐ B) (outputLabels : C ≃ᵐ D) :
    ((κ.comap inputLabels.symm inputLabels.symm.measurable).map outputLabels) ∘ₘ
      μ.map inputLabels = (κ ∘ₘ μ).map outputLabels := by
  rw [← Measure.map_comp _ _ outputLabels.measurable]
  congr 1
  ext s hs
  rw [Measure.bind_apply hs (Kernel.aemeasurable _), Measure.bind_apply hs κ.aemeasurable,
    inputLabels.measurableEmbedding.lintegral_map]
  simp only [Kernel.comap_apply', inputLabels.symm_apply_apply]

variable {State : Type w} [Fintype State]
  (source : FiniteBayesianInformation State Index Signal)

/-- Conjugating the garbling proves that the support-relative order ignores report labels. -/
theorem isGeneralBlackwellBelowOn_relabel_iff
    (less more : GeneralSignalDisclosure Index Signal)
    {Y Z : Type (max u v)} [MeasurableSpace Y] [MeasurableSpace Z]
    (lessLabels : less.Output ≃ᵐ Y) (moreLabels : more.Output ≃ᵐ Z) :
    IsGeneralBlackwellBelowOn source (less.relabel lessLabels) (more.relabel moreLabels) ↔
      IsGeneralBlackwellBelowOn source less more := by
  constructor
  · rintro ⟨κ, hκ, h⟩
    letI := hκ
    refine ⟨(κ.comap moreLabels moreLabels.measurable).map lessLabels.symm,
      Kernel.IsMarkovKernel.map _ lessLabels.symm.measurable, ?_⟩
    intro input hinput
    have hinput' : (less.kernel input).map lessLabels =
        κ ∘ₘ (more.kernel input).map moreLabels := h input hinput
    calc
      less.kernel input = (κ ∘ₘ (more.kernel input).map moreLabels).map lessLabels.symm :=
        lessLabels.map_apply_eq_iff_map_symm_apply_eq.mp hinput'
      _ = ((κ.comap moreLabels moreLabels.measurable).map lessLabels.symm) ∘ₘ
          more.kernel input := by
        simpa only [MeasurableEquiv.symm_symm, MeasurableEquiv.map_symm_map] using
          (relabeled_kernel_comp ((more.kernel input).map moreLabels) κ
            moreLabels.symm lessLabels.symm).symm
  · rintro ⟨κ, hκ, h⟩
    letI := hκ
    change ∃ garbling : Kernel Z Y, IsMarkovKernel garbling ∧
      ∀ input, 0 < signalProfileProbability source input →
        (less.kernel input).map lessLabels = garbling ∘ₘ (more.kernel input).map moreLabels
    refine ⟨(κ.comap moreLabels.symm moreLabels.symm.measurable).map lessLabels,
      Kernel.IsMarkovKernel.map _ lessLabels.measurable, ?_⟩
    intro input hinput
    rw [relabeled_kernel_comp (more.kernel input) κ moreLabels lessLabels, h input hinput]

/-- Each state/report law is pushed forward by the same relabeling. -/
theorem generalDisclosureStateMeasure_relabel (d : GeneralSignalDisclosure Index Signal)
    {Y : Type (max u v)} [MeasurableSpace Y] (labels : d.Output ≃ᵐ Y) (e : State) :
    generalDisclosureStateMeasure source (d.relabel labels) e =
      (generalDisclosureStateMeasure source d e).map labels := by
  classical
  simp only [generalDisclosureStateMeasure, GeneralSignalDisclosure.relabel,
    Measure.map_finset_sum labels.measurable.aemeasurable, Measure.map_smul]
  rfl

/-- The report marginal is pushed forward as well. -/
theorem generalDisclosureMeasure_relabel (d : GeneralSignalDisclosure Index Signal)
    {Y : Type (max u v)} [MeasurableSpace Y] (labels : d.Output ≃ᵐ Y) :
    generalDisclosureMeasure source (d.relabel labels) =
      (generalDisclosureMeasure source d).map labels := by
  simp only [generalDisclosureMeasure, generalDisclosureStateMeasure_relabel,
    Measure.map_finset_sum labels.measurable.aemeasurable]
  rfl

/-- RN posteriors agree almost everywhere, as appropriate for conditional laws. -/
theorem generalDisclosurePosterior_relabel_ae (d : GeneralSignalDisclosure Index Signal)
    {Y : Type (max u v)} [MeasurableSpace Y] (labels : d.Output ≃ᵐ Y) :
    (fun output => generalDisclosurePosterior source (d.relabel labels) (labels output))
      =ᵐ[generalDisclosureMeasure source d] generalDisclosurePosterior source d := by
  have h : ∀ e : State, ∀ᵐ output ∂generalDisclosureMeasure source d,
      ((generalDisclosureStateMeasure source d e).map labels).rnDeriv
        ((generalDisclosureMeasure source d).map labels) (labels output) =
      (generalDisclosureStateMeasure source d e).rnDeriv
        (generalDisclosureMeasure source d) output :=
    fun e => labels.measurableEmbedding.rnDeriv_map _ _
  filter_upwards [ae_all_iff.mpr h] with output hout
  funext e
  simp only [generalDisclosurePosterior, generalDisclosureStateMeasure_relabel,
    generalDisclosureMeasure_relabel]
  exact congrArg ENNReal.toReal (hout e)

/-- Expected posterior score is invariant under measurable report relabeling. -/
theorem generalDisclosureValue_relabel (d : GeneralSignalDisclosure Index Signal)
    {Y : Type (max u v)} [MeasurableSpace Y] (labels : d.Output ≃ᵐ Y) :
    generalDisclosureValue source (d.relabel labels) = generalDisclosureValue source d := by
  unfold generalDisclosureValue
  rw [generalDisclosureMeasure_relabel]
  change (∫ output : Y, source.score (generalDisclosurePosterior source
    (d.relabel labels) output) ∂(generalDisclosureMeasure source d).map labels) = _
  rw [integral_map_equiv labels]
  exact integral_congr_ae ((generalDisclosurePosterior_relabel_ae source d labels).fun_comp
    source.score)

variable [∀ i, Nonempty (Signal i)]

/-- Fixing a whole-signal observation commutes with report relabeling. -/
theorem generalDisclosureWithWholeStateMeasure_relabel (B : Finset Index)
    (d : GeneralSignalDisclosure Index Signal)
    {Y : Type (max u v)} [MeasurableSpace Y] (labels : d.Output ≃ᵐ Y)
    (observed : SignalProfile Index Signal) (e : State) :
    generalDisclosureWithWholeStateMeasure source B (d.relabel labels) observed e =
      (generalDisclosureWithWholeStateMeasure source B d observed e).map labels := by
  classical
  unfold generalDisclosureWithWholeStateMeasure
  rw [Measure.map_finset_sum labels.measurable.aemeasurable]
  apply Finset.sum_congr rfl
  intro input _
  split_ifs <;> simp only [GeneralSignalDisclosure.relabel, Measure.map_smul, Measure.map_zero]
    <;> rfl

/-- The joint whole-observation/report law is pushed forward in the report coordinate. -/
theorem generalDisclosureWithWholeMeasure_relabel (B : Finset Index)
    (d : GeneralSignalDisclosure Index Signal)
    {Y : Type (max u v)} [MeasurableSpace Y] (labels : d.Output ≃ᵐ Y)
    (observed : SignalProfile Index Signal) :
    generalDisclosureWithWholeMeasure source B (d.relabel labels) observed =
      (generalDisclosureWithWholeMeasure source B d observed).map labels := by
  simp only [generalDisclosureWithWholeMeasure, generalDisclosureWithWholeStateMeasure_relabel,
    Measure.map_finset_sum labels.measurable.aemeasurable]
  rfl

/-- Joint posteriors agree almost everywhere in each whole-observation slice. -/
theorem generalDisclosureWithWholePosterior_relabel_ae (B : Finset Index)
    (d : GeneralSignalDisclosure Index Signal)
    {Y : Type (max u v)} [MeasurableSpace Y] (labels : d.Output ≃ᵐ Y)
    (observed : SignalProfile Index Signal) :
    (fun output => generalDisclosureWithWholePosterior source B (d.relabel labels)
      observed (labels output)) =ᵐ[generalDisclosureWithWholeMeasure source B d observed]
      generalDisclosureWithWholePosterior source B d observed := by
  have h : ∀ e : State, ∀ᵐ output ∂generalDisclosureWithWholeMeasure source B d observed,
      ((generalDisclosureWithWholeStateMeasure source B d observed e).map labels).rnDeriv
        ((generalDisclosureWithWholeMeasure source B d observed).map labels) (labels output) =
      (generalDisclosureWithWholeStateMeasure source B d observed e).rnDeriv
        (generalDisclosureWithWholeMeasure source B d observed) output :=
    fun e => labels.measurableEmbedding.rnDeriv_map _ _
  filter_upwards [ae_all_iff.mpr h] with output hout
  funext e
  simp only [generalDisclosureWithWholePosterior, generalDisclosureWithWholeStateMeasure_relabel,
    generalDisclosureWithWholeMeasure_relabel]
  exact congrArg ENNReal.toReal (hout e)

/-- Joint observation values, hence all marginal-score comparisons, are label-invariant. -/
theorem generalDisclosureWithWholeValue_relabel (B : Finset Index)
    (d : GeneralSignalDisclosure Index Signal)
    {Y : Type (max u v)} [MeasurableSpace Y] (labels : d.Output ≃ᵐ Y) :
    generalDisclosureWithWholeValue source B (d.relabel labels) =
      generalDisclosureWithWholeValue source B d := by
  classical
  unfold generalDisclosureWithWholeValue
  apply Finset.sum_congr rfl
  intro observed _
  rw [generalDisclosureWithWholeMeasure_relabel]
  change (∫ output : Y, source.score (generalDisclosureWithWholePosterior source B
    (d.relabel labels) observed output)
      ∂(generalDisclosureWithWholeMeasure source B d observed).map labels) = _
  rw [integral_map_equiv labels]
  exact integral_congr_ae
    ((generalDisclosureWithWholePosterior_relabel_ae source B d labels observed).fun_comp source.score)

end
end EconCSLib.OpenProblem.New.EconCSBench.InformationalSubstitutesComplements

end
