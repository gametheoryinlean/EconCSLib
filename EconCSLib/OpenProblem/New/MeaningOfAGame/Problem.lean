/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.Foundation.Utility.Lottery
import EconCSLib.OpenProblem.New.Complexity.All
import EconCSLib.OpenProblem.Util.Answer
import Lean.Elab.Tactic.NormCast
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Sigmoid
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Set.Card
import Mathlib.Dynamics.Flow
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.Topology.MetricSpace.Thickening

/-!
# 11. The meaning of a game
-/



section

/-!
## Replicator flow and minimal attractors

The domain includes real-payoff normal-form games and all mixed profiles, including
boundary profiles. Attractors follow Biggar--Shames (2024), Definition 3.5: nonempty
compact invariant sets uniformly attracting a neighborhood, minimal under inclusion.
Approaching a set is weaker than convergence to a point or equality of the omega-limit
set with the entire attractor.
-/

open scoped BigOperators

namespace EconCSLib.OpenProblem.New.EconCSBench.MeaningOfAGame

/-- A payoff table with player-dependent finite action types. -/
structure FiniteNormalFormGame (Player : Type*) (Action : Player → Type*) where
  payoff : (∀ i, Action i) → Player → ℝ

/-- Independent mixed strategies. -/
abbrev MixedProfile (Player : Type*) (Action : Player → Type*)
    [∀ i, Fintype (Action i)] := ∀ i, Lottery ℝ (Action i)

section Semantics
variable {Player : Type*} {Action : Player → Type*}
  [Fintype Player] [DecidableEq Player] [∀ i, Fintype (Action i)]

/-- Probability of a pure profile under independent mixing. -/
noncomputable def pureProfileProbability
    (x : MixedProfile Player Action) (profile : ∀ i, Action i) : ℝ :=
  ∏ i, (x i).val (profile i)

/-- Expected payoff from fixing action a. Summation over the old own coordinate
contributes one, even if a currently has probability zero. -/
noncomputable def pureDeviationPayoff (G : FiniteNormalFormGame Player Action)
    (x : MixedProfile Player Action) (i : Player) (a : Action i) : ℝ :=
  ∑ profile : ∀ j, Action j,
    pureProfileProbability x profile * G.payoff (Function.update profile i a) i

/-- The player's current expected payoff. -/
noncomputable def mixedExpectedPayoff (G : FiniteNormalFormGame Player Action)
    (x : MixedProfile Player Action) (i : Player) : ℝ :=
  ∑ profile : ∀ j, Action j,
    pureProfileProbability x profile * G.payoff profile i

/-- The replicator vector: probability times payoff advantage. -/
noncomputable def replicatorVector (G : FiniteNormalFormGame Player Action)
    (x : MixedProfile Player Action) (i : Player) (a : Action i) : ℝ :=
  (x i).val a * (pureDeviationPayoff G x i a - mixedExpectedPayoff G x i)

/-- A Mathlib flow solving the game's ODE. Uniqueness and global existence are proved in
dedicated modules. -/
structure ReplicatorSemantics (G : FiniteNormalFormGame Player Action) where
  flow : Flow ℝ (MixedProfile Player Action)
  solvesODE : ∀ x i a t,
    HasDerivAt (fun s : ℝ => ((flow s x) i).val a)
      (replicatorVector G (flow t x) i a) t

/-- Finite-coordinate l1 distance, equivalent to the usual Euclidean metric. -/
noncomputable def mixedProfileDistance (x y : MixedProfile Player Action) : ℝ :=
  ∑ i, ∑ a, |(x i).val a - (y i).val a|

/-- An open neighborhood of a set, expressed without choosing a nearest point. -/
def IsWithinProfileSet (ε : ℝ) (A : Set (MixedProfile Player Action))
    (x : MixedProfile Player Action) : Prop :=
  ∃ y ∈ A, mixedProfileDistance x y < ε

/-- Invariance for every real time. -/
def ReplicatorSemantics.IsInvariant {G : FiniteNormalFormGame Player Action}
    (dynamics : ReplicatorSemantics G) (A : Set (MixedProfile Player Action)) : Prop :=
  ∀ t : ℝ, (fun x => dynamics.flow t x) '' A = A

/-- Uniform attraction of a fixed neighborhood. The time bound is independent of the
initial point within that neighborhood. -/
def ReplicatorSemantics.IsAttractingSet {G : FiniteNormalFormGame Player Action}
    (dynamics : ReplicatorSemantics G) (A : Set (MixedProfile Player Action)) : Prop :=
  A.Nonempty ∧ IsCompact A ∧ dynamics.IsInvariant A ∧
    ∃ radius : ℝ, 0 < radius ∧
      ∀ ε : ℝ, 0 < ε → ∃ T : ℝ, 0 ≤ T ∧
        ∀ t, T ≤ t → ∀ x, IsWithinProfileSet radius A x →
          IsWithinProfileSet ε A (dynamics.flow t x)

/-- Minimality excludes the trivial answer consisting of the whole strategy space when it
contains a proper attracting set. -/
def ReplicatorSemantics.IsMinimalAttractor {G : FiniteNormalFormGame Player Action}
    (dynamics : ReplicatorSemantics G) (A : Set (MixedProfile Player Action)) : Prop :=
  dynamics.IsAttractingSet A ∧
    ∀ B, B ⊆ A → dynamics.IsAttractingSet B → A ⊆ B

/-- Compatibility name for a minimal attractor. -/
abbrev ReplicatorSemantics.IsAttractor {G : FiniteNormalFormGame Player Action}
    (dynamics : ReplicatorSemantics G) (A : Set (MixedProfile Player Action)) : Prop :=
  dynamics.IsMinimalAttractor A

/-- All minimal attractors, with no finiteness assumption. -/
def ReplicatorSemantics.attractors {G : FiniteNormalFormGame Player Action}
    (dynamics : ReplicatorSemantics G) : Set (Set (MixedProfile Player Action)) :=
  { A | dynamics.IsAttractor A }

/-- A minimal attractor approached in distance by the trajectory. -/
def ReplicatorSemantics.IsLimitAttractor {G : FiniteNormalFormGame Player Action}
    (dynamics : ReplicatorSemantics G) (x : MixedProfile Player Action)
    (A : Set (MixedProfile Player Action)) : Prop :=
  dynamics.IsAttractor A ∧
    ∀ ε : ℝ, 0 < ε → ∃ T : ℝ, 0 ≤ T ∧
      ∀ t, T ≤ t → IsWithinProfileSet ε A (dynamics.flow t x)

/-- The initial profile lies in the basin of a minimal attractor. -/
def ReplicatorSemantics.HasLimitAttractor {G : FiniteNormalFormGame Player Action}
    (dynamics : ReplicatorSemantics G) (x : MixedProfile Player Action) : Prop :=
  ∃ A, dynamics.IsLimitAttractor x A

end Semantics
end EconCSLib.OpenProblem.New.EconCSBench.MeaningOfAGame

end


section

/-!
## Uniqueness of the replicator semantics

The ambient vector field is polynomial. Its restriction to the compact unit ball is
Lipschitz, so Gronwall identifies any two simplex-valued solutions. Thus the flow
stored in `ReplicatorSemantics` cannot encode a choice of outcome.
-/

open scoped BigOperators

namespace EconCSLib.OpenProblem.New.EconCSBench.MeaningOfAGame

variable {Player : Type*} {Action : Player → Type*}
  [Fintype Player] [DecidableEq Player] [∀ i, Fintype (Action i)]

/-- Ambient coordinates, before imposing simplex constraints. -/
abbrev ProfileCoordinates (Player : Type*) (Action : Player → Type*) :=
  ∀ i, Action i → ℝ

/-- Forget the simplex proofs, retaining all probabilities. -/
def mixedProfileCoordinates (x : MixedProfile Player Action) :
    ProfileCoordinates Player Action := fun i => (x i).val

/-- Polynomial extension of the replicator vector to the ambient space. -/
noncomputable def ambientReplicatorVector (G : FiniteNormalFormGame Player Action)
    (x : ProfileCoordinates Player Action) : ProfileCoordinates Player Action :=
  fun i a => x i a *
    ((∑ profile : ∀ j, Action j,
      (∏ j, x j (profile j)) * G.payoff (Function.update profile i a) i) -
     (∑ profile : ∀ j, Action j,
      (∏ j, x j (profile j)) * G.payoff profile i))

/-- The extension agrees exactly with the original ODE on mixed profiles. -/
theorem ambientReplicatorVector_coordinates (G : FiniteNormalFormGame Player Action)
    (x : MixedProfile Player Action) :
    ambientReplicatorVector G (mixedProfileCoordinates x) = replicatorVector G x := rfl

/-- Polynomiality gives continuous differentiability without payoff restrictions. -/
theorem contDiff_ambientReplicatorVector (G : FiniteNormalFormGame Player Action) :
    ContDiff ℝ 1 (ambientReplicatorVector G) := by
  have hcoord (i : Player) (a : Action i) :
      ContDiff ℝ 1 (fun x : ProfileCoordinates Player Action => x i a) :=
    contDiff_pi.mp (contDiff_pi.mp contDiff_id i) a
  have hprod (profile : ∀ j, Action j) :
      ContDiff ℝ 1 (fun x : ProfileCoordinates Player Action => ∏ j, x j (profile j)) :=
    contDiff_prod fun j _ => hcoord j (profile j)
  unfold ambientReplicatorVector
  apply contDiff_pi.2
  intro i
  apply contDiff_pi.2
  intro a
  exact (hcoord i a).mul ((ContDiff.sum fun profile _ =>
    (hprod profile).mul contDiff_const).sub (ContDiff.sum fun profile _ =>
    (hprod profile).mul contDiff_const))

omit [DecidableEq Player] in
/-- Every mixed profile lies in one fixed compact ambient ball. -/
theorem mixedProfileCoordinates_mem_closedBall (x : MixedProfile Player Action) :
    mixedProfileCoordinates x ∈ Metric.closedBall 0 1 := by
  rw [Metric.mem_closedBall, dist_zero_right]
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).2
  intro i
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).2
  intro a
  change ‖(x i).val a‖ ≤ 1
  rw [Real.norm_eq_abs, abs_of_nonneg ((x i).property.1 a)]
  exact stdSimplex.le_one (x i) a

/-- A uniform Lipschitz constant exists on the ball containing all trajectories. -/
theorem ambientReplicatorVector_lipschitz (G : FiniteNormalFormGame Player Action) :
    ∃ K, LipschitzOnWith K (ambientReplicatorVector G) (Metric.closedBall 0 1) := by
  exact (contDiff_ambientReplicatorVector G).contDiffOn.exists_lipschitzOnWith
    (by norm_num) (convex_closedBall 0 1) (isCompact_closedBall 0 1)

/-- Coordinatewise ODE proofs assemble into the ambient vector ODE. -/
theorem ReplicatorSemantics.hasDerivAt_coordinates
    {G : FiniteNormalFormGame Player Action} (dynamics : ReplicatorSemantics G)
    (x : MixedProfile Player Action) (t : ℝ) :
    HasDerivAt (fun s => mixedProfileCoordinates (dynamics.flow s x))
      (ambientReplicatorVector G (mixedProfileCoordinates (dynamics.flow t x))) t := by
  apply hasDerivAt_pi.2
  intro i
  apply hasDerivAt_pi.2
  intro a
  exact dynamics.solvesODE x i a t

/-- Any two certified replicator flows agree at every time and initial profile. -/
theorem ReplicatorSemantics.flow_eq
    {G : FiniteNormalFormGame Player Action} (dynamics other : ReplicatorSemantics G)
    (t : ℝ) (x : MixedProfile Player Action) :
    dynamics.flow t x = other.flow t x := by
  obtain ⟨K, hK⟩ := ambientReplicatorVector_lipschitz G
  have h := ODE_solution_unique_univ
    (s := fun _ : ℝ => Metric.closedBall (0 : ProfileCoordinates Player Action) 1)
    (v := fun _ : ℝ => ambientReplicatorVector G)
    (t₀ := 0) (fun _ => hK)
    (fun s => ⟨dynamics.hasDerivAt_coordinates x s,
      mixedProfileCoordinates_mem_closedBall _⟩)
    (fun s => ⟨other.hasDerivAt_coordinates x s,
      mixedProfileCoordinates_mem_closedBall _⟩)
    (by simp)
  have hcoords := congrFun h t
  funext i
  apply Subtype.ext
  exact congrFun hcoords i

/-- The ODE certificate admits no two different choices of dynamics. -/
instance (G : FiniteNormalFormGame Player Action) : Subsingleton (ReplicatorSemantics G) where
  allEq dynamics other := by
    have hflow : dynamics.flow = other.flow :=
      Flow.ext fun t x => dynamics.flow_eq other t x
    cases dynamics
    cases other
    cases hflow
    rfl

/-- Any zero of the vector field is stationary, including boundary zeros. -/
theorem ReplicatorSemantics.flow_eq_of_replicatorVector_eq_zero
    {G : FiniteNormalFormGame Player Action} (dynamics : ReplicatorSemantics G)
    (x : MixedProfile Player Action) (hx : replicatorVector G x = 0) (t : ℝ) :
    dynamics.flow t x = x := by
  obtain ⟨K, hK⟩ := ambientReplicatorVector_lipschitz G
  have h := ODE_solution_unique_univ
    (s := fun _ : ℝ => Metric.closedBall (0 : ProfileCoordinates Player Action) 1)
    (v := fun _ : ℝ => ambientReplicatorVector G)
    (g := fun _ : ℝ => mixedProfileCoordinates x)
    (t₀ := 0) (fun _ => hK)
    (fun s => ⟨dynamics.hasDerivAt_coordinates x s,
      mixedProfileCoordinates_mem_closedBall _⟩)
    (fun s => ⟨by
      dsimp only
      rw [ambientReplicatorVector_coordinates, hx]
      exact hasDerivAt_const s _, mixedProfileCoordinates_mem_closedBall _⟩)
    (by simp)
  have hcoords := congrFun h t
  funext i
  apply Subtype.ext
  exact congrFun hcoords i

/-- A separately constructed simplex-valued solution is the certified flow orbit. -/
theorem ReplicatorSemantics.flow_eq_of_solution
    {G : FiniteNormalFormGame Player Action} (dynamics : ReplicatorSemantics G)
    (curve : ℝ → MixedProfile Player Action)
    (hcurve : ∀ i a t, HasDerivAt (fun s => (curve s i).val a)
      (replicatorVector G (curve t) i a) t) (s t : ℝ) :
    dynamics.flow t (curve s) = curve (t + s) := by
  obtain ⟨K, hK⟩ := ambientReplicatorVector_lipschitz G
  have h := ODE_solution_unique_univ
    (s := fun _ : ℝ => Metric.closedBall (0 : ProfileCoordinates Player Action) 1)
    (v := fun _ : ℝ => ambientReplicatorVector G)
    (g := fun t : ℝ => mixedProfileCoordinates (curve (t + s)))
    (t₀ := 0) (fun _ => hK)
    (fun t => ⟨dynamics.hasDerivAt_coordinates (curve s) t,
      mixedProfileCoordinates_mem_closedBall _⟩)
    (fun t => ⟨by
      apply hasDerivAt_pi.2
      intro i
      apply hasDerivAt_pi.2
      intro a
      simpa using (hcurve i a (t + s)).comp t ((hasDerivAt_id t).add_const s),
      mixedProfileCoordinates_mem_closedBall _⟩)
    (by simp)
  have hcoords := congrFun h t
  funext i
  apply Subtype.ext
  exact congrFun hcoords i

end EconCSLib.OpenProblem.New.EconCSBench.MeaningOfAGame

end


section

/-!
## Basic metric consequences of attractor semantics

The explicit l1 distance controls the inherited product metric. In particular,
approaching a compact set from a stationary profile is equivalent to membership.
-/

open scoped BigOperators

namespace EconCSLib.OpenProblem.New.EconCSBench.MeaningOfAGame

variable {Player : Type*} {Action : Player → Type*}
  [Fintype Player] [∀ i, Fintype (Action i)]

/-- The explicit profile distance is nonnegative. -/
theorem mixedProfileDistance_nonneg (x y : MixedProfile Player Action) :
    0 ≤ mixedProfileDistance x y := by
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _

/-- The explicit profile distance vanishes on the diagonal. -/
@[simp] theorem mixedProfileDistance_self (x : MixedProfile Player Action) :
    mixedProfileDistance x x = 0 := by
  simp [mixedProfileDistance]

/-- The inherited product metric is bounded by the explicit l1 distance. -/
theorem dist_le_mixedProfileDistance (x y : MixedProfile Player Action) :
    dist x y ≤ mixedProfileDistance x y := by
  classical
  apply (dist_pi_le_iff (mixedProfileDistance_nonneg x y)).2
  intro i
  change dist ((x i).val) ((y i).val) ≤ mixedProfileDistance x y
  apply (dist_pi_le_iff (mixedProfileDistance_nonneg x y)).2
  intro a
  rw [Real.dist_eq]
  calc
    |(x i).val a - (y i).val a| ≤ ∑ b, |(x i).val b - (y i).val b| :=
      Finset.single_le_sum (fun b _ => abs_nonneg ((x i).val b - (y i).val b))
        (Finset.mem_univ a)
    _ ≤ ∑ j, ∑ b, |(x j).val b - (y j).val b| :=
      Finset.single_le_sum
        (f := fun j : Player => ∑ b : Action j, |(x j).val b - (y j).val b|)
        (fun j _ => Finset.sum_nonneg fun b _ => abs_nonneg ((x j).val b - (y j).val b))
        (Finset.mem_univ i)

/-- Arbitrarily small explicit neighborhoods detect membership in a closed set. -/
theorem mem_of_forall_isWithinProfileSet {A : Set (MixedProfile Player Action)}
    (hA : IsClosed A) {x : MixedProfile Player Action}
    (hx : ∀ ε : ℝ, 0 < ε → IsWithinProfileSet ε A x) : x ∈ A := by
  apply (Metric.mem_of_closed' hA).2
  intro ε hε
  obtain ⟨y, hy, hxy⟩ := hx ε hε
  exact ⟨y, hy, (dist_le_mixedProfileDistance x y).trans_lt hxy⟩

variable [DecidableEq Player]

/-- A stationary trajectory approaches a minimal attractor exactly when it lies in it. -/
theorem ReplicatorSemantics.isLimitAttractor_iff_of_stationary
    {G : FiniteNormalFormGame Player Action} (dynamics : ReplicatorSemantics G)
    (x : MixedProfile Player Action) (hx : ∀ t : ℝ, dynamics.flow t x = x)
    (A : Set (MixedProfile Player Action)) :
    dynamics.IsLimitAttractor x A ↔ dynamics.IsMinimalAttractor A ∧ x ∈ A := by
  constructor
  · intro h
    refine ⟨h.1, mem_of_forall_isWithinProfileSet h.1.1.2.1.isClosed ?_⟩
    intro ε hε
    obtain ⟨T, _, hT⟩ := h.2 ε hε
    simpa only [hx T] using hT T le_rfl
  · rintro ⟨hA, hxA⟩
    refine ⟨hA, fun ε hε => ⟨0, le_rfl, fun t _ => ?_⟩⟩
    exact ⟨x, hxA, by simpa only [hx t, mixedProfileDistance_self] using hε⟩

/-- The stationary criterion follows from a zero of the actual replicator vector. -/
theorem ReplicatorSemantics.isLimitAttractor_iff_of_replicatorVector_eq_zero
    {G : FiniteNormalFormGame Player Action} (dynamics : ReplicatorSemantics G)
    (x : MixedProfile Player Action) (hx : replicatorVector G x = 0)
    (A : Set (MixedProfile Player Action)) :
    dynamics.IsLimitAttractor x A ↔ dynamics.IsMinimalAttractor A ∧ x ∈ A :=
  dynamics.isLimitAttractor_iff_of_stationary x
    (dynamics.flow_eq_of_replicatorVector_eq_zero x hx) A

end EconCSLib.OpenProblem.New.EconCSBench.MeaningOfAGame

end


section

/-!
## Finite game shape, independent of payoff representation
-/
namespace EconCSLib.OpenProblem.New.EconCSBench.MeaningOfAGame

/-- Nonempty finite player and action labels, supplied as part of the input. -/
structure GameShape where
  playerCount : ℕ
  playerCount_pos : 0 < playerCount
  actionCount : Fin playerCount → ℕ
  actionCount_pos : ∀ i, 0 < actionCount i

abbrev GameShape.Player (shape : GameShape) := Fin shape.playerCount
abbrev GameShape.Action (shape : GameShape) (i : shape.Player) := Fin (shape.actionCount i)
abbrev GameShape.PureProfile (shape : GameShape) := ∀ i, shape.Action i
abbrev GameShape.RealProfile (shape : GameShape) := MixedProfile shape.Player shape.Action

end EconCSLib.OpenProblem.New.EconCSBench.MeaningOfAGame

end


section

/-!
## Explicit rational games and starting profiles

This named adapter encodes rational data exactly and does not round arbitrary reals.
Codes are independent of the dynamics and the output language.
-/
namespace EconCSLib.OpenProblem.New.EconCSBench.MeaningOfAGame
open WordRAM.FiniteData

/-- Lexicographic profile enumeration, with the first player varying slowest. -/
def finiteProfiles : (n : ℕ) → (card : Fin n → ℕ) →
    List ((i : Fin n) → Fin (card i))
  | 0, _ => [fun i => Fin.elim0 i]
  | n + 1, card =>
    (List.ofFn (fun head : Fin (card 0) => head)).flatMap (fun head =>
      (finiteProfiles n (fun i => card i.succ)).map (fun tail => Fin.cons head tail))

/-- Every rational payoff table, without zero-sum, genericity or sign restrictions. -/
structure RationalGame where
  shape : GameShape
  payoff : shape.PureProfile → shape.Player → ℚ

/-- Exact real interpretation; not a real-arithmetic RAM instruction. -/
noncomputable def RationalGame.toReal (G : RationalGame) :
    FiniteNormalFormGame G.shape.Player G.shape.Action where
  payoff profile i := (G.payoff profile i : ℝ)

/-- Player/action counts followed by all payoffs in profile-major order. -/
def RationalGame.inputAtoms (G : RationalGame) : List Atom :=
  [.integer (Int.ofNat G.shape.playerCount)] ++
  List.ofFn (fun i : G.shape.Player => .integer (Int.ofNat (G.shape.actionCount i))) ++
  (finiteProfiles G.shape.playerCount G.shape.actionCount).flatMap (fun profile =>
    List.ofFn (fun i : G.shape.Player => .rational (G.payoff profile i)))

/-- Full numerators and denominators, without value-dependent padding. -/
def RationalGame.code (G : RationalGame) : Code := tableCode G.inputAtoms

/-- Rational mixed profiles, including probabilities zero and one. -/
abbrev RationalMixedProfile (shape : GameShape) := ∀ i, Lottery ℚ (shape.Action i)

/-- Casting probabilities preserves nonnegativity and normalization. -/
noncomputable def RationalMixedProfile.toReal {shape : GameShape}
    (x : RationalMixedProfile shape) : shape.RealProfile :=
  fun i => ⟨fun a => ((x i).val a : ℝ), by
    constructor
    · intro a
      change (0 : ℝ) ≤ ((x i).val a : ℝ)
      exact_mod_cast (x i).property.1 a
    · change (∑ a, ((x i).val a : ℝ)) = 1
      exact_mod_cast (x i).property.2⟩

/-- Player-major probability table; the game supplies the dimensions. -/
def RationalMixedProfile.code {shape : GameShape} (x : RationalMixedProfile shape) : Code :=
  tableCode ((List.ofFn (fun i : shape.Player =>
    List.ofFn (fun a : shape.Action i => Atom.rational ((x i).val a)))).flatten)

/-- No basin, interior or nonstationarity promise is imposed. -/
structure RationalStart where
  game : RationalGame
  profile : RationalMixedProfile game.shape

/-- Length-framed game and profile codes, independent of dynamics and output. -/
def RationalStart.code (I : RationalStart) : Code :=
  pairCode I.game.code I.profile.code

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

/-- A set description. None means malformed syntax, not absence of an attractor.
Denotation receives the shape but no input payoff or profile. -/
structure AttractorSetLanguage where
  denotes : (shape : GameShape) → Code → Option (Set shape.RealProfile)

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

/-- Public dimensions, independent of the payoff table or its attractors. -/
def GameShape.code (shape : GameShape) : Code :=
  tableCode ([.integer (Int.ofNat shape.playerCount)] ++
    List.ofFn (fun i : shape.Player => .integer (Int.ofNat (shape.actionCount i))))

/-- A distance query contains a description, rational point and unary precision. -/
def distanceQuery {shape : GameShape} (description : Code)
    (point : RationalMixedProfile shape) (precision : ℕ) : Code :=
  pairCode (pairCode shape.code description)
    (pairCode point.code (List.replicate precision true ++ [false]))

/-- One fixed evaluator and polynomial bound, shared by all descriptions. -/
structure PolynomialDistanceInterpreter where
  model : WordRAM.Model
  program : WordRAM.Program
  coefficient : ℕ
  exponent : ℕ

/-- Distance to a nonempty compact set in the finite-coordinate l1 metric. -/
noncomputable def profileSetDistance {shape : GameShape}
    (point : shape.RealProfile) (A : Set shape.RealProfile) : ℝ :=
  sInf ((fun y => mixedProfileDistance point y) '' A)

/-- The actual interpreter outputs a rational approximation with absolute error at most
2^(-k). Output construction is included in its runtime. -/
def PolynomialDistanceInterpreter.Describes (interpreter : PolynomialDistanceInterpreter)
    (shape : GameShape) (description : Code) (A : Set shape.RealProfile) : Prop :=
  A.Nonempty ∧ IsCompact A ∧
    ∀ point : RationalMixedProfile shape, ∀ precision : ℕ,
      ∃ fuel : ℕ, ∃ approximation : ℚ,
        let input := distanceQuery description point precision
        let result := WordRAM.Search.execution interpreter.model interpreter.program fuel input
        result.termination = .halted (words (tableCode [.rational approximation])) ∧
        |(approximation : ℝ) - profileSetDistance point.toReal A| ≤
          1 / (2 : ℝ) ^ precision ∧
        result.cost ≤ interpreter.coefficient *
          (bitSize interpreter.model input + 1) ^ interpreter.exponent

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

/-- Escape each payload bit and terminate with false. -/
def descriptionBlock : Code → Code
  | [] => [false]
  | bit :: rest => true :: bit :: descriptionBlock rest

/-- A structural, linear-size code for a list of descriptions. -/
def descriptionListCode : List Code → Code
  | [] => [false]
  | description :: rest => true :: descriptionBlock description ++ descriptionListCode rest

/-- Exact coverage: every listed description names an attractor and every attractor has a
listed description. Duplicate names do not change the answer. -/
def DescribesAttractors (language : AttractorSetLanguage) (shape : GameShape)
    {G : FiniteNormalFormGame shape.Player shape.Action}
    (dynamics : ReplicatorSemantics G) (descriptions : List Code) : Prop :=
  (∀ description ∈ descriptions, ∃ A,
    language.denotes shape description = some A ∧ dynamics.IsAttractor A) ∧
  (∀ A, dynamics.IsAttractor A → ∃ description ∈ descriptions,
    language.denotes shape description = some A)

/-- Rational-input specialization of the same exact coverage contract. -/
abbrev DescribesAllAttractors (language : AttractorSetLanguage) (G : RationalGame)
    (dynamics : ReplicatorSemantics G.toReal) (descriptions : List Code) : Prop :=
  DescribesAttractors language G.shape dynamics descriptions

/-- Exact finite-list output with a fixed parser. -/
def ListedAttractorCollectionSolution
    (dynamics : (G : RationalGame) → ReplicatorSemantics G.toReal)
    (language : AttractorSetLanguage) (input output : Code) : Prop :=
  ∃ G : RationalGame, G.code = input ∧ ∃ descriptions,
    output = descriptionListCode descriptions ∧
      DescribesAllAttractors language G (dynamics G) descriptions

end EconCSLib.OpenProblem.New.EconCSBench.MeaningOfAGame

end


section

/-!
## A two-player coordination counterexample

Both players receive one for matching actions and zero otherwise. The uniform mixed
profile is an interior stationary point belonging to no minimal attractor. The proof
uses a uniformly attracting pure equilibrium and an explicit outgoing heteroclinic
orbit. This refutes literal all-start prediction under these exact minimal-attractor
semantics; it does not alter the source conjecture silently.
-/

open scoped BigOperators
open Filter Topology

namespace EconCSLib.OpenProblem.New.EconCSBench.MeaningOfAGame.CoordinationFixture

abbrev Profile := MixedProfile (Fin 2) (fun _ => Fin 2)

/-- Strict coordination: matching actions give each player payoff one. -/
def game : FiniteNormalFormGame (Fin 2) (fun _ => Fin 2) where
  payoff profile _ := if profile 0 = profile 1 then 1 else 0

/-- Both players strictly prefer action zero against the pure zero opponent. -/
theorem upper_strict_payoff (i a : Fin 2) (ha : a ≠ 0) :
    game.payoff (Function.update (fun _ : Fin 2 => 0) i a) i <
      game.payoff (fun _ : Fin 2 => 0) i := by
  fin_cases i <;> fin_cases a <;> norm_num [game] at *

/-- The probability of action zero; action one has the remaining probability. -/
def binaryLottery (p : ℝ) (hp : p ∈ Set.Icc 0 1) : Lottery ℝ (Fin 2) :=
  ⟨![p, 1 - p], by
    constructor
    · intro a
      fin_cases a <;> dsimp <;> linarith [hp.1, hp.2]
    · simp [Fin.sum_univ_two]⟩

/-- The diagonal of the product of binary simplices. -/
def diagonal (p : ℝ) (hp : p ∈ Set.Icc 0 1) : Profile := fun _ => binaryLottery p hp

private theorem sum_profiles (f : (Fin 2 → Fin 2) → ℝ) :
    ∑ profile, f profile = f ![0, 0] + f ![0, 1] + f ![1, 0] + f ![1, 1] := by
  rw [← (finTwoArrowEquiv (Fin 2)).symm.sum_comp]
  simp [Fintype.sum_prod_type, Fin.sum_univ_two, finTwoArrowEquiv_symm_apply]
  ring

/-- The two coordinate equations of the exact multipopulation replicator. -/
theorem vector_zero (x : Profile) (i : Fin 2) :
    replicatorVector game x i 0 =
      (x i).val 0 * (1 - (x i).val 0) * (2 * (x (1 - i)).val 0 - 1) := by
  have h0 := (x 0).property.2
  have h1 := (x 1).property.2
  simp only [Fin.sum_univ_two] at h0 h1
  have e0 : (x 0).val 1 = 1 - (x 0).val 0 := by linarith
  have e1 : (x 1).val 1 = 1 - (x 1).val 0 := by linarith
  fin_cases i <;>
    simp [replicatorVector, pureDeviationPayoff, mixedExpectedPayoff,
      pureProfileProbability, sum_profiles, Fin.prod_univ_two, game, e0, e1] <;> ring

/-- The action-one equation preserves the simplex sum. -/
theorem vector_one (x : Profile) (i : Fin 2) :
    replicatorVector game x i 1 = -replicatorVector game x i 0 := by
  have h0 := (x 0).property.2
  have h1 := (x 1).property.2
  simp only [Fin.sum_univ_two] at h0 h1
  have e0 : (x 0).val 1 = 1 - (x 0).val 0 := by linarith
  have e1 : (x 1).val 1 = 1 - (x 1).val 0 := by linarith
  fin_cases i <;>
    simp [replicatorVector, pureDeviationPayoff, mixedExpectedPayoff,
      pureProfileProbability, sum_profiles, Fin.prod_univ_two, game, e0, e1] <;> ring

/-- The interior mixed equilibrium. -/
noncomputable def center : Profile := diagonal (1 / 2) (by constructor <;> norm_num)

/-- The regression lies in the relative interior, with neither action absent. -/
theorem center_fully_mixed (i a : Fin 2) :
    0 < (center i).val a ∧ (center i).val a < 1 := by
  fin_cases a <;> norm_num [center, diagonal, binaryLottery]

/-- The pure equilibrium where both players choose action zero. -/
def upper : Profile := diagonal 1 (by constructor <;> norm_num)

theorem vector_center : replicatorVector game center = 0 := by
  funext i a
  fin_cases a
  · simp [vector_zero, center, diagonal, binaryLottery]
  · simp [vector_one, vector_zero, center, diagonal, binaryLottery]

theorem vector_upper : replicatorVector game upper = 0 := by
  funext i a
  fin_cases a
  · simp [vector_zero, upper, diagonal, binaryLottery]
  · simp [vector_one, vector_zero, upper, diagonal, binaryLottery]

/-- This interior point stays fixed for every certified replicator flow. -/
theorem center_stationary (dynamics : ReplicatorSemantics game) (t : ℝ) :
    dynamics.flow t center = center :=
  dynamics.flow_eq_of_replicatorVector_eq_zero center vector_center t

/-- Total probability assigned to the two non-equilibrium actions. -/
noncomputable def deficit (x : Profile) : ℝ := 2 - (x 0).val 0 - (x 1).val 0

theorem deficit_nonneg (x : Profile) : 0 ≤ deficit x := by
  have h0 : (x 0).val 0 ≤ 1 := stdSimplex.le_one (x 0) 0
  have h1 : (x 1).val 0 ≤ 1 := stdSimplex.le_one (x 1) 0
  unfold deficit
  linarith

theorem distance_upper (x : Profile) : mixedProfileDistance x upper = 2 * deficit x := by
  have h0 := (x 0).property.2
  have h1 := (x 1).property.2
  simp only [Fin.sum_univ_two] at h0 h1
  have hn0 := (x 0).property.1 1
  have hn1 := (x 1).property.1 1
  have hl0 : (x 0).val 0 ≤ 1 := stdSimplex.le_one (x 0) 0
  have hl1 : (x 1).val 0 ≤ 1 := stdSimplex.le_one (x 1) 0
  simp [mixedProfileDistance, Fin.sum_univ_two, upper, diagonal, binaryLottery,
    abs_of_nonpos (sub_nonpos.mpr hl0), abs_of_nonpos (sub_nonpos.mpr hl1),
    abs_of_nonneg hn0, abs_of_nonneg hn1, deficit]
  linarith

private theorem hasDerivAt_deficit (dynamics : ReplicatorSemantics game)
    (x : Profile) (t : ℝ) :
    HasDerivAt (fun s => deficit (dynamics.flow s x))
      (-(replicatorVector game (dynamics.flow t x) 0 0) -
        replicatorVector game (dynamics.flow t x) 1 0) t := by
  exact ((dynamics.solvesODE x 0 0 t).const_sub 2).sub (dynamics.solvesODE x 1 0 t)

private theorem vector_deficit_bound (x : Profile) (hx : deficit x ≤ 1 / 4) :
    -(replicatorVector game x 0 0) - replicatorVector game x 1 0 ≤
      -(3 / 8) * deficit x := by
  have hp : (x 0).val 0 ≤ 1 := stdSimplex.le_one (x 0) 0
  have hq : (x 1).val 0 ≤ 1 := stdSimplex.le_one (x 1) 0
  have hp' : 3 / 4 ≤ (x 0).val 0 := by unfold deficit at hx; linarith
  have hq' : 3 / 4 ≤ (x 1).val 0 := by unfold deficit at hx; linarith
  have hmul : (3 / 8 : ℝ) ≤ (x 0).val 0 * (2 * (x 1).val 0 - 1) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hp') (sub_nonneg.mpr hq')]
  have hmul' : (3 / 8 : ℝ) ≤ (x 1).val 0 * (2 * (x 0).val 0 - 1) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hp') (sub_nonneg.mpr hq')]
  have hb0 := mul_le_mul_of_nonneg_right hmul (sub_nonneg.mpr hp)
  have hb1 := mul_le_mul_of_nonneg_right hmul' (sub_nonneg.mpr hq)
  rw [vector_zero, vector_zero]
  change -((x 0).val 0 * (1 - (x 0).val 0) * (2 * (x 1).val 0 - 1)) -
    (x 1).val 0 * (1 - (x 1).val 0) * (2 * (x 0).val 0 - 1) ≤
    -(3 / 8) * (2 - (x 0).val 0 - (x 1).val 0)
  nlinarith

private noncomputable def envelope (t : ℝ) : ℝ := (1 / 4) * Real.exp (-t / 4)

private theorem envelope_pos (t : ℝ) : 0 < envelope t := by
  unfold envelope
  positivity

private theorem envelope_le (t : ℝ) (ht : 0 ≤ t) : envelope t ≤ 1 / 4 := by
  have h : Real.exp (-t / 4) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  unfold envelope
  linarith

private theorem hasDerivAt_envelope (t : ℝ) :
    HasDerivAt envelope (-(1 / 4) * envelope t) t := by
  convert (((hasDerivAt_id t).neg.div_const 4).exp.const_mul (1 / 4)) using 1
  simp [envelope]
  ring

/-- One decay envelope works for every start in the same neighborhood. -/
theorem deficit_decay (dynamics : ReplicatorSemantics game) (x : Profile)
    (hx : deficit x ≤ 1 / 4) {t : ℝ} (ht : 0 ≤ t) :
    deficit (dynamics.flow t x) ≤ envelope t := by
  apply image_le_of_deriv_right_lt_deriv_boundary
    (f := fun s => deficit (dynamics.flow s x))
    (f' := fun s => -(replicatorVector game (dynamics.flow s x) 0 0) -
      replicatorVector game (dynamics.flow s x) 1 0)
    (B := envelope) (a := 0) (b := t)
    (fun s _ => (hasDerivAt_deficit dynamics x s).continuousAt.continuousWithinAt)
    (fun s _ => (hasDerivAt_deficit dynamics x s).hasDerivWithinAt)
    (by simpa [envelope] using hx) hasDerivAt_envelope ?_ ⟨ht, le_rfl⟩
  intro s hs hse
  have hd := vector_deficit_bound (dynamics.flow s x)
    (hse.trans_le (envelope_le s hs.1))
  have he := envelope_pos s
  linarith

/-- The strict pure equilibrium is a uniformly attracting compact invariant set. -/
theorem upper_attracting (dynamics : ReplicatorSemantics game) :
    dynamics.IsAttractingSet {upper} := by
  refine ⟨Set.singleton_nonempty _, isCompact_singleton, ?_, 1 / 2, by norm_num, ?_⟩
  · intro t
    simp [dynamics.flow_eq_of_replicatorVector_eq_zero upper vector_upper t]
  · intro ε hε
    have hlim : Tendsto (fun t : ℝ => 2 * envelope t) atTop (𝓝 0) := by
      have hexp : Tendsto (fun t : ℝ => Real.exp (-t / 4)) atTop (𝓝 0) :=
        Real.tendsto_exp_atBot.comp
          (tendsto_neg_atTop_atBot.atBot_div_const (by norm_num : (0 : ℝ) < 4))
      convert (hexp.const_mul (1 / 4)).const_mul 2 using 1
      norm_num [envelope]
    obtain ⟨T, hT⟩ := Filter.eventually_atTop.1 (hlim.eventually (gt_mem_nhds hε))
    refine ⟨max T 0, le_max_right _ _, fun t ht x hx => ?_⟩
    obtain ⟨y, hy, hxy⟩ := hx
    have hy' : y = upper := Set.mem_singleton_iff.mp hy
    subst y
    rw [distance_upper] at hxy
    refine ⟨upper, Set.mem_singleton _, ?_⟩
    rw [distance_upper]
    exact (mul_le_mul_of_nonneg_left
      (deficit_decay dynamics x (by linarith) ((le_max_right T 0).trans ht))
      (by norm_num)).trans_lt (hT t ((le_max_left T 0).trans ht))

/-- Nonempty singletons have no proper nonempty attracting subset. -/
theorem upper_minimal (dynamics : ReplicatorSemantics game) :
    dynamics.IsMinimalAttractor {upper} := by
  refine ⟨upper_attracting dynamics, ?_⟩
  intro B hB hattr
  obtain ⟨b, hb⟩ := hattr.1
  have : b = upper := Set.mem_singleton_iff.mp (hB hb)
  subst b
  exact Set.singleton_subset_iff.mpr hb

/-- A diagonal heteroclinic orbit from the mixed saddle to the pure equilibrium. -/
noncomputable def curveCoordinate (t : ℝ) : ℝ :=
  (1 + Real.sqrt (Real.sigmoid t)) / 2

theorem curveCoordinate_mem (t : ℝ) : curveCoordinate t ∈ Set.Icc 0 1 := by
  have hnonneg := Real.sqrt_nonneg (Real.sigmoid t)
  have hle : Real.sqrt (Real.sigmoid t) ≤ 1 :=
    (Real.sqrt_le_one).2 (Real.sigmoid_le_one t)
  constructor <;> unfold curveCoordinate <;> linarith

noncomputable def curve (t : ℝ) : Profile := diagonal (curveCoordinate t) (curveCoordinate_mem t)

private theorem curveCoordinate_deriv (t : ℝ) :
    HasDerivAt curveCoordinate
      (curveCoordinate t * (1 - curveCoordinate t) * (2 * curveCoordinate t - 1)) t := by
  have hs := Real.sq_sqrt (Real.sigmoid_nonneg t)
  have hn : Real.sqrt (Real.sigmoid t) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (Real.sigmoid_pos t))
  convert (((Real.hasDerivAt_sigmoid t).sqrt (ne_of_gt (Real.sigmoid_pos t))).const_add 1).div_const 2
    using 1
  unfold curveCoordinate
  generalize Real.sqrt (Real.sigmoid t) = q at hs hn ⊢
  rw [← hs]
  field_simp [hn]
  ring

private theorem curve_solves (i a : Fin 2) (t : ℝ) :
    HasDerivAt (fun s => (curve s i).val a)
      (replicatorVector game (curve t) i a) t := by
  fin_cases a
  · simpa [curve, diagonal, binaryLottery, vector_zero] using curveCoordinate_deriv t
  · simpa [curve, diagonal, binaryLottery, vector_one, vector_zero] using
      (curveCoordinate_deriv t).const_sub 1

theorem curve_flow (dynamics : ReplicatorSemantics game) (s t : ℝ) :
    dynamics.flow t (curve s) = curve (t + s) :=
  dynamics.flow_eq_of_solution curve curve_solves s t

theorem distance_diagonal (p q : ℝ) (hp : p ∈ Set.Icc 0 1) (hq : q ∈ Set.Icc 0 1) :
    mixedProfileDistance (diagonal p hp) (diagonal q hq) = 4 * |p - q| := by
  simp [mixedProfileDistance, diagonal, binaryLottery, Fin.sum_univ_two]
  rw [abs_sub_comm q p]
  ring

theorem curve_tendsto_center :
    Tendsto (fun t => mixedProfileDistance (curve t) center) atBot (𝓝 0) := by
  have hp : Tendsto curveCoordinate atBot (𝓝 (1 / 2)) := by
    simpa [curveCoordinate] using
      (Real.tendsto_sigmoid_atBot.sqrt.const_add 1).div_const 2
  simpa [curve, center, distance_diagonal] using
    ((hp.sub_const (1 / 2)).abs.const_mul 4)

theorem curve_tendsto_upper :
    Tendsto (fun t => mixedProfileDistance upper (curve t)) atTop (𝓝 0) := by
  have hp : Tendsto curveCoordinate atTop (𝓝 1) := by
    simpa [curveCoordinate] using
      (Real.tendsto_sigmoid_atTop.sqrt.const_add 1).div_const 2
  simpa [curve, upper, distance_diagonal] using
    ((hp.const_sub 1).abs.const_mul 4)

/-- Uniform attraction forces a set containing the saddle to contain its outgoing orbit. -/
theorem curve_mem_of_center_mem (dynamics : ReplicatorSemantics game)
    {A : Set Profile} (hA : dynamics.IsAttractingSet A) (hc : center ∈ A) (u : ℝ) :
    curve u ∈ A := by
  apply mem_of_forall_isWithinProfileSet hA.2.1.isClosed
  intro ε hε
  obtain ⟨r, hr, h⟩ := hA.2.2.2
  obtain ⟨T, _, hT⟩ := h ε hε
  obtain ⟨S, hS⟩ := Filter.eventually_atBot.1
    (curve_tendsto_center.eventually (gt_mem_nhds hr))
  let s := min S (u - T)
  have hs : IsWithinProfileSet r A (curve s) :=
    ⟨center, hc, hS s (min_le_left _ _)⟩
  have hh := hT (u - s) (by dsimp [s]; linarith [min_le_right S (u - T)]) (curve s) hs
  simpa [curve_flow] using hh

/-- A compact attracting set containing the mixed saddle contains the pure attractor. -/
theorem upper_mem_of_center_mem (dynamics : ReplicatorSemantics game)
    {A : Set Profile} (hA : dynamics.IsAttractingSet A) (hc : center ∈ A) : upper ∈ A := by
  apply mem_of_forall_isWithinProfileSet hA.2.1.isClosed
  intro ε hε
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.1
    (curve_tendsto_upper.eventually (gt_mem_nhds hε))
  exact ⟨curve T, curve_mem_of_center_mem dynamics hA hc T, hT T le_rfl⟩

/-- The interior saddle is contained in no minimal attractor. -/
theorem center_not_mem_minimal (dynamics : ReplicatorSemantics game)
    {A : Set Profile} (hA : dynamics.IsMinimalAttractor A) : center ∉ A := by
  intro hc
  have hu := upper_mem_of_center_mem dynamics hA.1 hc
  have hsub := hA.2 {upper} (Set.singleton_subset_iff.mpr hu) (upper_attracting dynamics)
  have heq := Set.mem_singleton_iff.mp (hsub hc)
  have hv := congrArg (fun x : Profile => (x 0).val 0) heq
  norm_num [center, upper, diagonal, binaryLottery] at hv

/-- The literal all-start prediction task has no valid output at this interior input. -/
theorem center_has_no_limit_attractor (dynamics : ReplicatorSemantics game) :
    ¬ dynamics.HasLimitAttractor center := by
  rintro ⟨A, hA⟩
  have h := (dynamics.isLimitAttractor_iff_of_stationary center
    (center_stationary dynamics) A).mp hA
  exact center_not_mem_minimal dynamics h.1 h.2

end EconCSLib.OpenProblem.New.EconCSBench.MeaningOfAGame.CoordinationFixture

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

def shape : GameShape where
  playerCount := 2
  playerCount_pos := by decide
  actionCount := fun _ => 2
  actionCount_pos := fun _ => by decide

end CoordinationFixture
end EconCSLib.OpenProblem.New.EconCSBench.MeaningOfAGame

end


section

/-!
## Injectivity of the explicit rational game and start codecs

Header recovery determines the finite shape. Fixed-width rows and complete profile
enumeration then recover every payoff and probability.
-/

namespace EconCSLib.OpenProblem.New.EconCSBench.MeaningOfAGame
open WordRAM.FiniteData

/-- The canonical enumeration includes every pure profile. -/
theorem mem_finiteProfiles (n : ℕ) (card : Fin n → ℕ)
    (profile : (i : Fin n) → Fin (card i)) : profile ∈ finiteProfiles n card := by
  induction n with
  | zero =>
      simp only [finiteProfiles, List.mem_singleton]
      exact Subsingleton.elim _ _
  | succ n ih =>
      apply List.mem_flatMap.mpr
      refine ⟨profile 0, List.mem_ofFn.mpr ⟨profile 0, rfl⟩, ?_⟩
      apply List.mem_map.mpr
      exact ⟨Fin.tail profile, ih _ _, Fin.cons_self_tail profile⟩

private theorem fixed_rows_injective {α β : Type*} (rows : List α) (width : α → ℕ)
    (f g : (a : α) → Fin (width a) → β)
    (h : rows.flatMap (fun a => List.ofFn (f a)) =
      rows.flatMap (fun a => List.ofFn (g a))) :
    ∀ a ∈ rows, f a = g a := by
  induction rows with
  | nil => simp
  | cons a rest ih =>
      simp only [List.flatMap_cons] at h
      have hhead : List.ofFn (f a) = List.ofFn (g a) := by
        have ht := congrArg (List.take (width a)) h
        simpa using ht
      have htail : rest.flatMap (fun a => List.ofFn (f a)) =
          rest.flatMap (fun a => List.ofFn (g a)) := by
        simpa using congrArg (List.drop (width a)) h
      intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact List.ofFn_injective hhead
      · exact ih htail b hb

/-- A game's complete code determines its shape and every rational payoff. -/
theorem RationalGame.code_injective : Function.Injective RationalGame.code := by
  intro G H h
  have hatoms := tableCode_injective h
  cases G with
  | mk gs gp =>
      cases H with
      | mk hs hp =>
          cases gs with
          | mk n hn actions ha =>
              cases hs with
              | mk m hm actions' ha' =>
                  simp only [RationalGame.inputAtoms,
                    List.cons_append, List.nil_append, List.cons.injEq] at hatoms
                  have hnm : n = m := by
                    exact Int.ofNat_inj.mp (Atom.integer.inj hatoms.1)
                  subst m
                  have hshape : actions = actions' := by
                    have hheads : List.ofFn (fun i => Atom.integer (Int.ofNat (actions i))) =
                        List.ofFn (fun i => Atom.integer (Int.ofNat (actions' i))) := by
                      simpa using congrArg (List.take n) hatoms.2
                    have hh := List.ofFn_injective hheads
                    funext i
                    exact Int.ofNat_inj.mp (Atom.integer.inj (congrFun hh i))
                  subst actions'
                  have hrows :
                      (finiteProfiles n actions).flatMap (fun p => List.ofFn
                        (fun i => Atom.rational (gp p i))) =
                      (finiteProfiles n actions).flatMap (fun p => List.ofFn
                        (fun i => Atom.rational (hp p i))) := by
                    simpa using congrArg (List.drop n) hatoms.2
                  have hpayoffs : gp = hp := by
                    funext profile i
                    exact Atom.rational.inj (congrFun
                      (fixed_rows_injective (finiteProfiles n actions) (fun _ => n)
                        (fun p i => Atom.rational (gp p i))
                        (fun p i => Atom.rational (hp p i)) hrows
                        profile (mem_finiteProfiles n actions profile)) i)
                  subst hp
                  rfl

/-- The fixed shape makes all variable-width probability rows unambiguous. -/
theorem RationalMixedProfile.code_injective (shape : GameShape) :
    Function.Injective (@RationalMixedProfile.code shape) := by
  intro x y h
  have hatoms := tableCode_injective h
  have hrows :
      (List.ofFn (fun i : shape.Player => i)).flatMap (fun i =>
        List.ofFn (fun a : shape.Action i => Atom.rational ((x i).val a))) =
      (List.ofFn (fun i : shape.Player => i)).flatMap (fun i =>
        List.ofFn (fun a : shape.Action i => Atom.rational ((y i).val a))) := by
    simpa only [List.flatMap_def, List.map_ofFn, Function.comp_def] using hatoms
  funext i
  apply Subtype.ext
  funext a
  exact Atom.rational.inj (congrFun
    (fixed_rows_injective (List.ofFn (fun j : shape.Player => j)) shape.actionCount
      (fun j b => Atom.rational ((x j).val b))
      (fun j b => Atom.rational ((y j).val b)) hrows i
      (List.mem_ofFn.mpr ⟨i, rfl⟩)) a)

/-- An encoded rational start cannot be reinterpreted as a different game or profile. -/
theorem RationalStart.code_injective : Function.Injective RationalStart.code := by
  intro I J h
  obtain ⟨hgame, hprofile⟩ := pairCode_injective h
  have hg := RationalGame.code_injective hgame
  cases I with
  | mk G x =>
      cases J with
      | mk H y =>
          dsimp only at hg
          subst H
          have hxy : x = y := RationalMixedProfile.code_injective G.shape hprofile
          subst y
          rfl

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

/-- A mathematical replicator-flow model for rational games. Existence and uniqueness are
proved separately. -/
abbrev ReplicatorModel := (G : RationalGame) → ReplicatorSemantics G.toReal

/-- All well-formed rational games, without an attractor promise. -/
def ValidGameInput (input : Code) : Prop := ∃ G : RationalGame, G.code = input

/-- All rational mixed profiles, including unstable stationary points. -/
def ValidStartInput (input : Code) : Prop := ∃ I : RationalStart, I.code = input

/-- A separate promise-domain question. -/
def PromisedStartInput (dynamics : ReplicatorModel) (input : Code) : Prop :=
  ∃ I : RationalStart, I.code = input ∧
    (dynamics I.game).HasLimitAttractor I.profile.toReal

/-- The output describes an approached minimal attractor. -/
def LimitAttractorSolution (dynamics : ReplicatorModel)
    (language : AttractorSetLanguage) (input output : Code) : Prop :=
  ∃ I : RationalStart, I.code = input ∧ ∃ A,
    language.denotes I.game.shape output = some A ∧
      (dynamics I.game).IsLimitAttractor I.profile.toReal A

/-- Polynomial-time computation of the list of minimal attractors, using rational inputs
and the specified set-description language. -/
def AttractorComputationRationalWordRAMQuestion (dynamics : ReplicatorModel)
    (language : AttractorSetLanguage) : Prop :=
  WordRAM.Search.PolynomiallySolvable ValidGameInput
    (ListedAttractorCollectionSolution dynamics language)

/-- Polynomial-time prediction of an approached minimal attractor for every rational
initial profile. -/
def LimitPredictionRationalWordRAMQuestion (dynamics : ReplicatorModel)
    (language : AttractorSetLanguage) : Prop :=
  WordRAM.Search.PolynomiallySolvable ValidStartInput
    (LimitAttractorSolution dynamics language)

/-- An explicit promised-domain alternative. -/
def PromisedLimitPredictionRationalWordRAMQuestion (dynamics : ReplicatorModel)
    (language : AttractorSetLanguage) : Prop :=
  WordRAM.Search.PolynomiallySolvable (PromisedStartInput dynamics)
    (LimitAttractorSolution dynamics language)
abbrev BasinPromisedLimitPredictionRationalWordRAMQuestion :=
  PromisedLimitPredictionRationalWordRAMQuestion

end EconCSLib.OpenProblem.New.EconCSBench.MeaningOfAGame

end


section

/-!
## Literal prediction is impossible even on rational inputs

The strict coordination obstruction has zero/one payoffs and the uniform mixed initial
profile. Injectivity of the complete rational codec prevents a solver's solution
witness from reinterpreting the same input as another game or profile.
-/

namespace EconCSLib.OpenProblem.New.EconCSBench.MeaningOfAGame
namespace CoordinationFixture
open WordRAM.FiniteData
open scoped BigOperators

/-- The exact rational payoff table of the strict coordination fixture. -/
def rationalGame : RationalGame where
  shape := CoordinationFixture.shape
  payoff := fun (profile : Fin 2 → Fin 2) (_ : Fin 2) =>
    if profile 0 = profile 1 then 1 else 0

/-- Exact uniform probabilities, without approximation or a basin promise. -/
def rationalCenter : RationalMixedProfile CoordinationFixture.shape := fun _ =>
  ⟨fun _ => 1 / 2, by
    constructor
    · intro a
      norm_num
    · change (∑ _a : Fin 2, (1 / 2 : ℚ)) = 1
      norm_num⟩

def rationalStart : RationalStart := ⟨rationalGame, rationalCenter⟩

theorem rationalGame_toReal : rationalGame.toReal = game := by
  unfold RationalGame.toReal rationalGame game
  congr 1
  funext profile i
  split_ifs with h <;> simp_all

theorem rationalCenter_toReal : rationalCenter.toReal = center := by
  funext i
  apply Subtype.ext
  funext a
  fin_cases a
  · change ((1 / 2 : ℚ) : ℝ) = (1 / 2 : ℝ)
    norm_num
  · change ((1 / 2 : ℚ) : ℝ) = 1 - (1 / 2 : ℝ)
    norm_num

/-- The rational adapter includes the same answerless interior start. -/
theorem rationalStart_has_no_limit_attractor (dynamics : ReplicatorModel) :
    ¬ (dynamics rationalGame).HasLimitAttractor rationalCenter.toReal := by
  have h : ∀ d : ReplicatorSemantics rationalGame.toReal,
      ¬ d.HasLimitAttractor rationalCenter.toReal := by
    rw [rationalGame_toReal, rationalCenter_toReal]
    exact center_has_no_limit_attractor
  exact h (dynamics rationalGame)

/-- Neither finite descriptions nor unrestricted runtime can answer this rational input. -/
theorem not_limitPredictionRationalWordRAMQuestion (dynamics : ReplicatorModel)
    (language : AttractorSetLanguage) :
    ¬ LimitPredictionRationalWordRAMQuestion dynamics language := by
  rintro ⟨_, solver, _⟩
  obtain ⟨output, _, I, hcode, A, _, correct⟩ :=
    solver.correct rationalStart.code ⟨rationalStart, rfl⟩
  have hI : I = rationalStart := RationalStart.code_injective hcode
  subst I
  exact rationalStart_has_no_limit_attractor dynamics ⟨A, correct⟩

end CoordinationFixture
end EconCSLib.OpenProblem.New.EconCSBench.MeaningOfAGame

end


/-!
## Questions and answers
-/

namespace EconCSLib.OpenProblem.New.EconCSBench.MeaningOfAGame

/-- Finite-list computation in the fixed justified set language; this is a
representation-parametric schema. -/
theorem computeAttractors (dynamics : ReplicatorModel) (language : AttractorSetLanguage) :
    answer(sorry) ↔ AttractorComputationRationalWordRAMQuestion dynamics language := by
  sorry

/-- Polynomial-time attractor prediction for initial profiles in an attractor basin. -/
theorem predictAttractorOnBasin (dynamics : ReplicatorModel) (language : AttractorSetLanguage) :
    answer(sorry) ↔ BasinPromisedLimitPredictionRationalWordRAMQuestion dynamics language := by
  sorry

/-- The coordination-game counterexample refutes prediction for every rational initial
profile. -/
theorem literalPredictionAnswer (dynamics : ReplicatorModel)
    (language : AttractorSetLanguage) :
    answer(False) ↔ LimitPredictionRationalWordRAMQuestion dynamics language := by
  constructor
  · exact False.elim
  · exact CoordinationFixture.not_limitPredictionRationalWordRAMQuestion dynamics language

end EconCSLib.OpenProblem.New.EconCSBench.MeaningOfAGame
