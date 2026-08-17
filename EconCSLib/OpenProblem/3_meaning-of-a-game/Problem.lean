/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.OpenProblem.EconCSBench.Common
import EconCSLib.GameTheory.StrategicGame.MixedStrategy
import Mathlib.Analysis.Calculus.Deriv.Basic

namespace EconCSLib.OpenProblem.EconCSBench.MeaningOfAGame

/-- A finite normal-form game with a possibly player-dependent action type. -/
structure FiniteNormalFormGame
    (Player : Type*) (Action : Player → Type*) where
  /-- Real-valued payoff at every pure profile. -/
  payoff : (∀ i, Action i) → Player → ℝ

/-- Convert the benchmark representation to EconCSLib's strategic-game type. -/
def FiniteNormalFormGame.toStrategicGame
    {Player : Type*} {Action : Player → Type*}
    (G : FiniteNormalFormGame Player Action) : StrategicGame Player ℝ where
  strategy := Action
  payoff := G.payoff

/-- Mixed profiles of a finite game with player-dependent actions. -/
abbrev MixedProfile
    (Player : Type*) (Action : Player → Type*)
    [∀ i, Fintype (Action i)] :=
  ∀ i, Lottery ℝ (Action i)

/-- Probability of a pure profile under independent mixed play. -/
noncomputable def pureProfileProbability
    {Player : Type*} {Action : Player → Type*}
    [Fintype Player] [DecidableEq Player] [∀ i, Fintype (Action i)]
    (x : MixedProfile Player Action) (profile : ∀ i, Action i) : ℝ :=
  ∏ i, (x i).val (profile i)

/-- Expected payoff from forcing player `i` to pure action `a` while all
players' other coordinates are drawn from `x`. -/
noncomputable def pureDeviationPayoff
    {Player : Type*} {Action : Player → Type*}
    [Fintype Player] [DecidableEq Player]
    [∀ i, Fintype (Action i)]
    (G : FiniteNormalFormGame Player Action)
    (x : MixedProfile Player Action) (i : Player) (a : Action i) : ℝ :=
  ∑ profile : ∀ j, Action j,
    pureProfileProbability x profile *
      G.payoff (Function.update profile i a) i

/-- Expected payoff under the current mixed profile. -/
noncomputable def mixedExpectedPayoff
    {Player : Type*} {Action : Player → Type*}
    [Fintype Player] [DecidableEq Player]
    [∀ i, Fintype (Action i)]
    (G : FiniteNormalFormGame Player Action)
    (x : MixedProfile Player Action) (i : Player) : ℝ :=
  ∑ profile : ∀ j, Action j,
    pureProfileProbability x profile * G.payoff profile i

/-- The coordinate vector field of the replicator dynamics. -/
noncomputable def replicatorVector
    {Player : Type*} {Action : Player → Type*}
    [Fintype Player] [DecidableEq Player]
    [∀ i, Fintype (Action i)]
    (G : FiniteNormalFormGame Player Action)
    (x : MixedProfile Player Action) (i : Player) (a : Action i) : ℝ :=
  (x i).val a * (pureDeviationPayoff G x i a - mixedExpectedPayoff G x i)

/-- Semantic realization of the replicator flow.  The ODE and flow laws tie
the supplied trajectories to the game's standard replicator vector field. -/
structure ReplicatorSemantics
    (Player : Type*) (Action : Player → Type*)
    [Fintype Player] [DecidableEq Player]
    [∀ i, Fintype (Action i)] [∀ i, DecidableEq (Action i)]
    (G : FiniteNormalFormGame Player Action) where
  /-- Continuous-time flow from each initial mixed profile. -/
  trajectory : MixedProfile Player Action → ℝ → MixedProfile Player Action
  /-- Every trajectory starts at its supplied initial condition. -/
  initial : ∀ x, trajectory x 0 = x
  /-- Every mixed-strategy coordinate solves the replicator ODE. -/
  isReplicatorTrajectory :
    ∀ x i a t,
      0 ≤ t →
        HasDerivAt (fun time => ((trajectory x time) i).val a)
          (replicatorVector G (trajectory x t) i a) t
  /-- The trajectories form a flow, rather than unrelated ODE solutions. -/
  flow :
    ∀ x s t, trajectory x (s + t) = trajectory (trajectory x s) t

/-- An explicit metric-equivalent distance on the finite product of mixed
strategy simplices. -/
noncomputable def mixedProfileDistance
    {Player : Type*} {Action : Player → Type*}
    [Fintype Player] [DecidableEq Player] [∀ i, Fintype (Action i)]
    [∀ i, DecidableEq (Action i)]
    (x y : MixedProfile Player Action) : ℝ :=
  ∑ i, ∑ a, |(x i).val a - (y i).val a|

/-- A profile lies within `ε` of a set of mixed profiles. -/
def IsWithinProfileSet
    {Player : Type*} {Action : Player → Type*}
    [Fintype Player] [DecidableEq Player] [∀ i, Fintype (Action i)]
    [∀ i, DecidableEq (Action i)]
    (ε : ℝ) (A : Set (MixedProfile Player Action))
    (x : MixedProfile Player Action) : Prop :=
  ∃ y ∈ A, mixedProfileDistance x y < ε

/-- Invariance of a set under the complete replicator flow. -/
def ReplicatorSemantics.IsInvariant
    {Player : Type*} {Action : Player → Type*}
    [Fintype Player] [DecidableEq Player]
    [∀ i, Fintype (Action i)] [∀ i, DecidableEq (Action i)]
    {G : FiniteNormalFormGame Player Action}
    (semantics : ReplicatorSemantics Player Action G)
    (A : Set (MixedProfile Player Action)) : Prop :=
  ∀ t, (fun x => semantics.trajectory x t) '' A = A

/-- An attracting set: it is nonempty, closed, invariant, and uniformly
attracts some metric neighborhood. -/
def ReplicatorSemantics.IsAttractingSet
    {Player : Type*} {Action : Player → Type*}
    [Fintype Player] [DecidableEq Player]
    [∀ i, Fintype (Action i)] [∀ i, DecidableEq (Action i)]
    {G : FiniteNormalFormGame Player Action}
    (semantics : ReplicatorSemantics Player Action G)
    (A : Set (MixedProfile Player Action)) : Prop :=
  A.Nonempty ∧ IsClosed A ∧ semantics.IsInvariant A ∧
    ∃ neighborhoodRadius : ℝ, 0 < neighborhoodRadius ∧
      ∀ ε : ℝ, 0 < ε →
        ∃ T : ℝ, 0 ≤ T ∧
          ∀ t, T ≤ t →
            ∀ x, IsWithinProfileSet neighborhoodRadius A x →
              IsWithinProfileSet ε A (semantics.trajectory x t)

/-- A replicator attractor is an inclusion-minimal attracting set, matching the
minimal-attractor convention used in the cited dynamical-systems work. -/
def ReplicatorSemantics.IsAttractor
    {Player : Type*} {Action : Player → Type*}
    [Fintype Player] [DecidableEq Player]
    [∀ i, Fintype (Action i)] [∀ i, DecidableEq (Action i)]
    {G : FiniteNormalFormGame Player Action}
    (semantics : ReplicatorSemantics Player Action G)
    (A : Set (MixedProfile Player Action)) : Prop :=
  semantics.IsAttractingSet A ∧
    ∀ B, B ⊆ A → semantics.IsAttractingSet B → A ⊆ B

/-- The collection of attractors is now derived from the replicator flow,
rather than supplied as unconstrained semantic data. -/
def ReplicatorSemantics.attractors
    {Player : Type*} {Action : Player → Type*}
    [Fintype Player] [DecidableEq Player]
    [∀ i, Fintype (Action i)] [∀ i, DecidableEq (Action i)]
    {G : FiniteNormalFormGame Player Action}
    (semantics : ReplicatorSemantics Player Action G) :
    Set (Set (MixedProfile Player Action)) :=
  {A | semantics.IsAttractor A}

/-- `A` is an attractor approached by the trajectory starting from `x`. -/
def ReplicatorSemantics.IsLimitAttractor
    {Player : Type*} {Action : Player → Type*}
    [Fintype Player] [DecidableEq Player]
    [∀ i, Fintype (Action i)] [∀ i, DecidableEq (Action i)]
    {G : FiniteNormalFormGame Player Action}
    (semantics : ReplicatorSemantics Player Action G)
    (x : MixedProfile Player Action)
    (A : Set (MixedProfile Player Action)) : Prop :=
  semantics.IsAttractor A ∧
    ∀ ε : ℝ, 0 < ε →
      ∃ T : ℝ, 0 ≤ T ∧
        ∀ t, T ≤ t →
          IsWithinProfileSet ε A (semantics.trajectory x t)

/-- The natural promise condition for exact limit prediction: the trajectory
from `x` approaches at least one replicator attractor.  This condition is
needed because a trajectory starting at, for example, an unstable stationary
point need not approach any inclusion-minimal attracting set. -/
def ReplicatorSemantics.HasLimitAttractor
    {Player : Type*} {Action : Player → Type*}
    [Fintype Player] [DecidableEq Player]
    [∀ i, Fintype (Action i)] [∀ i, DecidableEq (Action i)]
    {G : FiniteNormalFormGame Player Action}
    (semantics : ReplicatorSemantics Player Action G)
    (x : MixedProfile Player Action) : Prop :=
  ∃ A, semantics.IsLimitAttractor x A

/-! ## Canonical exact-real input words -/

/-- Structural normal-form encoding: dimensions first, followed by the full
payoff table in the fixed finite enumerations. -/
noncomputable def finiteGameWords
    {Player : Type*} {Action : Player → Type*}
    [Fintype Player] [DecidableEq Player]
    [∀ i, Fintype (Action i)] [∀ i, DecidableEq (Action i)]
    (G : FiniteNormalFormGame Player Action) : List UnitCostRAM.Word :=
  [.integer (Fintype.card Player),
    .integer (Fintype.card (∀ i, Action i))] ++
  (List.ofFn fun index : Fin (Fintype.card Player) =>
    .integer (Fintype.card (Action ((Fintype.equivFin Player).symm index)))) ++
  List.ofFn fun index : Fin (Fintype.card ((∀ i, Action i) × Player)) =>
    let pair := (Fintype.equivFin ((∀ i, Action i) × Player)).symm index
    .real (G.payoff pair.1 pair.2)

/-- Structural encoding of one mixed profile. -/
noncomputable def mixedProfileWords
    {Player : Type*} {Action : Player → Type*}
    [Fintype Player] [DecidableEq Player]
    [∀ i, Fintype (Action i)] [∀ i, DecidableEq (Action i)]
    (x : MixedProfile Player Action) : List UnitCostRAM.Word :=
  List.ofFn fun index : Fin (Fintype.card (Σ i, Action i)) =>
    let pair := (Fintype.equivFin (Σ i, Action i)).symm index
    .real ((x pair.1).val pair.2)

/-- Canonical input words for limit prediction. -/
noncomputable def finiteGameProfileWords
    {Player : Type*} {Action : Player → Type*}
    [Fintype Player] [DecidableEq Player]
    [∀ i, Fintype (Action i)] [∀ i, DecidableEq (Action i)]
    (input : FiniteNormalFormGame Player Action × MixedProfile Player Action) :
    List UnitCostRAM.Word :=
  .integer (finiteGameWords input.1).length ::
    finiteGameWords input.1 ++ mixedProfileWords input.2

/-- A finite representation language for descriptions of the complete
attractor collection of a game.

The original problem asks for a *description* of the attractors.  Returning
the mathematical object `Set (Set MixedProfile)` directly is not a finite
algorithmic output.  A representation therefore fixes, before the program is
chosen, lossless word encodings for games and description codes together with
the denotation of a code.  The adequacy of a proposed description language is
part of the mathematical answer and remains subject to ordinary review. -/
structure AttractorCollectionRepresentation
    (Player : Type*) (Action : Player → Type*)
    [Fintype Player] [DecidableEq Player]
    [∀ i, Fintype (Action i)] [∀ i, DecidableEq (Action i)] where
  Code : Type
  gameEncoding : UnitCostRAM.Encoding (FiniteNormalFormGame Player Action)
  gameEncoding_is_structural :
    ∀ game, gameEncoding.encode game = finiteGameWords game
  codeEncoding : UnitCostRAM.Encoding Code
  denotes : Code → Set (Set (MixedProfile Player Action))

/-- A finite representation language for one limit attractor. -/
structure LimitAttractorRepresentation
    (Player : Type*) (Action : Player → Type*)
    [Fintype Player] [DecidableEq Player]
    [∀ i, Fintype (Action i)] [∀ i, DecidableEq (Action i)] where
  Code : Type
  inputEncoding : UnitCostRAM.Encoding
    (FiniteNormalFormGame Player Action × MixedProfile Player Action)
  inputEncoding_is_structural :
    ∀ input, inputEncoding.encode input = finiteGameProfileWords input
  codeEncoding : UnitCostRAM.Encoding Code
  denotes : Code → Set (MixedProfile Player Action)

/-- Instruction-level algorithm for the first research goal. -/
structure AttractorComputationSolver
    (Player : Type*) (Action : Player → Type*)
    [Fintype Player] [DecidableEq Player]
    [∀ i, Fintype (Action i)] [∀ i, DecidableEq (Action i)]
    (semantics :
      (G : FiniteNormalFormGame Player Action) →
        ReplicatorSemantics Player Action G)
    (representation : AttractorCollectionRepresentation Player Action) where
  computeDescription :
    FiniteNormalFormGame Player Action → representation.Code
  implementation : StrictRAMComputableInPolyTime
    representation.gameEncoding representation.codeEncoding.dependent
    computeDescription
  attractors_correct :
    ∀ G, representation.denotes (computeDescription G) =
      (semantics G).attractors

/-- One fixed polynomial running-time bound for the concrete attractor
program. -/
def AttractorComputationSolver.RunsWithin
    {Player : Type*} {Action : Player → Type*}
    [Fintype Player] [DecidableEq Player]
    [∀ i, Fintype (Action i)] [∀ i, DecidableEq (Action i)]
    {semantics :
      (G : FiniteNormalFormGame Player Action) →
        ReplicatorSemantics Player Action G}
    {representation : AttractorCollectionRepresentation Player Action}
    (solver : AttractorComputationSolver Player Action semantics representation)
    (coefficient exponent : ℕ) : Prop :=
  ∀ game,
    solver.implementation.time.eval
        (representation.gameEncoding.size game) ≤
      coefficient * (representation.gameEncoding.size game + 1) ^ exponent

/-- Algorithm interface for the second research goal: predicting the limit
attractor from one initial real mixed profile. -/
structure LimitPredictionSolver
    (Player : Type*) (Action : Player → Type*)
    [Fintype Player] [DecidableEq Player]
    [∀ i, Fintype (Action i)] [∀ i, DecidableEq (Action i)]
    (semantics :
      (G : FiniteNormalFormGame Player Action) →
        ReplicatorSemantics Player Action G)
    (representation : LimitAttractorRepresentation Player Action) where
  predictDescription :
    FiniteNormalFormGame Player Action × MixedProfile Player Action →
      representation.Code
  implementation : StrictRAMComputableInPolyTime
    representation.inputEncoding representation.codeEncoding.dependent
    predictDescription
  /-- Exactness of limit prediction on its natural promise domain.  No
  uniqueness is assumed: whenever the trajectory approaches at least one
  attractor, any such limit attractor is a valid output. -/
  limit_correct :
    ∀ G x,
      (semantics G).HasLimitAttractor x →
        (semantics G).IsLimitAttractor x
          (representation.denotes (predictDescription (G, x)))

/-- One fixed polynomial running-time bound for the concrete limit-prediction
program. -/
def LimitPredictionSolver.RunsWithin
    {Player : Type*} {Action : Player → Type*}
    [Fintype Player] [DecidableEq Player]
    [∀ i, Fintype (Action i)] [∀ i, DecidableEq (Action i)]
    {semantics :
      (G : FiniteNormalFormGame Player Action) →
        ReplicatorSemantics Player Action G}
    {representation : LimitAttractorRepresentation Player Action}
    (solver : LimitPredictionSolver Player Action semantics representation)
    (coefficient exponent : ℕ) : Prop :=
  ∀ input,
    solver.implementation.time.eval
        (representation.inputEncoding.size input) ≤
      coefficient * (representation.inputEncoding.size input + 1) ^ exponent

/-- The first question from the Markdown. -/
def AttractorComputationStatement : Prop :=
  ∃ coefficient exponent : ℕ,
  ∃ program : UnitCostRAM.Program Empty,
    ∀ (Player : Type) [Fintype Player] [DecidableEq Player] [Nonempty Player],
      ∀ (Action : Player → Type)
        [∀ i, Fintype (Action i)] [∀ i, DecidableEq (Action i)]
        [∀ i, Nonempty (Action i)],
      ∃ representation : AttractorCollectionRepresentation Player Action,
      ∀ semantics :
          (G : FiniteNormalFormGame Player Action) →
            ReplicatorSemantics Player Action G,
        ∃ solver : AttractorComputationSolver Player Action semantics representation,
          solver.implementation.program = program ∧
            solver.RunsWithin coefficient exponent

/-- The second question from the Markdown, interpreted on the natural promise
domain where the requested limit attractor exists. -/
def LimitPredictionStatement : Prop :=
  ∃ coefficient exponent : ℕ,
  ∃ program : UnitCostRAM.Program Empty,
    ∀ (Player : Type) [Fintype Player] [DecidableEq Player] [Nonempty Player],
      ∀ (Action : Player → Type)
        [∀ i, Fintype (Action i)] [∀ i, DecidableEq (Action i)]
        [∀ i, Nonempty (Action i)],
      ∃ representation : LimitAttractorRepresentation Player Action,
      ∀ semantics :
          (G : FiniteNormalFormGame Player Action) →
            ReplicatorSemantics Player Action G,
        ∃ solver : LimitPredictionSolver Player Action semantics representation,
          solver.implementation.program = program ∧
            solver.RunsWithin coefficient exponent

/-- Research goal (1), kept logically independent. -/
theorem attractorComputation :
    answer(sorry) ↔ AttractorComputationStatement := by
  sorry

/-- Research goal (2), kept logically independent. -/
theorem limitPrediction :
    answer(sorry) ↔ LimitPredictionStatement := by
  sorry

end EconCSLib.OpenProblem.EconCSBench.MeaningOfAGame
