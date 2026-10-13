/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.Foundation.Utility.Lottery
import EconCSLib.OpenProblem.New.Complexity.All
import EconCSLib.OpenProblem.Util.Answer
import Lean.Elab.Tactic.NormCast
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Real.Basic

/-!
# 01. Bayesian security games
-/



section

/-!
## Bayesian simple security games

Real payoffs and mixed strategies follow Conitzer, "Computing Bayes-Nash equilibrium
in simple security games", Section 1. The defender covers exactly r targets. This is
simultaneous Bayesian Nash equilibrium, not Stackelberg commitment. Zero-prior types
have no ex-ante best-response constraint.
-/

open scoped BigOperators

namespace EconCSLib.OpenProblem.New.EconCSBench.BayesianSecurityGames

/-- One defender and a privately informed attacker, with real-valued payoffs. -/
structure BayesianSimpleSecurityGame
    (Target AttackerType : Type*) [Fintype Target] [DecidableEq Target]
    [Fintype AttackerType] where
  /-- Number of defensive resources. -/
  resources : ℕ
  /-- Resources cannot exceed the number of targets. -/
  resources_le_targets : resources ≤ Fintype.card Target
  /-- Prior over attacker types; zero probabilities are allowed. -/
  typePrior : Lottery ℝ AttackerType
  /-- Defender payoff when the attacked target is uncovered. -/
  defenderUncovered : Target → ℝ
  /-- Defender payoff when the attacked target is covered. -/
  defenderCovered : Target → ℝ
  /-- Type-dependent attacker payoff at an uncovered target. -/
  attackerUncovered : AttackerType → Target → ℝ
  /-- Type-dependent attacker payoff at a covered target. -/
  attackerCovered : AttackerType → Target → ℝ
  /-- The defender weakly prefers coverage of the attacked target. -/
  defender_prefers_coverage :
    ∀ t, defenderUncovered t ≤ defenderCovered t
  /-- The attacker weakly prefers an uncovered attacked target. -/
  attacker_prefers_uncovered :
    ∀ θ t, attackerCovered θ t ≤ attackerUncovered θ t

/-- A pure defender action covers exactly r targets. -/
abbrev DefenderPureStrategy
    {Target AttackerType : Type*} [Fintype Target] [DecidableEq Target]
    [Fintype AttackerType]
    (G : BayesianSimpleSecurityGame Target AttackerType) :=
  {S : Finset Target // S.card = G.resources}

/-- A distribution over subsets of exactly r targets. -/
abbrev DefenderStrategy
    {Target AttackerType : Type*} [Fintype Target] [DecidableEq Target]
    [Fintype AttackerType]
    (G : BayesianSimpleSecurityGame Target AttackerType) :=
  Lottery ℝ (DefenderPureStrategy G)

/-- A target distribution conditional on type, not on the defender's realized action. -/
abbrev AttackerStrategy
    (Target AttackerType : Type*) [Fintype Target] :=
  AttackerType → Lottery ℝ Target

/-- Ex-ante defender utility, weighted by the type prior. -/
noncomputable def defenderExpectedUtility
    {Target AttackerType : Type*} [Fintype Target] [DecidableEq Target]
    [Fintype AttackerType]
    (G : BayesianSimpleSecurityGame Target AttackerType)
    (defender : DefenderStrategy G)
    (attacker : AttackerStrategy Target AttackerType) : ℝ :=
  ∑ θ, G.typePrior.val θ *
    ∑ covered, defender.val covered *
      ∑ t, (attacker θ).val t *
        if t ∈ covered.1 then G.defenderCovered t else G.defenderUncovered t

/-- Defender utility from a pure deviation against the same attacker strategy. -/
noncomputable def defenderPureDeviationUtility
    {Target AttackerType : Type*} [Fintype Target] [DecidableEq Target]
    [Fintype AttackerType]
    (G : BayesianSimpleSecurityGame Target AttackerType)
    (covered : DefenderPureStrategy G)
    (attacker : AttackerStrategy Target AttackerType) : ℝ :=
  ∑ θ, G.typePrior.val θ *
    ∑ t, (attacker θ).val t *
      if t ∈ covered.1 then G.defenderCovered t else G.defenderUncovered t

/-- Type-conditional attacker utility; the prior is not multiplied twice. -/
noncomputable def attackerExpectedUtility
    {Target AttackerType : Type*} [Fintype Target] [DecidableEq Target]
    [Fintype AttackerType]
    (G : BayesianSimpleSecurityGame Target AttackerType)
    (defender : DefenderStrategy G)
    (attacker : AttackerStrategy Target AttackerType)
    (θ : AttackerType) : ℝ :=
  ∑ covered, defender.val covered *
    ∑ t, (attacker θ).val t *
      if t ∈ covered.1 then G.attackerCovered θ t else G.attackerUncovered θ t

/-- A type-specific target deviation against the same defender strategy. -/
noncomputable def attackerPureDeviationUtility
    {Target AttackerType : Type*} [Fintype Target] [DecidableEq Target]
    [Fintype AttackerType]
    (G : BayesianSimpleSecurityGame Target AttackerType)
    (defender : DefenderStrategy G)
    (θ : AttackerType) (target : Target) : ℝ :=
  ∑ covered, defender.val covered *
    if target ∈ covered.1 then G.attackerCovered θ target
    else G.attackerUncovered θ target

/-- Ex-ante Bayesian Nash equilibrium. Pure deviations suffice by linearity. Only
positive-prior types affect the attacker's ex-ante utility. -/
def IsBayesNashEquilibrium
    {Target AttackerType : Type*} [Fintype Target] [DecidableEq Target]
    [Fintype AttackerType]
    (G : BayesianSimpleSecurityGame Target AttackerType)
    (profile : DefenderStrategy G × AttackerStrategy Target AttackerType) : Prop :=
  (∀ covered : DefenderPureStrategy G,
      defenderPureDeviationUtility G covered profile.2 ≤
        defenderExpectedUtility G profile.1 profile.2) ∧
  (∀ θ target,
      0 < G.typePrior.val θ →
        attackerPureDeviationUtility G profile.1 θ target ≤
          attackerExpectedUtility G profile.1 profile.2 θ)

/-- Sparse output data. Normalization, valid defensive actions and equilibrium are checked
by the representation and solution predicates, not assumed here. -/
structure SparseEquilibriumProfile
    (targetCount attackerTypeCount : ℕ) where
  /-- Defender support subsets and their weights. -/
  defenderSupport : List (Finset (Fin targetCount) × ℝ)
  /-- Attack probabilities for each type and target. -/
  attackerProbability : Fin attackerTypeCount → Fin targetCount → ℝ

/-- The sparse data denote the same mixed profile. Repeated subsets have additive weights;
all weights are nonnegative. Lottery normalization is reused. -/
def SparseEquilibriumProfile.Represents
    {targetCount attackerTypeCount : ℕ}
    (sparse : SparseEquilibriumProfile targetCount attackerTypeCount)
    (G : BayesianSimpleSecurityGame
      (Fin targetCount) (Fin attackerTypeCount))
    (profile : DefenderStrategy G ×
      AttackerStrategy (Fin targetCount) (Fin attackerTypeCount)) : Prop :=
  (∀ entry ∈ sparse.defenderSupport,
      entry.1.card = G.resources ∧ 0 ≤ entry.2) ∧
    (∀ covered : DefenderPureStrategy G,
      profile.1.val covered =
        (sparse.defenderSupport.map (fun entry =>
          if entry.1 = covered.1 then entry.2 else 0)).sum) ∧
    (∀ θ t, (profile.2 θ).val t = sparse.attackerProbability θ t)

end EconCSLib.OpenProblem.New.EconCSBench.BayesianSecurityGames

end


section

/-!
## Full-real security-game inputs and outputs

Priors, payoffs and strategies remain real. Only finite cardinalities and the resource
count are natural numbers. This section specifies mathematical data.
-/
namespace EconCSLib.OpenProblem.New.EconCSBench.BayesianSecurityGames

/-- A valid real game with explicit dimensions and no embedded solution. -/
structure RealSecurityGame where
  targetCount : ℕ
  attackerTypeCount : ℕ
  targetCount_pos : 0 < targetCount
  attackerTypeCount_pos : 0 < attackerTypeCount
  game : BayesianSimpleSecurityGame (Fin targetCount) (Fin attackerTypeCount)

/-- Number of explicitly listed scalar entries, including dimensions and resources. -/
def RealSecurityGame.scalarCount (I : RealSecurityGame) : ℕ :=
  3 + I.attackerTypeCount + 2 * I.targetCount +
    2 * I.attackerTypeCount * I.targetCount

/-- Sparse equilibrium data with real weights. -/
abbrev RealSecurityGame.Output (I : RealSecurityGame) :=
  SparseEquilibriumProfile I.targetCount I.attackerTypeCount

/-- The output denotes an exact equilibrium of this input. No equilibrium is selected in
advance and no approximation is substituted. -/
def IsRealSecurityGameSolution (I : RealSecurityGame) (s : I.Output) : Prop :=
  ∃ profile : DefenderStrategy I.game ×
      AttackerStrategy (Fin I.targetCount) (Fin I.attackerTypeCount),
    s.Represents I.game profile ∧ IsBayesNashEquilibrium I.game profile

end EconCSLib.OpenProblem.New.EconCSBench.BayesianSecurityGames

end


section

/-!
## Security-game search with a concrete exact-real program

Public dimensions and real input arrays have fixed order. Sparse output is explicit
incidence bits and real probabilities; no semantic answer decoder is chosen by the
solver. A uniform finite program uses field arithmetic and comparisons only. The model
is exact-real unit cost.
-/
namespace EconCSLib.OpenProblem.New.EconCSBench.BayesianSecurityGames

/-- Public counts and resources; no payoff-dependent advice. -/
def RealSecurityGame.wordInput (I : RealSecurityGame) : List ℕ :=
  [I.targetCount, I.attackerTypeCount, I.game.resources]

/-- Prior, defender payoffs and attacker payoffs in type-major order. -/
def RealSecurityGame.realInput (I : RealSecurityGame) : List ℝ :=
  List.ofFn (fun θ => I.game.typePrior.val θ) ++
  List.ofFn I.game.defenderUncovered ++ List.ofFn I.game.defenderCovered ++
  (List.ofFn (fun θ => List.ofFn (I.game.attackerUncovered θ))).flatten ++
  (List.ofFn (fun θ => List.ofFn (I.game.attackerCovered θ))).flatten

/-- Dimensions, support count and explicit incidence bits of each defended set. -/
def SparseEquilibriumProfile.wordOutput {m k : ℕ}
    (profile : SparseEquilibriumProfile m k) : List ℕ :=
  [m, k, profile.defenderSupport.length] ++
    profile.defenderSupport.flatMap (fun entry =>
      List.ofFn (fun t : Fin m => if t ∈ entry.1 then 1 else 0))

/-- Support weights, followed by every attacker probability in type-major order. -/
def SparseEquilibriumProfile.realOutput {m k : ℕ}
    (profile : SparseEquilibriumProfile m k) : List ℝ :=
  profile.defenderSupport.map Prod.snd ++
    (List.ofFn (fun θ => List.ofFn (profile.attackerProbability θ))).flatten

/-- One fixed instruction program and width factor before every real instance. Its output
and scalar-count cost bound refer to the same concrete execution. -/
def BayesianSecurityGameExactRealRAMQuestion : Prop :=
  ∃ model : WordRAM.Model, ∃ program : ExactRealController.Program Empty,
    ∃ coefficient exponent : ℕ, ∀ I : RealSecurityGame,
      ∃ fuel : ℕ, ∃ profile : I.Output,
        let result := ExactRealController.runClosed
          (WordRAM.wordWidth model.widthFactor I.scalarCount)
          program fuel I.wordInput I.realInput
        result.termination = .halted profile.wordOutput profile.realOutput ∧
          IsRealSecurityGameSolution I profile ∧
          result.cost ≤ coefficient * (I.scalarCount + 1) ^ exponent

/-- The default full-real formulation uses the concrete exact-real machine. -/
abbrev BayesianSecurityGameQuestion := BayesianSecurityGameExactRealRAMQuestion

end EconCSLib.OpenProblem.New.EconCSBench.BayesianSecurityGames

end


/-!
## Questions and answers
-/

namespace EconCSLib.OpenProblem.New.EconCSBench.BayesianSecurityGames

/-- Existence of a polynomial-time exact-real solver for Bayesian security games. -/
theorem bayesianSecurityGames :
    answer(sorry) ↔ BayesianSecurityGameQuestion := by
  sorry

end EconCSLib.OpenProblem.New.EconCSBench.BayesianSecurityGames
