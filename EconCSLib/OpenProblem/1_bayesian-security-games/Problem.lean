/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.OpenProblem.EconCSBench.Common

open scoped BigOperators

namespace EconCSLib.OpenProblem.EconCSBench.BayesianSecurityGames

/-- A Bayesian simple security game with one defender and one typed attacker. -/
structure BayesianSimpleSecurityGame
    (Target AttackerType : Type*) [Fintype Target] [DecidableEq Target]
    [Fintype AttackerType] where
  /-- Number of defensive resources. -/
  resources : ℕ
  /-- There are enough targets on which to place all resources. -/
  resources_le_targets : resources ≤ Fintype.card Target
  /-- Prior distribution of the attacker's type. -/
  typePrior : Lottery ℝ AttackerType
  /-- Defender utility when an attacked target is uncovered. -/
  defenderUncovered : Target → ℝ
  /-- Defender utility when an attacked target is covered. -/
  defenderCovered : Target → ℝ
  /-- Attacker utility when the attacked target is uncovered. -/
  attackerUncovered : AttackerType → Target → ℝ
  /-- Attacker utility when the attacked target is covered. -/
  attackerCovered : AttackerType → Target → ℝ
  /-- The defender weakly prefers coverage of an attacked target. -/
  defender_prefers_coverage :
    ∀ t, defenderUncovered t ≤ defenderCovered t
  /-- Every attacker type weakly prefers an uncovered attacked target. -/
  attacker_prefers_uncovered :
    ∀ θ t, attackerCovered θ t ≤ attackerUncovered θ t

/-- A pure defender strategy covers exactly the available number of targets. -/
abbrev DefenderPureStrategy
    {Target AttackerType : Type*} [Fintype Target] [DecidableEq Target]
    [Fintype AttackerType]
    (G : BayesianSimpleSecurityGame Target AttackerType) :=
  {S : Finset Target // S.card = G.resources}

/-- A mixed defender strategy. -/
abbrev DefenderStrategy
    {Target AttackerType : Type*} [Fintype Target] [DecidableEq Target]
    [Fintype AttackerType]
    (G : BayesianSimpleSecurityGame Target AttackerType) :=
  Lottery ℝ (DefenderPureStrategy G)

/-- A behavioral attacker strategy chooses a target distribution after learning
the attacker's type. -/
abbrev AttackerStrategy
    (Target AttackerType : Type*) [Fintype Target] :=
  AttackerType → Lottery ℝ Target

/-- Defender expected utility at a mixed-strategy profile. -/
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

/-- Defender utility after deviating to a pure coverage set. -/
noncomputable def defenderPureDeviationUtility
    {Target AttackerType : Type*} [Fintype Target] [DecidableEq Target]
    [Fintype AttackerType]
    (G : BayesianSimpleSecurityGame Target AttackerType)
    (covered : DefenderPureStrategy G)
    (attacker : AttackerStrategy Target AttackerType) : ℝ :=
  ∑ θ, G.typePrior.val θ *
    ∑ t, (attacker θ).val t *
      if t ∈ covered.1 then G.defenderCovered t else G.defenderUncovered t

/-- Expected utility of one attacker type at a mixed-strategy profile. -/
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

/-- Utility of one attacker type after deviating to a pure target. -/
noncomputable def attackerPureDeviationUtility
    {Target AttackerType : Type*} [Fintype Target] [DecidableEq Target]
    [Fintype AttackerType]
    (G : BayesianSimpleSecurityGame Target AttackerType)
    (defender : DefenderStrategy G)
    (θ : AttackerType) (target : Target) : ℝ :=
  ∑ covered, defender.val covered *
    if target ∈ covered.1 then G.attackerCovered θ target
    else G.attackerUncovered θ target

/-- Bayes-Nash equilibrium: neither the defender nor any realized attacker type
can gain from a unilateral pure deviation. -/
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

/-! ## Fixed structural representation and strict search complexity -/

/-- Canonical compact word representation of a security-game table.  The
header stores the two dimensions and the resource count.  It is followed, in
`Fin` order, by the prior, the two defender payoff vectors, and the two
attacker payoff matrices.  Thus the representation has one word per scalar
table entry; no finite object is packed into one exact-real word. -/
def securityGameInputWords
    {targetCount attackerTypeCount : ℕ}
    (G : BayesianSimpleSecurityGame
      (Fin targetCount) (Fin attackerTypeCount)) : List UnitCostRAM.Word :=
  [.integer targetCount, .integer attackerTypeCount, .integer G.resources] ++
    List.ofFn (fun θ : Fin attackerTypeCount => .real (G.typePrior.val θ)) ++
    List.ofFn (fun t : Fin targetCount => .real (G.defenderUncovered t)) ++
    List.ofFn (fun t : Fin targetCount => .real (G.defenderCovered t)) ++
    (List.ofFn (fun θ : Fin attackerTypeCount =>
      List.ofFn (fun t : Fin targetCount =>
        .real (G.attackerUncovered θ t)))).flatten ++
    (List.ofFn (fun θ : Fin attackerTypeCount =>
      List.ofFn (fun t : Fin targetCount =>
        .real (G.attackerCovered θ t)))).flatten

/-- A sparse finite representation of an equilibrium profile.  Listing only
the defender's support avoids imposing an exponentially long dense vector
over all resource subsets.  Attacker behavior is a compact type-by-target
table. -/
structure SparseEquilibriumProfile
    (targetCount attackerTypeCount : ℕ) where
  /-- Defender support entries and their probabilities. -/
  defenderSupport : List (Finset (Fin targetCount) × ℝ)
  /-- Behavioral attack probability for every type and target. -/
  attackerProbability : Fin attackerTypeCount → Fin targetCount → ℝ

/-- Canonical structural words for a sparse equilibrium.  Every support set
is written as its full Boolean incidence vector, so even a support entry
cannot hide a large subset in one word. -/
def sparseEquilibriumWords
    {targetCount attackerTypeCount : ℕ}
    (profile : SparseEquilibriumProfile targetCount attackerTypeCount) :
    List UnitCostRAM.Word :=
  [.integer targetCount, .integer attackerTypeCount,
      .integer profile.defenderSupport.length] ++
    profile.defenderSupport.flatMap (fun entry =>
      .real entry.2 ::
        List.ofFn (fun t : Fin targetCount => .bit (decide (t ∈ entry.1)))) ++
    (List.ofFn (fun θ : Fin attackerTypeCount =>
      List.ofFn (fun t : Fin targetCount =>
        .real (profile.attackerProbability θ t)))).flatten

/-- A sparse table represents the same mixed strategies as a semantic
profile.  Duplicate support entries are harmless: their nonnegative weights
are added. -/
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

/-- The canonical input promise: the words are exactly the structural table
of a nonempty finite Bayesian security game. -/
def IsCanonicalSecurityGameInput (input : List UnitCostRAM.Word) : Prop :=
  ∃ targetCount attackerTypeCount : ℕ,
    0 < targetCount ∧ 0 < attackerTypeCount ∧
      ∃ G : BayesianSimpleSecurityGame
          (Fin targetCount) (Fin attackerTypeCount),
        securityGameInputWords G = input

/-- The fixed encoded search relation.  Its output is a sparse strategy table
representing an actual Bayes--Nash equilibrium of the encoded game. -/
def IsCanonicalSecurityGameEquilibrium
    (input output : List UnitCostRAM.Word) : Prop :=
  ∃ targetCount attackerTypeCount : ℕ,
    ∃ (_ : 0 < targetCount) (_ : 0 < attackerTypeCount),
      ∃ (G : BayesianSimpleSecurityGame
          (Fin targetCount) (Fin attackerTypeCount))
        (sparse : SparseEquilibriumProfile targetCount attackerTypeCount)
        (profile : DefenderStrategy G ×
          AttackerStrategy (Fin targetCount) (Fin attackerTypeCount)),
        securityGameInputWords G = input ∧
          sparseEquilibriumWords sparse = output ∧
          sparse.Represents G profile ∧
          IsBayesNashEquilibrium G profile

/-- Identity encoding of already canonical RAM words. -/
def securityGameWordEncoding :
    UnitCostRAM.Encoding (List UnitCostRAM.Word) where
  encode := id
  decode := some
  decode_encode _ := rfl

/-- Open-problem statement: one finite strict real-RAM program solves every
encoded Bayesian simple security game in time bounded by one explicit
polynomial in the full compact table length. -/
def BayesianSecurityGamePolynomialEquilibriumStatement : Prop :=
  SearchRunsInFixedEncodingStrictRAMPolynomialTimeOn
    securityGameWordEncoding
    securityGameWordEncoding.dependent
    IsCanonicalSecurityGameInput
    IsCanonicalSecurityGameEquilibrium

/-- English version: "Can a Bayes-Nash equilibrium of every Bayesian simple
security game be computed in polynomial time?" -/
theorem bayesianSecurityGamePolynomialEquilibrium :
    answer(sorry) ↔ BayesianSecurityGamePolynomialEquilibriumStatement := by
  sorry

end EconCSLib.OpenProblem.EconCSBench.BayesianSecurityGames
