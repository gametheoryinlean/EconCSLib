/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.OpenProblem.EconCSBench.Common
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Probability.Independence.Basic

open scoped BigOperators

namespace EconCSLib.OpenProblem.EconCSBench.MatroidIntersectionProphet

open MeasureTheory ProbabilityTheory
open Filter

/-- A finite prophet-inequality instance constrained by the intersection of
`p` matroids. -/
structure ProphetInstance (n p : ℕ) where
  /-- The `p` matroid constraints. -/
  constraint : Fin p → Matroid (Fin n)
  /-- Every matroid has the advertised `n`-element ground set. -/
  constraint_ground : ∀ j, (constraint j).E = Set.univ
  /-- Joint law of the real-valued element weights. -/
  prior : Measure (Fin n → ℝ)
  /-- The joint law has total mass one. -/
  probability : IsProbabilityMeasure prior
  /-- Element values are mutually independent. -/
  independent : iIndepFun (fun e ω => ω e) prior
  /-- Values are nonnegative almost surely. -/
  nonnegative : ∀ᵐ ω ∂prior, ∀ e, 0 ≤ ω e
  /-- Each coordinate has finite expectation, making every finite feasible
  welfare and the hindsight optimum integrable. -/
  value_integrable : ∀ e, Integrable (fun ω => ω e) prior

/-- An arrival-order rule, including fixed order, random order, and an
omniscient adversary whose order may depend measurably on all realized values. -/
structure ProphetArrivalRule (n : ℕ) where
  /-- Distribution of arrival orders after the value realization is fixed.
  Constant kernels represent fixed or random order; a realization-dependent
  point mass represents an omniscient adversary. -/
  arrivalDist :
    (Fin n → ℝ) → Lottery ℝ (Equiv.Perm (Fin n))
  /-- Every arrival-order probability is measurable in the realized values;
  otherwise the expected online value need not even be a defined random
  variable in the intended probabilistic sense. -/
  arrival_measurable :
    ∀ order, Measurable (fun ω => (arrivalDist ω).val order)

/-- Feasibility in the intersection of all matroids. -/
def ProphetInstance.Feasible
    {n p : ℕ} (problem : ProphetInstance n p)
    (S : Finset (Fin n)) : Prop :=
  ∀ j, (problem.constraint j).Indep (S : Set (Fin n))

/-- Elements revealed through time `t` in an arrival order. -/
def prophetRevealedSet
    {n : ℕ} (order : Equiv.Perm (Fin n)) (t : Fin n) : Finset (Fin n) :=
  (Finset.univ.filter fun s => s ≤ t).image order

/-- Probability of exactly the accepted prefix `A`. -/
noncomputable def selectedPrefixProbability
    {n : ℕ} (L : Lottery ℝ (Finset (Fin n)))
    (seen A : Finset (Fin n)) : ℝ :=
  ∑ S, L.val S * if S ∩ seen = A then 1 else 0

/-- Two prophet inputs reveal the same values through time `t`. -/
def SameProphetHistory
    {n p : ℕ} (_problem : ProphetInstance n p)
    (ω ω' : Fin n → ℝ) (order order' : Equiv.Perm (Fin n))
    (t : Fin n) : Prop :=
  ∀ s, s ≤ t →
    order s = order' s ∧
      ω (order s) = ω' (order' s)

/-- An online selection rule.  `online` is an abstract non-anticipation
condition; it does not impose a computational-complexity model. -/
structure ProphetAlgorithm {n p : ℕ} (problem : ProphetInstance n p) where
  /-- Selected-set distribution for each scenario and order. -/
  outcome :
    (Fin n → ℝ) → Equiv.Perm (Fin n) → Lottery ℝ (Finset (Fin n))
  /-- Selected sets in the support satisfy every matroid. -/
  feasible :
    ∀ ω order S, 0 < (outcome ω order).val S → problem.Feasible S
  /-- The joint law of all decisions through time `t` depends only on the
  values and identities revealed through `t`. -/
  online :
    ∀ ω ω' order order' t,
      SameProphetHistory problem ω ω' order order' t →
        ∀ A,
          selectedPrefixProbability (outcome ω order)
              (prophetRevealedSet order t) A =
            selectedPrefixProbability (outcome ω' order')
              (prophetRevealedSet order' t) A
  /-- The induced expected online welfare is integrable under the value prior. -/
  welfare_integrable :
    ∀ arrival : ProphetArrivalRule n,
      Integrable
        (fun ω =>
          Lottery.expectedValue (arrival.arrivalDist ω) fun order =>
            Lottery.expectedValue (outcome ω order) fun S =>
              ∑ e ∈ S, ω e)
        problem.prior

/-- Expected online welfare under the value distribution and the instance's
possibly realization-dependent arrival-order kernel. -/
noncomputable def prophetAlgorithmValue
    {n p : ℕ} {problem : ProphetInstance n p}
    (arrival : ProphetArrivalRule n)
    (algorithm : ProphetAlgorithm problem) : ℝ :=
  ∫ ω,
    Lottery.expectedValue (arrival.arrivalDist ω) fun order =>
      Lottery.expectedValue (algorithm.outcome ω order) fun S =>
        ∑ e ∈ S, ω e ∂problem.prior

/-- Expected offline prophet welfare. -/
noncomputable def prophetOPT
    {n p : ℕ} (problem : ProphetInstance n p) : ℝ :=
  ∫ ω,
    ⨆ S : {S : Finset (Fin n) // problem.Feasible S},
      ∑ e ∈ S.1, ω e ∂problem.prior

/-- An approximation-factor rate is achievable, up to a universal
multiplicative constant, on every sufficiently large
`p`-matroid-intersection instance.  The cutoff prevents an asymptotic answer
from being constrained by finitely many irrelevant small values of `p`. -/
def IsAchievableProphetApproximationRate (factor : ℕ → ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∃ p₀ : ℕ, 1 ≤ p₀ ∧
    ∀ p : ℕ, p₀ ≤ p →
      1 ≤ factor p ∧
      ∀ n : ℕ, ∀ problem : ProphetInstance n p,
        ∃ algorithm : ProphetAlgorithm problem,
          ∀ arrival : ProphetArrivalRule n,
            prophetOPT problem ≤
              C * factor p * prophetAlgorithmValue arrival algorithm

/-- A matching lower-bound rate: for every number of matroids there is a hard
instance, once `p` is sufficiently large, on which no online algorithm
improves that rate by more than a universal constant. -/
def IsNecessaryProphetApproximationRate (factor : ℕ → ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∃ p₀ : ℕ, 1 ≤ p₀ ∧
    ∀ p : ℕ, p₀ ≤ p →
      ∃ n : ℕ, ∃ problem : ProphetInstance n p,
        0 < prophetOPT problem ∧
          ∀ algorithm : ProphetAlgorithm problem,
            ∃ arrival : ProphetArrivalRule n,
              prophetAlgorithmValue arrival algorithm ≤
                (C / factor p) * prophetOPT problem

/-- `factor` gives matching asymptotic upper and lower approximation rates. -/
def IsOptimalProphetApproximationRate (factor : ℕ → ℝ) : Prop :=
  IsAchievableProphetApproximationRate factor ∧
    IsNecessaryProphetApproximationRate factor

/-- `k` proper colorings witness product dimension at most `k` for `r`
disjoint cliques of size `ell`. -/
def CliqueFactorProductDimensionAtMost (ell r k : ℕ) : Prop :=
  ∃ color : Fin k → (Fin r × Fin ell) → Fin (r * ell),
    (∀ c row a b, a ≠ b →
      color c (row, a) ≠ color c (row, b)) ∧
    (∀ row row' a b, row ≠ row' →
      ∃ c, color c (row, a) = color c (row', b))

/-- Exact product dimension, expressed without guessing a linear endpoint. -/
def CliqueFactorProductDimensionExactly (ell r k : ℕ) : Prop :=
  CliqueFactorProductDimensionAtMost ell r k ∧
    ∀ j : ℕ, j < k → ¬ CliqueFactorProductDimensionAtMost ell r j

/-- A real-valued rate is asymptotically equal to the exact product dimension
of `q^q` disjoint `q`-cliques.  This asks only for the asymptotics requested in
the Markdown, not the strictly stronger exact value at every `q`. -/
def IsProductDimensionAsymptoticRate (rate : ℕ → ℝ) : Prop :=
  (∀ q : ℕ, 2 ≤ q → 0 ≤ rate q) ∧
  ∃ exact : ℕ → ℕ,
    (∀ q : ℕ, 2 ≤ q →
      CliqueFactorProductDimensionExactly q (q ^ q) (exact q)) ∧
    (fun q => (exact q : ℝ)) =Θ[atTop] rate

/-- The two function-valued asymptotic answers requested by the Markdown. -/
structure MatroidIntersectionProphetResearchAnswer where
  prophetApproximationFactor : ℕ → ℝ
  productDimensionRate : ℕ → ℝ

/-- Correctness of proposed asymptotic rates for both research goals. -/
def IsCorrectMatroidIntersectionProphetResearchAnswer
    (result : MatroidIntersectionProphetResearchAnswer) : Prop :=
  IsOptimalProphetApproximationRate
      result.prophetApproximationFactor ∧
    IsProductDimensionAsymptoticRate result.productDimensionRate

/-- Open-problem statement: there are two rate functions that correctly answer
both quantitative research goals. -/
def MatroidIntersectionProphetResearchStatement : Prop :=
  ∃ result : MatroidIntersectionProphetResearchAnswer,
    IsCorrectMatroidIntersectionProphetResearchAnswer result

/-- Typed open-problem answer.  The replacement must explicitly identify both
rate functions rather than reuse their extremal definitions. -/
theorem matroidIntersectionProphetResearch :
    IsCorrectMatroidIntersectionProphetResearchAnswer (answer(sorry)) := by
  sorry

end EconCSLib.OpenProblem.EconCSBench.MatroidIntersectionProphet
