/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.OpenProblem.Util.Answer
import Mathlib.Combinatorics.Matroid.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Powerset
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Probability.Independence.Basic

/-!
# 10. Matroid-intersection prophet inequalities
-/



section

/-!
## Prophet inequalities for intersections of matroids

Sources: Feldman–Svensson–Zenklusen (2016), Section 1.1, and Saxena–Velusamy–Weinberg
(2023), Sections 2–3. The main almighty adversary observes both realized weights and
random coins: the minimum over orders is inside their joint expectation. Other arrival
conventions are named separately. Nonnegative expectations use extended integrals;
finite expected optimum is an explicit promise for ratio questions. There is no
computational-efficiency restriction.
-/

open scoped BigOperators ENNReal NNReal

namespace EconCSLib.OpenProblem.New.EconCSBench.MatroidIntersectionProphet

open MeasureTheory ProbabilityTheory

noncomputable section

/-- Finite nonnegative real weights; their expectations need not be finite. -/
abbrev WeightVector (n : ℕ) := Fin n → ℝ≥0

/-- A permutation maps arrival positions to element labels. -/
abbrev ArrivalOrder (n : ℕ) := Equiv.Perm (Fin n)

/-- Known matroids and independent weight distributions, chosen before weights are
realized. -/
structure ProphetInstance (n p : ℕ) where
  constraint : Fin p → Matroid (Fin n)
  constraint_ground : ∀ j, (constraint j).E = Set.univ
  prior : Measure (WeightVector n)
  probability : IsProbabilityMeasure prior
  independent : iIndepFun (fun e (w : WeightVector n) => w e) prior

/-- A feasible set is independent in every matroid; it need not be a base. -/
def ProphetInstance.Feasible {n p : ℕ} (problem : ProphetInstance n p)
    (S : Finset (Fin n)) : Prop :=
  ∀ j, (problem.constraint j).Indep (S : Set (Fin n))

/-- Total selected weight, valued in extended nonnegative reals for integration. -/
def setWeight {n : ℕ} (w : WeightVector n) (S : Finset (Fin n)) : ℝ≥0∞ :=
  ∑ e ∈ S, (w e : ℝ≥0∞)

/-- The revealed prefix includes the current item, which must be accepted or rejected
immediately. -/
def revealedSet {n : ℕ} (order : ArrivalOrder n) (t : Fin n) : Finset (Fin n) :=
  (Finset.univ.filter fun s => s ≤ t).image order

/-- Equality of revealed labels and values only, without comparing future observations. -/
def SameHistoryThrough {n : ℕ} (w w' : WeightVector n)
    (order order' : ArrivalOrder n) (t : Fin n) : Prop :=
  ∀ s : Fin n, s ≤ t →
    order s = order' s ∧ w (order s) = w' (order' s)

/-- An online strategy with an arbitrary independent random seed. Final feasibility also
ensures prefix feasibility. -/
structure ProphetAlgorithm {n p : ℕ} (problem : ProphetInstance n p) where
  Seed : Type
  seedSpace : MeasurableSpace Seed
  seedLaw : @Measure Seed seedSpace
  seed_probability : letI := seedSpace; IsProbabilityMeasure seedLaw
  outcome : WeightVector n → Seed → ArrivalOrder n → Finset (Fin n)
  feasible : ∀ w seed order, problem.Feasible (outcome w seed order)
  online : ∀ w w' seed order order' t,
    SameHistoryThrough w w' order order' t →
      outcome w seed order ∩ revealedSet order t =
        outcome w' seed order' ∩ revealedSet order' t
  /-- Output events are jointly measurable in weights and seed. -/
  outcome_measurable : letI := seedSpace
    ∀ order S, MeasurableSet
      {z : WeightVector n × Seed | outcome z.1 z.2 order = S}

/-- Distinct arrival-information conventions; almighty observes both weights and random
coins. -/
inductive ArrivalModel
  | almighty
  | prophet
  | fixedAdversarial
  | uniformRandom
  | chosenBeforeValues
  deriving DecidableEq, Repr

/-- The placement of order minimization relative to expectations specifies adversarial
information. Chosen-before-values is not adaptive free order. -/
def prophetAlgorithmValue {n p : ℕ} {problem : ProphetInstance n p}
    (mode : ArrivalModel) (algorithm : ProphetAlgorithm problem) : ℝ≥0∞ :=
  letI := algorithm.seedSpace
  letI := algorithm.seed_probability
  letI := problem.probability
  let reward := fun (z : WeightVector n × algorithm.Seed) (order : ArrivalOrder n) =>
    setWeight z.1 (algorithm.outcome z.1 z.2 order)
  let joint := problem.prior.prod algorithm.seedLaw
  match mode with
  | .almighty => ∫⁻ z, ⨅ order, reward z order ∂joint
  | .prophet =>
      ∫⁻ w, (⨅ order, ∫⁻ seed, reward (w, seed) order ∂algorithm.seedLaw)
        ∂problem.prior
  | .fixedAdversarial => ⨅ order, ∫⁻ z, reward z order ∂joint
  | .uniformRandom =>
      (∑ order : ArrivalOrder n, ∫⁻ z, reward z order ∂joint) /
        (Fintype.card (ArrivalOrder n) : ℝ≥0∞)
  | .chosenBeforeValues => ⨆ order, ∫⁻ z, reward z order ∂joint

/-- The prophet sees all weights before choosing a feasible set; maximization is inside
expectation. -/
def prophetOPT {n p : ℕ} (problem : ProphetInstance n p) : ℝ≥0∞ :=
  ∫⁻ w, (⨆ S : {S : Finset (Fin n) // problem.Feasible S}, setWeight w S.1)
    ∂problem.prior

/-- Explicit finite-optimum promise; zero optimum and distributions with infinite support
are allowed. -/
def HasFiniteProphetValue {n p : ℕ} (problem : ProphetInstance n p) : Prop :=
  prophetOPT problem < ⊤

/-- Proper colorings of disjoint cliques, with a color collision for every pair from
distinct cliques. The palette does not restrict general colorings. -/
def CliqueFactorProductDimensionAtMost (ell r k : ℕ) : Prop :=
  ∃ color : Fin k → (Fin r × Fin ell) → Fin (r * ell),
    (∀ c row a b, a ≠ b →
      color c (row, a) ≠ color c (row, b)) ∧
    (∀ row row' a b, row ≠ row' →
      ∃ c, color c (row, a) = color c (row', b))

end

end EconCSLib.OpenProblem.New.EconCSBench.MatroidIntersectionProphet

end


section

/-!
## Two independent quantitative prophet questions

The approximation factor is OPT/ALG, the reciprocal of competitive ratio. Constants
and thresholds are chosen before dimensions and instances. The main arrival model is
almighty; the other explicitly named models remain separate. The product-dimension
target is independent of the prophet target. Candidate rates are parameters requiring
substantive mathematical descriptions and proofs, not names for the extremal quantity
itself. No running-time claim is made.
-/

open scoped ENNReal

namespace EconCSLib.OpenProblem.New.EconCSBench.MatroidIntersectionProphet

/-- An O(factor p) approximation: the algorithm may depend on the known instance, but not
on realized weights or seed. -/
def IsAchievableProphetApproximationRate
    (mode : ArrivalModel) (factor : ℕ → ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∃ p₀ : ℕ, 1 ≤ p₀ ∧
      ∀ p : ℕ, p₀ ≤ p →
        1 ≤ factor p ∧
        ∀ n : ℕ, ∀ problem : ProphetInstance n p,
          HasFiniteProphetValue problem →
          ∃ algorithm : ProphetAlgorithm problem,
            prophetOPT problem ≤
              ENNReal.ofReal (C * factor p) * prophetAlgorithmValue mode algorithm

/-- An Omega(factor p) lower bound: a positive, finite-optimum instance defeats every
algorithm. The instance precedes the algorithm. -/
def IsNecessaryProphetApproximationRate
    (mode : ArrivalModel) (factor : ℕ → ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∃ p₀ : ℕ, 1 ≤ p₀ ∧
      ∀ p : ℕ, p₀ ≤ p →
        1 ≤ factor p ∧
        ∃ n : ℕ, ∃ problem : ProphetInstance n p,
          HasFiniteProphetValue problem ∧ 0 < prophetOPT problem ∧
          ∀ algorithm : ProphetAlgorithm problem,
            ENNReal.ofReal (factor p) * prophetAlgorithmValue mode algorithm ≤
              ENNReal.ofReal C * prophetOPT problem

/-- Matching achievable and necessary approximation rates for a specified arrival model. -/
def IsOptimalProphetApproximationRate
    (mode : ArrivalModel) (factor : ℕ → ℝ) : Prop :=
  IsAchievableProphetApproximationRate mode factor ∧
    IsNecessaryProphetApproximationRate mode factor

/-- Theta growth of Q(q,q^q), over all sufficiently large natural q, with constants chosen
before q. -/
def IsProductDimensionAsymptoticRate (rate : ℕ → ℝ) : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∃ q₀ : ℕ, 2 ≤ q₀ ∧
      ∀ q : ℕ, q₀ ≤ q →
        0 < rate q ∧
        (∃ k : ℕ,
          CliqueFactorProductDimensionAtMost q (q ^ q) k ∧
            (k : ℝ) ≤ C * rate q) ∧
        (∀ k : ℕ,
          CliqueFactorProductDimensionAtMost q (q ^ q) k →
            c * rate q ≤ (k : ℝ))

/-- The main omniscient-adversary question, including knowledge of random coins [FSZ,
Section 1.1]. -/
def AlmightyProphetApproximationRateQuestion (factor : ℕ → ℝ) : Prop :=
  IsOptimalProphetApproximationRate .almighty factor

end EconCSLib.OpenProblem.New.EconCSBench.MatroidIntersectionProphet

end


/-!
## Questions and answers
-/

namespace EconCSLib.OpenProblem.New.EconCSBench.MatroidIntersectionProphet

/-- Supply the optimal asymptotic approximation rate against the almighty order. -/
theorem optimalProphetRate :
    AlmightyProphetApproximationRateQuestion (answer(sorry)) := by
  sorry

/-- Independent asymptotic product-dimension rate. -/
theorem productDimensionRate :
    IsProductDimensionAsymptoticRate (answer(sorry)) := by
  sorry

end EconCSLib.OpenProblem.New.EconCSBench.MatroidIntersectionProphet
