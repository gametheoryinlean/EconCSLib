/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.OpenProblem.New.RevelationGapPublicBudgetWelfare.Problem

/-!
# RevelationGapPublicBudgetWelfare: supporting material

Auxiliary definitions and lemmas for the problem statement.
-/

section

/-!
## Welfare with a common public budget

[FH18, Definition 2.1 and Section 5] distinguishes the priors used to assess
performance from those on which the fixed mechanism must be truthful. Values lie in a
bounded interval, payments are nonnegative and hard-budget feasible. Random
allocations and deterministic conditional expected payments represent risk-neutral
outcomes, without imposing outcome-by-outcome IR.
-/

namespace EconCSLib.OpenProblem.New.EconCSBench.RevelationGapPublicBudget

open MeasureTheory
open scoped BigOperators
noncomputable section

/-- Finite utility; admissibility separately enforces the hard budget at each report
profile. -/
def PublicBudgetOutcome.utility {n : ℕ} (A : PublicBudgetOutcome n)
    (v : ℝ) (reports : Fin n → ℝ) (i : Fin n) : ℝ :=
  v * A.allocation reports i - A.payment reports i

/-- Hard-budget feasibility on every nonnegative report profile. -/
def PublicBudgetOutcome.IsBudgetFeasible {n : ℕ}
    (A : PublicBudgetOutcome n) (B : ℝ) : Prop :=
  ∀ reports, (∀ i, 0 ≤ reports i) → ∀ i, A.payment reports i ≤ B

/-- The prior-informed benchmark only needs feasibility on its published type interval. -/
def PublicBudgetOutcome.IsBudgetFeasibleOn {n : ℕ}
    (A : PublicBudgetOutcome n) (B h : ℝ) : Prop :=
  ∀ reports, (∀ i, reports i ∈ Set.Icc 0 h) →
    ∀ i, A.payment reports i ≤ B

/-- DSIC is a separate predicate; it is not imposed on every revelation mechanism. -/
def PublicBudgetOutcome.IsDSIC {n : ℕ} (A : PublicBudgetOutcome n) : Prop :=
  ∀ reports, (∀ j, 0 ≤ reports j) → ∀ i fake, 0 ≤ fake →
    A.utility (reports i) (Function.update reports i fake) i ≤
      A.utility (reports i) reports i

/-- Individual rationality in expectation over the allocation lottery at every report
profile. -/
def PublicBudgetOutcome.IsExPostIR {n : ℕ}
    (A : PublicBudgetOutcome n) : Prop :=
  ∀ reports, (∀ j, 0 ≤ reports j) →
    ∀ i, 0 ≤ A.utility (reports i) reports i

/-- Prior-informed DSIC on the published type interval, including all opponents' reports
in that interval rather than only almost every profile. -/
def PublicBudgetOutcome.IsDSICOn {n : ℕ} (A : PublicBudgetOutcome n) (h : ℝ) : Prop :=
  ∀ reports, (∀ j, reports j ∈ Set.Icc 0 h) →
    ∀ i fake, fake ∈ Set.Icc 0 h →
      A.utility (reports i) (Function.update reports i fake) i ≤
        A.utility (reports i) reports i

/-- Ex-post IR on the same interval, before the allocation lottery. -/
def PublicBudgetOutcome.IsExPostIROn {n : ℕ}
    (A : PublicBudgetOutcome n) (h : ℝ) : Prop :=
  ∀ reports, (∀ j, reports j ∈ Set.Icc 0 h) →
    ∀ i, 0 ≤ A.utility (reports i) reports i

/-- Global DSIC implies its interval restriction. -/
theorem PublicBudgetOutcome.IsDSIC.on {n : ℕ} {A : PublicBudgetOutcome n}
    (hA : A.IsDSIC) (h : ℝ) : A.IsDSICOn h := by
  intro reports hreports i fake hfake
  exact hA reports (fun j => (hreports j).1) i fake hfake.1

/-- Global ex-post IR implies its interval restriction. -/
theorem PublicBudgetOutcome.IsExPostIR.on {n : ℕ} {A : PublicBudgetOutcome n}
    (hA : A.IsExPostIR) (h : ℝ) : A.IsExPostIROn h := by
  intro reports hreports i
  exact hA reports (fun j => (hreports j).1) i

/-- Average only over opponents: the own coordinate is overwritten, and its probability
measure has total mass one. -/
def PublicBudgetOutcome.interimUtility {n : ℕ} (A : PublicBudgetOutcome n)
    (F : PublicBudgetDistribution) (i : Fin n) (v report : ℝ) : ℝ :=
  ∫ values, A.utility v (Function.update values i report) i
    ∂iidValueProfileMeasure F n

/-- BIC on every true value and report in the prior type interval. -/
def PublicBudgetOutcome.IsBIC {n : ℕ} (A : PublicBudgetOutcome n)
    (F : PublicBudgetDistribution) : Prop :=
  ∀ i v report, v ∈ Set.Icc 0 F.supportUpper →
    report ∈ Set.Icc 0 F.supportUpper →
      A.interimUtility F i v report ≤ A.interimUtility F i v v

/-- Interim IR on the same type domain as BIC. -/
def PublicBudgetOutcome.IsInterimIR {n : ℕ} (A : PublicBudgetOutcome n)
    (F : PublicBudgetDistribution) : Prop :=
  ∀ i v, v ∈ Set.Icc 0 F.supportUpper →
    0 ≤ A.interimUtility F i v v

/-- A prior-informed Bayesian benchmark is BIC, interim IR, and budget feasible. Bounded
support and measurable bounded outcomes ensure the expectations exist. -/
def PublicBudgetOutcome.IsBayesianAdmissible {n : ℕ}
    (A : PublicBudgetOutcome n) (B : ℝ) (F : PublicBudgetDistribution) : Prop :=
  A.IsBudgetFeasibleOn B F.supportUpper ∧ A.IsBIC F ∧ A.IsInterimIR F

/-- The DSIC benchmark in FH18 Section 4 uses ex-post IR and hard budgets on the same type
interval; no prior-independent constraint is imposed. -/
def PublicBudgetOutcome.IsDSICAdmissible {n : ℕ}
    (A : PublicBudgetOutcome n) (B : ℝ) (F : PublicBudgetDistribution) : Prop :=
  A.IsBudgetFeasibleOn B F.supportUpper ∧
    A.IsDSICOn F.supportUpper ∧ A.IsExPostIROn F.supportUpper

/-- Truthfulness on all bounded IID priors, or only the regular subclass. -/
inductive TruthfulnessScope where
  | allIID
  | regularIID
  deriving DecidableEq

/-- The IC/IR domain, distinct from the performance domain. -/
def TruthfulnessScope.Accepts (scope : TruthfulnessScope)
    (F : PublicBudgetDistribution) : Prop :=
  match scope with
  | .allIID => True
  | .regularIID => F.IsRegular

/-- A family may depend on population size and the public budget, but not on the prior or
support bound. -/
abbrev PublicBudgetMechanismFamily := (n : ℕ) → ℝ → PublicBudgetOutcome n

/-- One family is fixed before all priors. The `allIID` convention matches FH18 Section 5,
footnote 11; it is not identified with DSIC. -/
def IsPriorIndependentTruthful (scope : TruthfulnessScope)
    (M : PublicBudgetMechanismFamily) : Prop :=
  ∀ n B, 0 ≤ B →
    (M n B).IsBudgetFeasible B ∧
    ∀ F : PublicBudgetDistribution, scope.Accepts F →
      (M n B).IsBIC F ∧ (M n B).IsInterimIR F

end
end EconCSLib.OpenProblem.New.EconCSBench.RevelationGapPublicBudget

end


section

/-!
## Separate revenue and position-environment questions

Welfare regularity is not revenue regularity [FH18, Definition 2.1]. This module
states objective-specific truthful approximation questions and a concrete
position-allocation model. The smooth revenue-regular subclass is named explicitly.
Position weights are public, and all IID truthfulness is required independently of the
class of priors used to assess performance.
-/
namespace EconCSLib.OpenProblem.New.EconCSBench.RevelationGapPublicBudget

open MeasureTheory
open scoped BigOperators
noncomputable section

/-- Smooth public-budget revenue regularity adds monotone virtual value to welfare
regularity [FH18, Definition 2.1]. Atomic extensions are not claimed. -/
def PublicBudgetDistribution.IsSmoothRevenueRegular (F : PublicBudgetDistribution) : Prop :=
  F.IsRegular ∧ NoAtoms F.measure ∧ ∃ density : ℝ → ℝ,
    (∀ x : ℝ, x ∈ Set.Ioo 0 F.supportUpper →
      HasDerivAt (fun t => (F.measure (Set.Iic t)).toReal) (density x) x ∧
        0 < density x) ∧
    MonotoneOn (fun x => x - (F.measure (Set.Ioi x)).toReal / density x)
      (Set.Ioo 0 F.supportUpper)

/-- A supplied prior-informed candidate may depend on the entire prior. -/
abbrev PriorInformedDSICFamily :=
  (n : ℕ) → ℝ → PublicBudgetDistribution → PublicBudgetOutcome n

/-- Pointwise Bayesian welfare optimality within DSIC. A concrete middle-ironed rule must
be supplied separately. -/
def BayesianDSICOptimalityQuestion (priors : PriorClass)
    (candidate : PriorInformedDSICFamily) : Prop :=
  ∀ n, 0 < n → ∀ B, 0 ≤ B → ∀ F ∈ priors,
    (candidate n B F).IsDSICAdmissible B F ∧
      ∀ A : PublicBudgetOutcome n, A.IsDSICAdmissible B F →
        A.expectedWelfare F ≤ (candidate n B F).expectedWelfare F

/-- The regular-prior extension of the Bayesian-optimal DSIC question. -/
def RegularBayesianDSICOptimalityQuestion (candidate : PriorInformedDSICFamily) : Prop :=
  BayesianDSICOptimalityQuestion {F | F.IsRegular} candidate

/-- An objective-specific guarantee on a fixed class, retaining all-IID BIC and IR. -/
def ObjectiveFamilyAchievesFactor (objective : Objective) (priors : PriorClass)
    (M : PublicBudgetMechanismFamily) (β : ℝ) : Prop :=
  1 ≤ β ∧ IsPriorIndependentTruthful .allIID M ∧
    ∀ n, objective.AllowsPopulation n → ∀ B, 0 ≤ B → ∀ F ∈ priors,
      ∀ A : PublicBudgetOutcome n, A.IsBayesianAdmissible B F →
        A.expectedObjective objective F ≤ β * (M n B).expectedObjective objective F

/-- One family attains the requested objective factor. -/
def ObjectiveGuarantee (objective : Objective) (priors : PriorClass) (β : ℝ) : Prop :=
  ∃ M : PublicBudgetMechanismFamily, ObjectiveFamilyAchievesFactor objective priors M β

/-- Tight factor without requiring endpoint attainment. -/
def ObjectiveFactorQuestion (objective : Objective) (priors : PriorClass) (β : ℝ) : Prop :=
  1 ≤ β ∧ (∀ γ : ℝ, β < γ → ObjectiveGuarantee objective priors γ) ∧
    ∀ γ : ℝ, 1 ≤ γ → γ < β → ¬ ObjectiveGuarantee objective priors γ

/-- The separate revenue question on the smooth public-budget regular class. -/
def SmoothRegularRevenueFactorQuestion (β : ℝ) : Prop :=
  ObjectiveFactorQuestion .revenue {F | F.IsSmoothRevenueRegular} β

/-- The separate welfare question without a regularity assumption. -/
def IrregularWelfareFactorQuestion (β : ℝ) : Prop :=
  ObjectiveFactorQuestion .welfare Set.univ β

/-- All-IID BIC and IR are required. -/
def IsPriorIndependentPositionTruthful (M : PositionMechanismFamily) : Prop :=
  ∀ n E B, 0 ≤ B →
    (∀ reports, (∀ i, 0 ≤ reports i) → ∀ i, (M n E B).payment reports i ≤ B) ∧
    ∀ F : PublicBudgetDistribution,
      (M n E B).IsBIC E F ∧ (M n E B).IsInterimIR E F

/-- Uniform truthful approximation across all public position environments. -/
def PositionGuarantee (objective : Objective) (priors : PriorClass) (β : ℝ) : Prop :=
  1 ≤ β ∧ ∃ M : PositionMechanismFamily, IsPriorIndependentPositionTruthful M ∧
    ∀ n, objective.AllowsPopulation n → ∀ E B, 0 ≤ B → ∀ F ∈ priors,
      ∀ A : PositionOutcome n, A.IsBayesianAdmissible E B F →
        A.expectedObjective E objective F ≤ β * (M n E B).expectedObjective E objective F

/-- Candidate optimal truthful factor in position environments; not automatically a
revelation gap. -/
def PositionFactorQuestion (objective : Objective) (priors : PriorClass) (β : ℝ) : Prop :=
  1 ≤ β ∧ (∀ γ : ℝ, β < γ → PositionGuarantee objective priors γ) ∧
    ∀ γ : ℝ, 1 ≤ γ → γ < β → ¬ PositionGuarantee objective priors γ

end
end EconCSLib.OpenProblem.New.EconCSBench.RevelationGapPublicBudget

end


section

/-!
## Strategic public-budget auctions and actual revelation gaps

A mechanism fixes its action space and feasible assignment/payment rules before the
prior. Bayesian strategies may use the prior, but each player's action uses only her
own value. Outcomes are actual lotteries over feasible assignments, reusing `Lottery`
and `PositionOutcome`; no supplied denotation or arbitrary equilibrium predicate
determines welfare. Every pure deviation is compared with the equilibrium action, with
integrability and interim IR explicit.

FH18 Section 2 assumes symmetric auctions. The symmetry mode is therefore a parameter
fixed before choosing either mechanism class. The reference question uses symmetric
mechanisms; it does not assume every equilibrium is symmetric. This is a
strategic-form model.
-/
namespace EconCSLib.OpenProblem.New.EconCSBench.RevelationGapPublicBudget

open MeasureTheory
open scoped BigOperators
noncomputable section

/-- Relabeling reports relabels each bidder's service and payment. -/
def PublicBudgetOutcome.IsSymmetric {n : ℕ} (A : PublicBudgetOutcome n) : Prop :=
  ∀ (σ : Equiv.Perm (Fin n)) reports i,
    A.allocation (reports ∘ σ) i = A.allocation reports (σ i) ∧
    A.payment (reports ∘ σ) i = A.payment reports (σ i)

/-- A deviation in one value report changes only that player's chosen action. -/
theorem StrategicPositionMechanism.actions_update {n : ℕ}
    {M : StrategicPositionMechanism n} (strategy : M.Strategy)
    (values : Fin n → ℝ) (i : Fin n) (report : ℝ) :
    M.actions strategy (Function.update values i report) =
      Function.update (M.actions strategy values) i (strategy i report) := by
  funext j
  by_cases h : j = i
  · subst j
    simp [StrategicPositionMechanism.actions, BayesianMechanism.inducedMessages]
  · simp [StrategicPositionMechanism.actions, BayesianMechanism.inducedMessages, h]

/-- Withdrawal really has zero conditional expected utility for every type. -/
theorem StrategicPositionMechanism.interimUtility_withdrawal {n : ℕ}
    (M : StrategicPositionMechanism n) (E : PositionEnvironment n)
    (F : PublicBudgetDistribution) (strategy : M.Strategy)
    (withdrawal : M.Withdrawal E) (i : Fin n) (v : ℝ) :
    M.interimUtility E F strategy i v withdrawal.action = 0 := by
  simp [StrategicPositionMechanism.interimUtility,
    StrategicPositionMechanism.deviationUtility, withdrawal.service_zero, withdrawal.payment_zero]

/-- An actual outside option makes every best response individually rational. -/
theorem StrategicPositionEquilibrium.individually_rational {n : ℕ}
    {M : StrategicPositionMechanism n} {E : PositionEnvironment n}
    {F : PublicBudgetDistribution} (e : StrategicPositionEquilibrium M E F)
    (withdrawal : M.Withdrawal E) (i : Fin n) (v : ℝ)
    (hv : v ∈ Set.Icc 0 F.supportUpper) :
    0 ≤ M.interimUtility E F e.strategy i v (e.strategy i v) := by
  have h := e.best_response i v hv withdrawal.action
  rw [M.interimUtility_withdrawal E F e.strategy withdrawal i v] at h
  exact h

/-- Direct reporting simulates the actual strategy, with no freely chosen output decoder. -/
theorem StrategicPositionEquilibrium.interimUtility_eq {n : ℕ}
    {M : StrategicPositionMechanism n} {E : PositionEnvironment n}
    {F : PublicBudgetDistribution} (e : StrategicPositionEquilibrium M E F)
    (i : Fin n) (v report : ℝ) :
    e.induced.interimUtility E F i v report =
      M.interimUtility E F e.strategy i v (e.strategy i report) := by
  unfold PositionOutcome.interimUtility StrategicPositionMechanism.interimUtility
  congr 1
  funext values
  simp only [PositionOutcome.utility, e.allocation_eq, e.payment_eq,
    StrategicPositionMechanism.actions_update]
  rfl

/-- The induced direct outcome is BIC for this prior, not necessarily prior independent. -/
theorem StrategicPositionEquilibrium.induced_isBIC {n : ℕ}
    {M : StrategicPositionMechanism n} {E : PositionEnvironment n}
    {F : PublicBudgetDistribution} (e : StrategicPositionEquilibrium M E F) :
    e.induced.IsBIC E F := by
  intro i v report hv _
  rw [e.interimUtility_eq, e.interimUtility_eq]
  exact e.best_response i v hv (e.strategy i report)

/-- Interim IR is inherited by the actual induced direct outcome. -/
theorem StrategicPositionEquilibrium.induced_isInterimIR {n : ℕ}
    {M : StrategicPositionMechanism n} {E : PositionEnvironment n}
    {F : PublicBudgetDistribution} (e : StrategicPositionEquilibrium M E F)
    (withdrawal : M.Withdrawal E) :
    e.induced.IsInterimIR E F := by
  intro i v hv
  rw [e.interimUtility_eq]
  exact e.individually_rational withdrawal i v hv

/-- A budget-feasible strategic equilibrium really induces an admissible Bayesian outcome. -/
theorem StrategicPositionEquilibrium.induced_isBayesianAdmissible {n : ℕ}
    {M : StrategicPositionMechanism n} {E : PositionEnvironment n}
    {F : PublicBudgetDistribution} (e : StrategicPositionEquilibrium M E F)
    {B : ℝ} (hB : M.IsBudgetFeasible B) (withdrawal : M.Withdrawal E) :
    e.induced.IsBayesianAdmissible E B F := by
  refine ⟨?_, e.induced_isBIC, e.induced_isInterimIR withdrawal⟩
  intro values _ i
  rw [e.payment_eq]
  exact hB _ i

end
end EconCSLib.OpenProblem.New.EconCSBench.RevelationGapPublicBudget

end


section

/-!
## The truthful prior-independent public-budget welfare factor

The central question identifies the tight factor against a prior-informed Bayesian
benchmark on welfare-regular IID priors. FH18's all-pay result motivates calling this
the revelation gap; that result is not assumed as an axiom. Truthfulness on all IID
priors and only regular IID priors are separate. Revenue and position variants require
their own objectives and feasibility.
-/

namespace EconCSLib.OpenProblem.New.EconCSBench.RevelationGapPublicBudget

noncomputable section

/-- Compare with every admissible Bayesian benchmark, avoiding an assumption that optimal
welfare is attained. -/
def PublicBudgetFamilyAchievesFactor (scope : TruthfulnessScope)
    (M : PublicBudgetMechanismFamily) (β : ℝ) : Prop :=
  1 ≤ β ∧ IsPriorIndependentTruthful scope M ∧
    ∀ n, 0 < n → ∀ B, 0 ≤ B →
      ∀ F : PublicBudgetDistribution, F.IsRegular →
        ∀ A : PublicBudgetOutcome n, A.IsBayesianAdmissible B F →
          A.expectedWelfare F ≤ β * (M n B).expectedWelfare F

/-- One family and factor work uniformly over population size, budget, and prior. -/
def TruthfulPublicBudgetGuarantee (scope : TruthfulnessScope) (β : ℝ) : Prop :=
  ∃ M : PublicBudgetMechanismFamily, PublicBudgetFamilyAchievesFactor scope M β

/-- A lower-bound candidate rules out every smaller admissible factor. -/
def PublicBudgetWelfareLowerBoundQuestion
    (scope : TruthfulnessScope) (β : ℝ) : Prop :=
  1 ≤ β ∧ ∀ γ : ℝ, 1 ≤ γ → γ < β →
    ¬ TruthfulPublicBudgetGuarantee scope γ

/-- Identify a finite infimum; different factors above the endpoint may use different
families. -/
def PublicBudgetWelfareFactorQuestion
    (scope : TruthfulnessScope) (β : ℝ) : Prop :=
  PublicBudgetWelfareLowerBoundQuestion scope β ∧
    ∀ γ : ℝ, β < γ → TruthfulPublicBudgetGuarantee scope γ

/-- A supplied concrete mechanism family both attains the candidate and is optimal. -/
def CandidateFamilyOptimalityQuestion (scope : TruthfulnessScope)
    (M : PublicBudgetMechanismFamily) (β : ℝ) : Prop :=
  PublicBudgetWelfareFactorQuestion scope β ∧
    PublicBudgetFamilyAchievesFactor scope M β

end
/-- The explicit symmetric strategic gap is stated separately below. -/
noncomputable def ReferencePublicBudgetWelfareFactorQuestion (β : ℝ) : Prop :=
  PublicBudgetWelfareFactorQuestion .allIID β

/-- An explicit name for the retained unrestricted-symmetry truthful numerator. -/
noncomputable abbrev UnrestrictedSymmetryPublicBudgetWelfareFactorQuestion :=
  ReferencePublicBudgetWelfareFactorQuestion

/-- The revenue extension includes its own optimized non-revelation denominator. -/
noncomputable def RevenueRevelationGapQuestion
    (truthfulFactor strategicFactor gap : ℝ) : Prop :=
  StrategicRevelationGapQuestion .singleItem .symmetric .robust .revenue
    {F | F.IsSmoothRevenueRegular} truthfulFactor strategicFactor gap

/-- Public position weights and the distribution class are fixed before mechanism choices. -/
noncomputable def PositionRevelationGapQuestion (objective : Objective) (priors : PriorClass)
    (truthfulFactor strategicFactor gap : ℝ) : Prop :=
  StrategicRevelationGapQuestion .positions .symmetric .robust objective priors
    truthfulFactor strategicFactor gap

end EconCSLib.OpenProblem.New.EconCSBench.RevelationGapPublicBudget

end
