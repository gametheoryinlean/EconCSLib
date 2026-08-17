/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.OpenProblem.EconCSBench.Common

namespace EconCSLib.OpenProblem.EconCSBench.RevelationGapPublicBudget

open MeasureTheory
open scoped BigOperators

/-!
## I.i.d. public-budget regular values
-/

/-- A value distribution supported on `[0, h]`.  Public-budget regularity for
the welfare objective is exactly concavity of the cumulative distribution
function on this support (Feng--Hartline, Definition 2.1). -/
structure PublicBudgetRegularDistribution where
  /-- Law of one agent's value. -/
  measure : Measure ℝ
  /-- The law has total mass one. -/
  probability : IsProbabilityMeasure measure
  /-- Upper endpoint `h` of the value support. -/
  supportUpper : ℝ
  /-- The support interval is nonempty. -/
  supportUpper_nonnegative : 0 ≤ supportUpper
  /-- Values lie in `[0, h]` almost surely. -/
  supported :
    measure (Set.Icc 0 supportUpper) = 1
  /-- The CDF is concave on `[0, h]`, the public-budget regularity condition
  for welfare maximization. -/
  cdf_concave :
    ConcaveOn ℝ (Set.Icc 0 supportUpper)
      (fun v => ENNReal.toReal (measure (Set.Iic v)))

/-- The i.i.d. law `F^n` of a profile of `n` values. -/
noncomputable def iidValueProfileMeasure
    (F : PublicBudgetRegularDistribution) (n : ℕ) :
    Measure (Fin n → ℝ) :=
  letI : IsProbabilityMeasure F.measure := F.probability
  Measure.pi (fun _ : Fin n => F.measure)

/-!
## Direct single-item outcomes with a common public budget
-/

/-- A direct single-item outcome rule for `n` agents.  Allocation coordinates
are probabilities and may sum to less than one; payments are nonnegative. -/
structure PublicBudgetOutcome (n : ℕ) where
  /-- Allocation probability of each agent at every report profile. -/
  allocation : (Fin n → ℝ) → Fin n → ℝ
  /-- Payment of each agent at every report profile. -/
  payment : (Fin n → ℝ) → Fin n → ℝ
  /-- Allocation probabilities lie in `[0,1]`. -/
  allocation_mem : ∀ reports i,
    0 ≤ allocation reports i ∧ allocation reports i ≤ 1
  /-- At most one item is allocated. -/
  feasible : ∀ reports, ∑ i, allocation reports i ≤ 1
  /-- The seller never pays an agent. -/
  payment_nonnegative : ∀ reports i, 0 ≤ payment reports i
  /-- Allocation and payment coordinates are measurable in the reports. -/
  allocation_measurable : ∀ i, Measurable (fun reports => allocation reports i)
  payment_measurable : ∀ i, Measurable (fun reports => payment reports i)

/-- Utility of agent `i` with true value `v` from the outcome at `reports`.
Budget violations are excluded separately by `IsBudgetFeasible`; hence on
admissible outcomes this is precisely the finite branch `v x - p` of the hard
budget utility. -/
def PublicBudgetOutcome.utility
    {n : ℕ} (A : PublicBudgetOutcome n)
    (v : ℝ) (reports : Fin n → ℝ) (i : Fin n) : ℝ :=
  v * A.allocation reports i - A.payment reports i

/-- No realized payment exceeds the common public hard budget `B`. -/
def PublicBudgetOutcome.IsBudgetFeasible
    {n : ℕ} (A : PublicBudgetOutcome n) (B : ℝ) : Prop :=
  ∀ reports : Fin n → ℝ, (∀ i, 0 ≤ reports i) →
    ∀ i, A.payment reports i ≤ B

/-- Hard-budget feasibility on a fixed distribution's report domain
`[0, h]`.  A distribution-tailored Bayesian benchmark need not specify
meaningful incentives outside its own type space. -/
def PublicBudgetOutcome.IsBudgetFeasibleOn
    {n : ℕ} (A : PublicBudgetOutcome n) (B h : ℝ) : Prop :=
  ∀ reports : Fin n → ℝ,
    (∀ i, 0 ≤ reports i ∧ reports i ≤ h) →
      ∀ i, A.payment reports i ≤ B

/-- Dominant-strategy incentive compatibility of a direct outcome rule. -/
def PublicBudgetOutcome.IsDSIC
    {n : ℕ} (A : PublicBudgetOutcome n) : Prop :=
  ∀ (reports : Fin n → ℝ), (∀ j, 0 ≤ reports j) →
    ∀ (i : Fin n) (fake : ℝ), 0 ≤ fake →
      A.utility (reports i) (Function.update reports i fake) i ≤
        A.utility (reports i) reports i

/-- Ex-post individual rationality under truthful reports. -/
def PublicBudgetOutcome.IsExPostIR
    {n : ℕ} (A : PublicBudgetOutcome n) : Prop :=
  ∀ (reports : Fin n → ℝ), (∀ j, 0 ≤ reports j) →
    ∀ i, 0 ≤ A.utility (reports i) reports i

/-- Interim utility when agent `i` has true value `v`, reports `report`, and
the other coordinates are i.i.d. from `F`.  The `i`-th dummy coordinate of the
product draw is overwritten, which is equivalent to integrating only over
the other agents because `F` is a probability measure. -/
noncomputable def PublicBudgetOutcome.interimUtility
    {n : ℕ} (A : PublicBudgetOutcome n)
    (F : PublicBudgetRegularDistribution)
    (i : Fin n) (v report : ℝ) : ℝ :=
  ∫ values,
    A.utility v (Function.update values i report) i
      ∂iidValueProfileMeasure F n

/-- Bayesian incentive compatibility for the i.i.d. prior `F`. -/
def PublicBudgetOutcome.IsBIC
    {n : ℕ} (A : PublicBudgetOutcome n)
    (F : PublicBudgetRegularDistribution) : Prop :=
  ∀ (i : Fin n) (v report : ℝ),
    0 ≤ v → v ≤ F.supportUpper →
      0 ≤ report → report ≤ F.supportUpper →
    A.interimUtility F i v report ≤ A.interimUtility F i v v

/-- Interim individual rationality for the i.i.d. prior `F`. -/
def PublicBudgetOutcome.IsInterimIR
    {n : ℕ} (A : PublicBudgetOutcome n)
    (F : PublicBudgetRegularDistribution) : Prop :=
  ∀ (i : Fin n) (v : ℝ),
    0 ≤ v → v ≤ F.supportUpper →
    0 ≤ A.interimUtility F i v v

/-- Expected social welfare under the i.i.d. value profile `F^n`. -/
noncomputable def PublicBudgetOutcome.expectedWelfare
    {n : ℕ} (A : PublicBudgetOutcome n)
    (F : PublicBudgetRegularDistribution) : ℝ :=
  ∫ values, (∑ i, values i * A.allocation values i)
    ∂iidValueProfileMeasure F n

/-- Admissibility of a distribution-tailored Bayesian direct mechanism:
single-item feasibility is built into `PublicBudgetOutcome`; this predicate
adds the common hard budget, BIC, and interim IR requirements. -/
def PublicBudgetOutcome.IsBayesianAdmissible
    {n : ℕ} (A : PublicBudgetOutcome n)
    (B : ℝ) (F : PublicBudgetRegularDistribution) : Prop :=
  A.IsBudgetFeasibleOn B F.supportUpper ∧ A.IsBIC F ∧ A.IsInterimIR F

/-- Welfare of the Bayesian welfare-optimal mechanism tailored to `F`.
Taking the supremum separately for every `F` is exactly where the benchmark
is permitted to use distributional knowledge. -/
noncomputable def bayesianOptimalWelfare
    (n : ℕ) (B : ℝ) (F : PublicBudgetRegularDistribution) : ℝ :=
  sSup {welfare : ℝ |
    ∃ A : PublicBudgetOutcome n,
      A.IsBayesianAdmissible B F ∧ welfare = A.expectedWelfare F}

/-!
## Prior-independent truthful mechanism families
-/

/-- One prior-independent revelation mechanism family.  It may depend on the
public parameters `n` and `B`, but its outcome rule is fixed before the value
distribution `F` is known.  Revelation truthfulness is required in the
Bayesian sense for every admissible i.i.d. distribution, rather than silently
restricting the comparison to the smaller DSIC/ex-post-IR subclass. -/
structure PriorIndependentPublicBudgetMechanism where
  /-- Direct outcome rule selected from the public parameters only. -/
  outcome : ∀ n : ℕ, ℝ → PublicBudgetOutcome n
  /-- The rule respects every nonnegative public budget. -/
  budget_feasible :
    ∀ (n : ℕ) (B : ℝ), 0 ≤ B → (outcome n B).IsBudgetFeasible B
  /-- The same prior-independent rule is Bayesian incentive compatible for
  every public-budget regular i.i.d. distribution. -/
  bic :
    ∀ (n : ℕ) (B : ℝ), 0 ≤ B →
      ∀ F : PublicBudgetRegularDistribution,
        (outcome n B).IsBIC F
  /-- The same rule is interim individually rational for every admissible
  distribution. -/
  interim_ir :
    ∀ (n : ℕ) (B : ℝ), 0 ≤ B →
      ∀ F : PublicBudgetRegularDistribution,
        (outcome n B).IsInterimIR F

/-- A prior-independent truthful family has approximation factor `β`
uniformly over every nonempty number of agents, every common nonnegative
budget, and every i.i.d. public-budget regular value distribution. -/
def PriorIndependentPublicBudgetMechanism.AchievesFactor
    (M : PriorIndependentPublicBudgetMechanism) (β : ℝ) : Prop :=
  1 ≤ β ∧
    ∀ (n : ℕ), 0 < n →
      ∀ (B : ℝ), 0 ≤ B →
        ∀ F : PublicBudgetRegularDistribution,
          bayesianOptimalWelfare n B F ≤
            β * (M.outcome n B).expectedWelfare F

/-- Some truthful prior-independent mechanism uniformly achieves approximation
factor `β`. -/
def TruthfulPublicBudgetGuarantee (β : ℝ) : Prop :=
  ∃ M : PriorIndependentPublicBudgetMechanism, M.AchievesFactor β

/-- `β` is the tight truthful prior-independent approximation factor.  Smaller
factors are stronger.  The infimum need not itself be attained: every strictly
larger factor must be achievable, while every factor in `[1, β)` must be
impossible.  Since the all-mechanism factor is the known value `1`, this is also
the exact revelation gap requested in the Research Goal. -/
def IsTightPublicBudgetRevelationGap (β : ℝ) : Prop :=
  1 ≤ β ∧
    (∀ γ : ℝ, β < γ → TruthfulPublicBudgetGuarantee γ) ∧
    ∀ γ : ℝ, 1 ≤ γ → γ < β → ¬ TruthfulPublicBudgetGuarantee γ

/-- Open-problem statement: the exact truthful prior-independent factor, and
hence the revelation gap, can be identified. -/
def TightPublicBudgetRevelationGapStatement : Prop :=
  ∃ β : ℝ, IsTightPublicBudgetRevelationGap β

/-- Typed answer to: "What is the exact truthful prior-independent
approximation factor, equivalently the revelation gap, for i.i.d.
public-budget regular single-item welfare maximization?"  A valid submission
must give a concrete real expression for the gap.  Repeating
`IsTightPublicBudgetRevelationGap`, its existential wrapper, or a defining
`sInf` is not regarded as identifying the requested value. -/
theorem tightPublicBudgetRevelationGap :
    IsTightPublicBudgetRevelationGap (answer(sorry)) := by
  sorry

end EconCSLib.OpenProblem.EconCSBench.RevelationGapPublicBudget
