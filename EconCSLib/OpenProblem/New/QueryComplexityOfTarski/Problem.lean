/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.Foundation.Utility.Lottery
import EconCSLib.OpenProblem.Util.Answer
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Nat.Log
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# 18. Tarski fixed-point query complexity
-/



section

/-!
## Tarski fixed-point query models

A query returns the entire vector `f(x)` at cost one. The monotone oracle is fixed
throughout execution; the tree sees only replies, not its table. Any fixed point
suffices, without extremality or uniqueness. Local processing is not charged.

Randomized algorithms are finite real-weight lotteries over finite adaptive trees, not
necessarily bounded fair-bit programs. Normalization, SeedCompression,
TranscriptUnrolling and AlmostSureStrategies prove the finite-grid reduction for
measurable, almost-surely terminating total transcript strategies. See
[Branzei–Phillips–Recker 2025, §2 and §5 footnote 2].

Expected query cost and success are measured separately on every fixed oracle. The
success threshold is `2/3`; the source uses `9/10` and permits any constant above
`1/2` for asymptotic bounds. No prior over oracles or Word-RAM time is used.
-/

open scoped BigOperators

namespace EconCSLib.OpenProblem.New.EconCSBench.QueryComplexityOfTarski

/-- A finite grid with the coordinatewise function order. -/
abbrev Grid (N d : ℕ) := Fin d → Fin N

/-- Mathlib monotonicity under the product order. -/
def IsGridMonotone {N d : ℕ} (f : Grid N d → Grid N d) : Prop :=
  Monotone f

/-- An adaptive tree whose continuation receives only the latest oracle reply. -/
inductive TarskiQueryTree (N d : ℕ)
  | output (point : Grid N d)
  | query (point : Grid N d) (next : Grid N d → TarskiQueryTree N d)

/-- One execution returns output and query count. Each repeat is charged; output nodes do
not query the oracle to verify their semantic correctness. -/
def TarskiQueryTree.run {N d : ℕ} :
    TarskiQueryTree N d → (Grid N d → Grid N d) → Grid N d × ℕ
  | .output point, _ => (point, 0)
  | .query point next, f =>
      let result := (next (f point)).run f
      (result.1, result.2 + 1)

/-- Correctness for every monotone oracle, without a uniqueness promise. -/
def TarskiQueryTree.IsCorrect {N d : ℕ} (tree : TarskiQueryTree N d) : Prop :=
  ∀ f, IsGridMonotone f → f (tree.run f).1 = (tree.run f).1

/-- A lottery over `seeds + 1` trees, fixed before the oracle. Real probabilities need not
be dyadic in this query-counting model. -/
structure RandomizedTarskiQueryAlgorithm (N d seeds : ℕ) where
  seedDist : Lottery ℝ (Fin (seeds + 1))
  program : Fin (seeds + 1) → TarskiQueryTree N d

/-- Success probability for one fixed oracle. Testing the output here is a semantic
predicate and grants no free oracle access to the tree. -/
noncomputable def RandomizedTarskiQueryAlgorithm.successProbability
    {N d seeds : ℕ} (A : RandomizedTarskiQueryAlgorithm N d seeds)
    (f : Grid N d → Grid N d) : ℝ := by
  classical
  exact ∑ seed, A.seedDist.val seed *
    if f ((A.program seed).run f).1 = ((A.program seed).run f).1 then 1 else 0

/-- Bounded-error correctness on every valid input; some seeds may fail. -/
def RandomizedTarskiQueryAlgorithm.IsBoundedErrorCorrect
    {N d seeds : ℕ} (A : RandomizedTarskiQueryAlgorithm N d seeds) : Prop :=
  ∀ f, IsGridMonotone f → (2 / 3 : ℝ) ≤ A.successProbability f

/-- Unconditional expected query count, including failed executions. -/
noncomputable def RandomizedTarskiQueryAlgorithm.expectedQueryCount
    {N d seeds : ℕ} (A : RandomizedTarskiQueryAlgorithm N d seeds)
    (f : Grid N d → Grid N d) : ℝ :=
  ∑ seed, A.seedDist.val seed * (((A.program seed).run f).2 : ℝ)

/-- Deterministic or bounded-error randomized expected query complexity. -/
inductive QueryModel
  | deterministic
  | randomizedExpected
  deriving DecidableEq

/-- A tree or lottery chosen before the oracle is correct with cost at most `q` on every
monotone oracle; randomized cost is expected over the seed. -/
def HasQueryUpperBound (model : QueryModel) (N d : ℕ) (q : ℝ) : Prop :=
  match model with
  | .deterministic =>
      ∃ tree : TarskiQueryTree N d, tree.IsCorrect ∧
        ∀ f, IsGridMonotone f → ((tree.run f).2 : ℝ) ≤ q
  | .randomizedExpected =>
      ∃ seeds : ℕ, ∃ A : RandomizedTarskiQueryAlgorithm N d seeds,
        A.IsBoundedErrorCorrect ∧
          ∀ f, IsGridMonotone f → A.expectedQueryCount f ≤ q

/-- Every correct algorithm has a hard monotone oracle, chosen before the seed in the
randomized case. -/
def HasQueryLowerBound (model : QueryModel) (N d : ℕ) (q : ℝ) : Prop :=
  match model with
  | .deterministic =>
      ∀ tree : TarskiQueryTree N d, tree.IsCorrect →
        ∃ f, IsGridMonotone f ∧ q ≤ ((tree.run f).2 : ℝ)
  | .randomizedExpected =>
      ∀ seeds : ℕ, ∀ A : RandomizedTarskiQueryAlgorithm N d seeds,
        A.IsBoundedErrorCorrect →
          ∃ f, IsGridMonotone f ∧ q ≤ A.expectedQueryCount f

end EconCSLib.OpenProblem.New.EconCSBench.QueryComplexityOfTarski

end


section

/-!
## Tarski query-complexity questions

Bounds take side length `N` before dimension `d`; the asymptotic domain is `N ≥ 2, d ≥
1`. Fixed-dimension polylogarithmic bounds with a dimension-dependent exponent are
already known. The barrier-breaking target instead chooses one exponent before every
dimension, while coefficients and thresholds may depend on dimension
[Chen–Li–Yannakakis 2026, §9].

Upper- and lower-bound directions are separate.
-/

namespace EconCSLib.OpenProblem.New.EconCSBench.QueryComplexityOfTarski

/-- A bound `O_d(log^exponent N)` with coefficient and threshold fixed before `N`. -/
def HasFixedDimensionPolylogUpperBound
    (model : QueryModel) (d exponent : ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, 2 ≤ N₀ ∧
    ∀ N : ℕ, N₀ ≤ N →
      HasQueryUpperBound model N d (C * (Nat.log 2 N : ℝ) ^ exponent)

/-- One exponent works for every dimension, with dimension-dependent coefficients and
thresholds. This is weaker than a polynomial in both `d` and `log N`. -/
def DimensionIndependentPolylogUpperBoundStatement (model : QueryModel) : Prop :=
  ∃ exponent : ℕ, 0 < exponent ∧
    ∀ d : ℕ, 1 ≤ d → HasFixedDimensionPolylogUpperBound model d exponent

/-- The `log^{Ω(d)} N` lower side. Integer division gives a linear exponent for large `d`.
Global slope and dimension threshold precede dimension-specific coefficients and
side-length thresholds; no impossible small-`N` uniformity is imposed. -/
def ExponentialInDimensionLogLowerBoundStatement (model : QueryModel) : Prop :=
  ∃ divisor d₀ : ℕ, 0 < divisor ∧ 2 ≤ d₀ ∧
    ∀ d : ℕ, d₀ ≤ d →
      ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, 2 ≤ N₀ ∧
        ∀ N : ℕ, N₀ ≤ N →
          HasQueryLowerBound model N d (C * (Nat.log 2 N : ℝ) ^ (d / divisor))

end EconCSLib.OpenProblem.New.EconCSBench.QueryComplexityOfTarski

end


/-!
## Questions and answers
-/

namespace EconCSLib.OpenProblem.New.EconCSBench.QueryComplexityOfTarski

/-- One logarithmic exponent precedes every dimension; coefficients may depend on
dimension. -/
theorem tarskiDimensionIndependentExponent (model : QueryModel) :
    answer(sorry) ↔ DimensionIndependentPolylogUpperBoundStatement model := by
  sorry

/-- Independent log-to-linear-in-dimension lower-bound direction. -/
theorem tarskiDimensionDependentLowerBound (model : QueryModel) :
    answer(sorry) ↔ ExponentialInDimensionLogLowerBoundStatement model := by
  sorry

end EconCSLib.OpenProblem.New.EconCSBench.QueryComplexityOfTarski
