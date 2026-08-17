/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.OpenProblem.EconCSBench.Common

namespace EconCSLib.OpenProblem.EconCSBench.QueryComplexityOfTarski

/-- The `d`-dimensional grid with side length `N`. -/
abbrev Grid (N d : ℕ) := Fin d → Fin N

/-- Coordinatewise monotonicity. -/
def IsGridMonotone {N d : ℕ} (f : Grid N d → Grid N d) : Prop :=
  ∀ x y, x ≤ y → f x ≤ f y

/-- A finite adaptive decision tree using only value queries to a grid oracle.
At a query node the continuation may depend on the complete oracle response. -/
inductive TarskiQueryTree (N d : ℕ)
  | output (point : Grid N d)
  | query (point : Grid N d) (next : Grid N d → TarskiQueryTree N d)

/-- Execute an adaptive query tree against an oracle. -/
def TarskiQueryTree.run
    {N d : ℕ} (tree : TarskiQueryTree N d)
    (oracle : Grid N d → Grid N d) : Grid N d :=
  match tree with
  | .output point => point
  | .query point next => (next (oracle point)).run oracle

/-- The actual number of oracle calls on one oracle-answer path. -/
def TarskiQueryTree.queryCount
    {N d : ℕ} (tree : TarskiQueryTree N d)
    (oracle : Grid N d → Grid N d) : ℕ :=
  match tree with
  | .output _ => 0
  | .query point next => 1 + (next (oracle point)).queryCount oracle

/-- A deterministic query algorithm is a finite adaptive tree that returns a
fixed point for every monotone oracle. -/
structure TarskiQueryAlgorithm (N d : ℕ) where
  /-- The adaptive oracle program. -/
  program : TarskiQueryTree N d
  /-- Correctness on every monotone oracle. -/
  correct :
    ∀ f, IsGridMonotone f →
      f (program.run f) = program.run f

/-- A finite-support randomized query algorithm.  Correctness is imposed on
the resulting success probability, rather than requiring every seed to be
correct (which would silently restrict the research question to zero-error
algorithms). -/
structure RandomizedTarskiQueryAlgorithm (N d : ℕ) (Seed : Type*)
    [Fintype Seed] where
  /-- Distribution of internal random coins. -/
  seedDist : Lottery ℝ Seed
  /-- Deterministic adaptive program selected by a seed. -/
  program : Seed → TarskiQueryTree N d

/-- Probability that a randomized algorithm returns a fixed point. -/
noncomputable def RandomizedTarskiQueryAlgorithm.successProbability
    {N d : ℕ} {Seed : Type*} [Fintype Seed]
    (algorithm : RandomizedTarskiQueryAlgorithm N d Seed)
    (f : Grid N d → Grid N d) : ℝ :=
  ∑ seed, algorithm.seedDist.val seed *
    if f ((algorithm.program seed).run f) =
        (algorithm.program seed).run f then 1 else 0

/-- Standard bounded-error correctness with success probability at least
`2/3` on every monotone oracle. -/
def RandomizedTarskiQueryAlgorithm.IsBoundedErrorCorrect
    {N d : ℕ} {Seed : Type*} [Fintype Seed]
    (algorithm : RandomizedTarskiQueryAlgorithm N d Seed) : Prop :=
  ∀ f, IsGridMonotone f →
    (2 / 3 : ℝ) ≤ algorithm.successProbability f

/-- Expected number of oracle calls of a randomized query algorithm. -/
noncomputable def RandomizedTarskiQueryAlgorithm.expectedQueryCount
    {N d : ℕ} {Seed : Type*} [Fintype Seed]
    (algorithm : RandomizedTarskiQueryAlgorithm N d Seed)
    (oracle : Grid N d → Grid N d) : ℝ :=
  Lottery.expectedValue algorithm.seedDist fun seed =>
    ((algorithm.program seed).queryCount oracle : ℝ)

/-- Worst-input expected-query lower bound against every finite-support
bounded-error randomized adaptive algorithm, matching the query-complexity
convention in the cited Tarski literature. -/
noncomputable def RequiresAtLeastQueries (N d q : ℕ) : Prop :=
  ∀ seeds : ℕ,
    ∀ algorithm : RandomizedTarskiQueryAlgorithm N d (Fin (seeds + 1)),
      algorithm.IsBoundedErrorCorrect →
        ∃ f : Grid N d → Grid N d,
          IsGridMonotone f ∧
            (q : ℝ) ≤ algorithm.expectedQueryCount f

/-- A `log(N)^{Ω(d)}` query lower bound in the standard fixed-dimension
regime.  The exponent has a universal linear dependence on `d`, while the
multiplicative constant and the threshold in `N` may depend on the fixed
dimension. -/
def ExponentialInDimensionLogLowerBoundStatement : Prop :=
  ∃ exponentDivisor d₀ : ℕ,
    0 < exponentDivisor ∧ 2 ≤ d₀ ∧
    ∀ d : ℕ, d₀ ≤ d →
      ∃ scale N₀ : ℕ,
        0 < scale ∧ 2 ≤ N₀ ∧
        ∀ N : ℕ, N₀ ≤ N →
          RequiresAtLeastQueries N d
            (((Nat.log 2 N) ^ (d / exponentDivisor)) / scale)

/-- A dimension-independent polylogarithmic exponent.  The Markdown does not
bound how the leading constant may depend on the fixed dimension. -/
def DimensionIndependentPolylogUpperBoundStatement : Prop :=
  ∃ exponent : ℕ, 0 < exponent ∧
    ∃ dimensionCost : ℕ → ℕ,
    ∀ d N : ℕ, 1 ≤ d → 2 ≤ N →
      0 < dimensionCost d ∧
      ∃ algorithm : TarskiQueryAlgorithm N d,
        ∀ f, IsGridMonotone f →
          algorithm.program.queryCount f ≤
            dimensionCost d * (Nat.log 2 N) ^ exponent

/-- The already known `log(N)^{O(d)}` side.  Since the cited upper bounds are
for every fixed dimension, their hidden leading constant may depend
arbitrarily on `d`; only the exponent has a universal linear bound. -/
def ExponentialInDimensionLogUpperBoundStatement : Prop :=
  ∃ C : ℕ, 0 < C ∧
    ∃ dimensionCost : ℕ → ℕ,
    ∀ d N : ℕ, 1 ≤ d → 2 ≤ N →
      0 < dimensionCost d ∧
      ∃ algorithm : TarskiQueryAlgorithm N d,
        ∀ f, IsGridMonotone f →
          algorithm.program.queryCount f ≤
            dimensionCost d *
              (Nat.log 2 N) ^ (C * d + C)

/-- Literal main question from the Markdown: the deterministic/bounded-error
query complexity has matching `log(N)^{Θ(d)}` upper and lower bounds. -/
def TarskiQueryComplexityStatement : Prop :=
  ExponentialInDimensionLogLowerBoundStatement ∧
    ExponentialInDimensionLogUpperBoundStatement

/-- English version: "Is Tarski fixed-point query complexity
`log(N)^{Θ(d)}`?" -/
theorem tarskiQueryComplexity :
    answer(sorry) ↔ TarskiQueryComplexityStatement := by
  sorry

/-- The stronger algorithmic route separately proposed in the Markdown. -/
theorem tarskiDimensionIndependentPolylogUpperBound :
    answer(sorry) ↔ DimensionIndependentPolylogUpperBoundStatement := by
  sorry

end EconCSLib.OpenProblem.EconCSBench.QueryComplexityOfTarski
