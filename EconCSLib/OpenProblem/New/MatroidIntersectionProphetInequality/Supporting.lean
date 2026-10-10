/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.OpenProblem.New.MatroidIntersectionProphetInequality.Problem

/-!
# MatroidIntersectionProphetInequality: supporting material

Auxiliary definitions and lemmas for the problem statement.
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

/-- The minimum number of colorings, without assuming a proposed asymptotic answer. -/
def CliqueFactorProductDimensionExactly (ell r k : ℕ) : Prop :=
  CliqueFactorProductDimensionAtMost ell r k ∧
    ∀ j : ℕ, j < k → ¬ CliqueFactorProductDimensionAtMost ell r j

end

end EconCSLib.OpenProblem.New.EconCSBench.MatroidIntersectionProphet

end
