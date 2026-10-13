/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.OpenProblem.New.ProphetInequalitySubadditiveCA.Problem

/-!
# ProphetInequalitySubadditiveCA: supporting material

Auxiliary definitions and lemmas for the problem statement.
-/

section

/-!
## Constant-factor static pricing for subadditive valuations

The factor is uniform over all market sizes and independent priors. Prices are chosen
after the prior but before realized values. This is an existential question with no
computational restriction. The reference baseline uses normalized monotone values and
known indexed order; stronger order and tie requirements are stated separately.
-/
namespace EconCSLib.OpenProblem.New.EconCSBench.SubadditiveStaticPricing

noncomputable section

/-- Stronger guarantee for unknown fixed order and arbitrary demand tie-breaking. -/
def RobustConstantFactorStatement : Prop :=
  ConstantFactorSubadditiveStaticPricingStatement
    .normalizedMonotone .unknownFixed .robustDemand

end
end EconCSLib.OpenProblem.New.EconCSBench.SubadditiveStaticPricing

end
