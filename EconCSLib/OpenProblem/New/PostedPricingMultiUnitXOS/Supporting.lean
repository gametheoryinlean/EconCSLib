/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.OpenProblem.New.PostedPricingMultiUnitXOS.Problem

/-!
# PostedPricingMultiUnitXOS: supporting material

Auxiliary definitions and lemmas for the problem statement.
-/

section

/-!
## Does the static-pricing ratio converge uniformly to one?

The supply threshold depends only on epsilon, not on buyers, item types, or priors.
Prices are selected from the instance before its values and order. The reference
convention uses a value-aware arrival adversary and a local tie rule fixed before
realization. Robust tie-breaking is a separate, stronger question.
-/
namespace EconCSLib.OpenProblem.New.EconCSBench.PostedPricingMultiUnitXOS

noncomputable section

/-- Stronger variant requiring the guarantee for every measurable demand selection. -/
def RobustStaticXOSPricingStatement : Prop :=
  StaticXOSPricingConvergesToOneStatement .valueAware .robustDemand

end
end EconCSLib.OpenProblem.New.EconCSBench.PostedPricingMultiUnitXOS

end
