---
id: social_choice.fair_division.cardinal_instance_wrappers
title: Cardinal-Instance Fairness and Welfare Wrappers
kind: definition
status: formalized
primary_topic: social_choice
topics:
  - social_choice
  - social_choice.fair_division
  - social_choice.fair_division.core
uses:
  - social_choice.fair_division.cardinal_instance
  - social_choice.fair_division.envy_free
  - social_choice.fair_division.proportional
  - social_choice.fair_division.equitable
  - social_choice.fair_division.pareto_optimal
  - social_choice.fair_division.utilitarian_welfare
  - social_choice.fair_division.egalitarian_welfare
lean:
  modules:
    - EconCSLib.SocialChoice.FairDivision.Cardinal
  declarations:
    - SocialChoice.FairDivision.CardinalInstance.IsEnvyFree
    - SocialChoice.FairDivision.CardinalInstance.IsProportional
    - SocialChoice.FairDivision.CardinalInstance.IsEquitable
    - SocialChoice.FairDivision.CardinalInstance.IsParetoOptimal
    - SocialChoice.FairDivision.CardinalInstance.utilitarianWelfare
    - SocialChoice.FairDivision.CardinalInstance.egalitarianWelfare
    - SocialChoice.FairDivision.CardinalInstance.IsUtilitarianOptimal
    - SocialChoice.FairDivision.CardinalInstance.IsMaxmin
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
tags:
  - fair-division
  - instance
  - cardinal
  - fairness
  - welfare
---

# Cardinal-Instance Fairness and Welfare Wrappers

The cardinal-instance API ([[social_choice.fair_division.cardinal_instance]])
re-exports the shared fairness and welfare predicates so they take an
instance as input directly, sparing call sites from unpacking the utility
field.

For an instance $I : \mathrm{CardinalInstance}\ N\ R\ S$ and an allocation $A$:

- `I.IsEnvyFree A` ⇔ envy-freeness w.r.t. $I.\mathrm{utility}$
  ([[social_choice.fair_division.envy_free]]).
- `I.IsProportional n whole A` ⇔ proportional with whole share `whole`
  ([[social_choice.fair_division.proportional]]).
- `I.IsEquitable A` ⇔ equitable
  ([[social_choice.fair_division.equitable]]).
- `I.IsParetoOptimal A` ⇔ Pareto optimal under $I.\mathrm{feasible}$
  ([[social_choice.fair_division.pareto_optimal]]).
- `I.utilitarianWelfare A`, `I.egalitarianWelfare A` ⇔ welfare
  aggregations ([[social_choice.fair_division.utilitarian_welfare]],
  [[social_choice.fair_division.egalitarian_welfare]]).
- `I.IsUtilitarianOptimal A`, `I.IsMaxmin A` ⇔ welfare-optimality under
  $I.\mathrm{feasible}$.

Each wrapper is a definitional pass-through to the underlying generic
predicate; no extra invariants are introduced. The point is purely
ergonomic: at the instance layer one writes `I.IsEnvyFree A` instead of
spelling out `IsEnvyFree I.utility A`.

The divisible-instance and indivisible-instance wrappers
([[social_choice.fair_division.divisible.cardinal_instance]],
[[social_choice.fair_division.indivisible.cardinal_instance]]) compose
this layer with the structured allocation types.

## References

- [AGT Chapter 11] Nisan, Roughgarden, Tardos, and Vazirani, *Algorithmic Game Theory*. Cardinal fair-division wrappers.
