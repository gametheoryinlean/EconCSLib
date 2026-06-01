---
id: social_choice.fair_division.divisible.cardinal_instance
title: Divisible Cardinal Instance
kind: definition
status: formalized
primary_topic: social_choice
topics:
  - social_choice
  - social_choice.fair_division
  - social_choice.fair_division.divisible
uses:
  - social_choice.fair_division.divisible.ordinal_instance
  - social_choice.fair_division.cardinal_instance
  - social_choice.fair_division.envy_free
  - social_choice.fair_division.proportional
  - social_choice.fair_division.utilitarian_welfare
  - social_choice.fair_division.egalitarian_welfare
lean:
  modules:
    - EconCSLib.SocialChoice.FairDivision.Divisible.Instance
  declarations:
    - SocialChoice.FairDivision.Divisible.CardinalInstance
    - SocialChoice.FairDivision.Divisible.CardinalInstance.toGenericCardinalInstance
    - SocialChoice.FairDivision.Divisible.CardinalInstance.toShareInstance
    - SocialChoice.FairDivision.Divisible.CardinalInstance.IsEnvyFree
    - SocialChoice.FairDivision.Divisible.CardinalInstance.IsProportional
    - SocialChoice.FairDivision.Divisible.CardinalInstance.IsEquitable
    - SocialChoice.FairDivision.Divisible.CardinalInstance.IsParetoOptimal
    - SocialChoice.FairDivision.Divisible.CardinalInstance.utilitarianWelfare
    - SocialChoice.FairDivision.Divisible.CardinalInstance.egalitarianWelfare
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
tags:
  - fair-division
  - divisible
  - instance
  - cardinal
---

# Divisible Cardinal Instance

A *divisible cardinal instance* assigns each agent a real-valued utility
for every measurable cake piece:
$$
\mathrm{utility} : N \to \mathrm{Set}\ \Omega \to \mathbb{R}.
$$

In Lean: structure `SocialChoice.FairDivision.Divisible.CardinalInstance N Ω`.

## Bridges

- `toGenericCardinalInstance` — view as a generic real-valued cardinal
  fair-division instance
  ([[social_choice.fair_division.cardinal_instance]]) over share type
  $\mathrm{Set}\ \Omega$ and resource $\mathrm{Set.univ}$.
- `toShareInstance` — compose with `inducedSharePref` to get the
  underlying divisible *ordinal* instance
  ([[social_choice.fair_division.divisible.ordinal_instance]]).

## Instance-keyed fairness and welfare

A complete set of instance-keyed wrappers re-exports the generic
predicates:

- `IsEnvyFree A`, `IsProportional n A`, `IsEquitable A`,
  `IsParetoOptimal A` — fairness / efficiency predicates pinned to the
  current instance's utility and feasibility.
- `utilitarianWelfare A`, `egalitarianWelfare A` — welfare aggregations
  ([[social_choice.fair_division.utilitarian_welfare]],
  [[social_choice.fair_division.egalitarian_welfare]]).

All wrappers are definitional passes through to the corresponding
generic predicates with $I.\mathrm{utility}$ and feasibility supplied
from the instance.

## References

- [AGT Chapter 13] Nisan, Roughgarden, Tardos, and Vazirani, *Algorithmic Game Theory*. Cardinal valuations in cake-cutting.
