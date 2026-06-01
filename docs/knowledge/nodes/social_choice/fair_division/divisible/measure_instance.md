---
id: social_choice.fair_division.divisible.measure_instance
title: Divisible Measure Instance
kind: definition
status: formalized
primary_topic: social_choice
topics:
  - social_choice
  - social_choice.fair_division
  - social_choice.fair_division.divisible
uses:
  - social_choice.fair_division.divisible.cardinal_instance
  - social_choice.fair_division.divisible.measure_valuation
  - social_choice.fair_division.divisible.envy_free
lean:
  modules:
    - EconCSLib.SocialChoice.FairDivision.Divisible.Instance
  declarations:
    - SocialChoice.FairDivision.Divisible.MeasureInstance
    - SocialChoice.FairDivision.Divisible.MeasureInstance.toCakeValuation
    - SocialChoice.FairDivision.Divisible.MeasureInstance.toCardinalInstance
    - SocialChoice.FairDivision.Divisible.MeasureInstance.toShareInstance
    - SocialChoice.FairDivision.Divisible.MeasureInstance.IsEnvyFree
    - SocialChoice.FairDivision.Divisible.MeasureInstance.IsProportional
    - SocialChoice.FairDivision.Divisible.MeasureInstance.IsEquitable
    - SocialChoice.FairDivision.Divisible.MeasureInstance.IsEnvyFree.isProportional
verification:
  definition: accepted
  proof: accepted
  alignment: aligned
tags:
  - fair-division
  - divisible
  - instance
  - measure
---

# Divisible Measure Instance

A *divisible measure instance* equips each agent with a (typically
finite, non-atomic) measure on the cake $\Omega$:
$$
\mathrm{measure} : N \to \mathrm{Measure}\ \Omega.
$$

In Lean: structure `SocialChoice.FairDivision.Divisible.MeasureInstance N Ω`.

## Conversions

Three canonical conversions tie the measure-instance into the rest of
the stack:

- `toCakeValuation` — view the family as a cake valuation
  ([[social_choice.fair_division.divisible.measure_valuation]]) with
  $\mathrm{ENNReal}$ values.
- `toCardinalInstance` — push the measures to real-valued utilities via
  `.toReal`, giving a divisible cardinal instance
  ([[social_choice.fair_division.divisible.cardinal_instance]]).
- `toShareInstance` — compose with the cardinal-induced share
  preference to obtain a no-externality share instance.

## Instance-keyed fairness predicates

Re-exports of the divisible fairness predicates
([[social_choice.fair_division.divisible.envy_free]]) keyed on the
instance: `IsEnvyFree A`, `IsProportional n A`, `IsEquitable A`. These
are stated in $\mathrm{ENNReal}$ (the natural ambient ring for measure
values), with a translation to the real-valued cardinal form provided
by [[social_choice.fair_division.divisible.measure_instance_ef_iff_real]].

The basic implication `IsEnvyFree ⇒ IsProportional` lifts directly from
the cake-valuation level
([[social_choice.fair_division.divisible.ef_implies_proportional]]); the
instance-level wrapper is `MeasureInstance.IsEnvyFree.isProportional`.

The existence theorems
([[social_choice.fair_division.divisible.measure_instance_existence]])
are stated at this layer.

## References

- [AGT Chapter 13] Nisan, Roughgarden, Tardos, and Vazirani, *Algorithmic Game Theory*. Measure-based cake-cutting instances.
