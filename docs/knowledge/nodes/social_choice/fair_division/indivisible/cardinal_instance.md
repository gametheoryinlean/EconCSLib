---
id: social_choice.fair_division.indivisible.cardinal_instance
title: Indivisible Cardinal Instance
kind: definition
status: formalized
primary_topic: social_choice
topics:
  - social_choice
  - social_choice.fair_division
  - social_choice.fair_division.indivisible
uses:
  - social_choice.fair_division.indivisible.valuation
  - social_choice.fair_division.cardinal_instance
  - social_choice.fair_division.envy_free
  - social_choice.fair_division.proportional
  - social_choice.fair_division.utilitarian_welfare
  - social_choice.fair_division.egalitarian_welfare
lean:
  modules:
    - EconCSLib.SocialChoice.FairDivision.Indivisible.Instance
  declarations:
    - SocialChoice.FairDivision.Indivisible.CardinalInstance
    - SocialChoice.FairDivision.Indivisible.CardinalInstance.toValuation
    - SocialChoice.FairDivision.Indivisible.CardinalInstance.toGenericCardinalInstance
    - SocialChoice.FairDivision.Indivisible.CardinalInstance.toShareInstance
    - SocialChoice.FairDivision.Indivisible.CardinalInstance.IsEnvyFree
    - SocialChoice.FairDivision.Indivisible.CardinalInstance.IsEF1
    - SocialChoice.FairDivision.Indivisible.CardinalInstance.IsEFX
    - SocialChoice.FairDivision.Indivisible.CardinalInstance.IsProportional
    - SocialChoice.FairDivision.Indivisible.CardinalInstance.IsEquitable
    - SocialChoice.FairDivision.Indivisible.CardinalInstance.IsMaxminShare
    - SocialChoice.FairDivision.Indivisible.CardinalInstance.IsParetoOptimal
    - SocialChoice.FairDivision.Indivisible.CardinalInstance.IsUtilitarianOptimal
    - SocialChoice.FairDivision.Indivisible.CardinalInstance.IsMaxmin
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
tags:
  - fair-division
  - indivisible
  - instance
  - cardinal
---

# Indivisible Cardinal Instance

An *indivisible cardinal instance* assigns each agent a real-valued
utility for every bundle:
$$
\mathrm{utility} : N \to \mathrm{Finset}\ G \to \mathbb{R}.
$$

In Lean: structure `SocialChoice.FairDivision.Indivisible.CardinalInstance N G`
with a `utility` field plus the outer good set `allGoods : Finset G`.

## Bridges

- `toValuation` — wrap as a bare `Valuation`
  ([[social_choice.fair_division.indivisible.valuation]]).
- `toGenericCardinalInstance` — view as a generic real-valued cardinal
  fair-division instance ([[social_choice.fair_division.cardinal_instance]])
  over share type $\mathrm{Finset}\ G$ and resource value `allGoods`.
- `toShareInstance` — compose with `inducedSharePref` to get the
  underlying indivisible ordinal instance
  ([[social_choice.fair_division.indivisible.ordinal_instance]]).

## Instance-keyed wrappers

A full menu of instance-keyed fairness and welfare predicates is
re-exported:

- `IsEnvyFree`, `IsEF1`, `IsEFX`, `IsProportional`, `IsEquitable`,
  `IsMaxminShare` — fairness predicates.
- `IsParetoOptimal`, `IsUtilitarianOptimal`, `IsMaxmin` — efficiency
  / welfare-optimality predicates.

All wrappers are definitional pass-throughs to the corresponding
generic or `Indivisible`-prefixed predicates with $I.\mathrm{utility}$
and feasibility supplied from the instance.

## References

- [AGT Chapter 11] Nisan, Roughgarden, Tardos, and Vazirani, *Algorithmic Game Theory*. Cardinal valuations in indivisible fair division.
