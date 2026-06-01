---
id: social_choice.fair_division.indivisible.additive_instance
title: Indivisible Additive Instance
kind: definition
status: formalized
primary_topic: social_choice
topics:
  - social_choice
  - social_choice.fair_division
  - social_choice.fair_division.indivisible
uses:
  - social_choice.fair_division.indivisible.cardinal_instance
  - social_choice.fair_division.indivisible.additive_valuation
lean:
  modules:
    - EconCSLib.SocialChoice.FairDivision.Indivisible.Instance
  declarations:
    - SocialChoice.FairDivision.Indivisible.AdditiveInstance
    - SocialChoice.FairDivision.Indivisible.AdditiveInstance.toAdditiveValuation
    - SocialChoice.FairDivision.Indivisible.AdditiveInstance.toValuation
    - SocialChoice.FairDivision.Indivisible.AdditiveInstance.toCardinalInstance
    - SocialChoice.FairDivision.Indivisible.AdditiveInstance.toGenericCardinalInstance
    - SocialChoice.FairDivision.Indivisible.AdditiveInstance.toShareInstance
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
tags:
  - fair-division
  - indivisible
  - instance
  - additive
---

# Indivisible Additive Instance

An *indivisible additive instance* equips each agent with per-item
weights $w(i, g) \in \mathbb{R}$, with the bundle utility computed
additively:
$$
v_i(S) = \sum_{g \in S} w(i, g).
$$

In Lean: structure `SocialChoice.FairDivision.Indivisible.AdditiveInstance N G`
with a `weight` field plus the outer good set `allGoods : Finset G`.

## Conversions

Five conversions tie the additive-instance layer into the rest of the
stack:

- `toAdditiveValuation` — view the weights as an
  `AdditiveValuation`
  ([[social_choice.fair_division.indivisible.additive_valuation]]).
- `toValuation` — compose with `AdditiveValuation.toValuation` to get
  a bare `Valuation`.
- `toCardinalInstance` — view as an indivisible cardinal instance
  ([[social_choice.fair_division.indivisible.cardinal_instance]]) with
  $\mathrm{utility}\ i\ S = \sum_g w(i, g)$.
- `toGenericCardinalInstance` — view as a generic real-valued cardinal
  fair-division instance.
- `toShareInstance` — view as the underlying ordinal share instance.

## Instance-keyed wrappers

Same as for the cardinal layer
([[social_choice.fair_division.indivisible.cardinal_instance]]), all
fairness and welfare predicates are re-exported at the additive
instance level. The bundled round-robin
([[social_choice.fair_division.indivisible.round_robin_alloc]]) and
envy-cycle
([[social_choice.fair_division.indivisible.envy_cycle_algorithm]])
rules are stated against `AdditiveInstance`, providing
algorithm-by-instance call sites.

## References

- [AGT Chapter 11] Nisan, Roughgarden, Tardos, and Vazirani, *Algorithmic Game Theory*. Additive instances in indivisible fair division.
