---
id: social_choice.fair_division.indivisible.utilitarian_welfare
title: Indivisible Utilitarian Welfare
kind: definition
status: formalized
primary_topic: social_choice
topics:
  - social_choice
  - social_choice.fair_division
  - social_choice.fair_division.indivisible
uses:
  - social_choice.fair_division.indivisible.allocation
  - social_choice.fair_division.indivisible.valuation
  - social_choice.fair_division.utilitarian_welfare
lean:
  modules:
    - EconCSLib.SocialChoice.FairDivision.Indivisible.SocialWelfare
  declarations:
    - SocialChoice.FairDivision.Indivisible.IsUtilitarianOptimal
    - SocialChoice.FairDivision.Indivisible.utilitarianWelfare_mono
    - SocialChoice.FairDivision.Indivisible.utilitarianWelfare_unique
verification:
  definition: accepted
  proof: accepted
  alignment: aligned
tags:
  - fair-division
  - indivisible
  - welfare
  - utilitarian
---

# Indivisible Utilitarian Welfare

Specialisation of the generic utilitarian welfare
([[social_choice.fair_division.utilitarian_welfare]]) to the
indivisible setting: for a valuation $v$ and allocation $A$,
$$
W_{\mathrm{util}}(v, A) = \sum_{i \in N} v_i(A(i)).
$$

The same definition `utilitarianWelfare` (under
`SocialChoice.FairDivision`) applies, taking `v.val` for the per-agent
utility function and the indivisible allocation
([[social_choice.fair_division.indivisible.allocation]]) for the share
assignment.

The instance-keyed *optimality* predicate is wrapped here:

- `IsUtilitarianOptimal` (abbrev): no complete allocation
  (`IsAllocation allGoods B`) has strictly larger utilitarian welfare.

## Basic lemmas

Re-exported from the generic layer with the indivisible-friendly
hypotheses:

- `utilitarianWelfare_mono`: pointwise improvement implies welfare
  improvement.
- `utilitarianWelfare_unique` (`@[simp]`): for `Unique N`, welfare
  equals the single agent's utility.

## Relation to fairness

Utilitarian welfare optimization can conflict with fairness:
maximizing total welfare may produce highly unequal allocations
(give everything to the agent with highest per-item values). The
*Nash welfare* (geometric mean instead of arithmetic mean) is the
standard mediator — its maximizer is known to be EF1 + PO under
additive valuations (Caragiannis et al. 2019). EconCSLib does not yet
formalize Nash welfare; this welfare module is the additive-mean
counterpart.

## References

- [AGT Chapter 11] Nisan, Roughgarden, Tardos, and Vazirani, *Algorithmic Game Theory*. Utilitarian welfare for indivisible goods.
- Caragiannis, Kurokawa, Moulin, Procaccia, Shah, and Wang (2019). "The Unreasonable Fairness of Maximum Nash Welfare". *EC*.
