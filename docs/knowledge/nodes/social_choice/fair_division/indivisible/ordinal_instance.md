---
id: social_choice.fair_division.indivisible.ordinal_instance
title: Indivisible Ordinal Instance
kind: definition
status: formalized
primary_topic: social_choice
topics:
  - social_choice
  - social_choice.fair_division
  - social_choice.fair_division.indivisible
uses:
  - social_choice.fair_division.share_instance
  - social_choice.fair_division.indivisible.allocation
lean:
  modules:
    - EconCSLib.SocialChoice.FairDivision.Indivisible.Instance
  declarations:
    - SocialChoice.FairDivision.Indivisible.Instance
    - SocialChoice.FairDivision.Indivisible.Instance.toShareInstance
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
tags:
  - fair-division
  - indivisible
  - instance
  - ordinal
---

# Indivisible Ordinal Instance

An *indivisible ordinal instance* is the no-externality share model
specialized to discrete-item allocation: each agent's preference is an
ordinal preference on bundles $\mathrm{Finset}\ G$.

In Lean: structure `SocialChoice.FairDivision.Indivisible.Instance N G`
with a `sharePref : N → Pref (Finset G)` field plus the outer good set
`allGoods : Finset G`.

Feasibility is the partition predicate
[[social_choice.fair_division.indivisible.allocation]].

## Bridge to the generic share-instance API

`Indivisible.Instance.toShareInstance` (with `[Fintype N]
[DecidableEq G]`) views the indivisible ordinal instance as a generic
no-externality share instance
([[social_choice.fair_division.share_instance]]) over share type
$\mathrm{Finset}\ G$ and resource value `allGoods`. This lets all
generic share-instance solution concepts apply.

This wrapper layer parallels the divisible analogue
([[social_choice.fair_division.divisible.ordinal_instance]]) — both
plug into the same shared social-choice infrastructure via
`toShareInstance`.

## References

- [AGT Chapter 11] Nisan, Roughgarden, Tardos, and Vazirani, *Algorithmic Game Theory*. Indivisible-goods instances.
