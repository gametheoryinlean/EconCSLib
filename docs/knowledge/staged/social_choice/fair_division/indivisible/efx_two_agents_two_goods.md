---
id: social_choice.fair_division.indivisible.efx_two_agents_two_goods
title: EFX Existence — 2 Agents, 2 Goods
kind: theorem
status: staged
primary_topic: social_choice
topics:
  - social_choice
  - social_choice.fair_division
  - social_choice.fair_division.indivisible
uses:
  - social_choice.fair_division.indivisible.efx_singleton_bundle
lean:
  modules:
    - EconCSLib.SocialChoice.FairDivision.Indivisible.EFX
  declarations:
    - SocialChoice.FairDivision.Indivisible.efx_two_agents_two_goods
verification:
  statement: accepted
  proof: accepted
  alignment: aligned
tags:
  - fair-division
  - indivisible
  - efx
  - existence
  - example
---

# EFX Existence — 2 Agents, 2 Goods

**Theorem.** For two agents and two distinct goods, an EFX allocation
always exists.

In Lean: `SocialChoice.FairDivision.Indivisible.efx_two_agents_two_goods`.
Hypotheses: `[DecidableEq G]`, two distinct goods $g_1, g_2 \in G$, an
arbitrary valuation $v$.

## Proof

Construct the obvious split: agent $0$ receives $\{g_1\}$ and agent $1$
receives $\{g_2\}$. The bundles partition $\{g_1, g_2\}$ (disjointness
by $g_1 \ne g_2$; cover by inspection).

Each bundle has size 1, so the *singleton-bundle EFX* sufficient
condition
([[social_choice.fair_division.indivisible.efx_singleton_bundle]])
applies and gives EFX directly without needing any structure on $v$.

## Significance

This is the trivial 2×2 case of the EFX existence question. The general
2-agent case
([[social_choice.fair_division.indivisible.efx_exists_two_agents]])
strengthens this to arbitrary good sets but still uses the
singleton-bundle device on a maximin-leximin sub-bundle.

## References

- [AGT Chapter 11] Nisan, Roughgarden, Tardos, and Vazirani, *Algorithmic Game Theory*. Small EFX existence examples.
