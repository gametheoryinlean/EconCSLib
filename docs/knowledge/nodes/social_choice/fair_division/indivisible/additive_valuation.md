---
id: social_choice.fair_division.indivisible.additive_valuation
title: Additive Valuation
kind: definition
status: formalized
primary_topic: social_choice
topics:
  - social_choice
  - social_choice.fair_division
  - social_choice.fair_division.indivisible
uses:
  - social_choice.fair_division.indivisible.valuation
lean:
  modules:
    - EconCSLib.SocialChoice.FairDivision.Indivisible.Valuation
  declarations:
    - SocialChoice.FairDivision.Indivisible.AdditiveValuation
    - SocialChoice.FairDivision.Indivisible.AdditiveValuation.toValuation
    - SocialChoice.FairDivision.Indivisible.AdditiveValuation.toValuation_empty
    - SocialChoice.FairDivision.Indivisible.AdditiveValuation.toValuation_union
    - SocialChoice.FairDivision.Indivisible.AdditiveValuation.toValuation_mono
verification:
  definition: accepted
  proof: accepted
  alignment: aligned
tags:
  - fair-division
  - indivisible
  - additive
  - valuation
---

# Additive Valuation

An *additive valuation* is the standard special case of indivisible
valuations in which the value of a bundle is the sum of per-item weights:
$$
v_i(S) = \sum_{g \in S} w_i(g),
$$
with weights $w_i : G \to \mathbb{R}$.

In Lean: structure `SocialChoice.FairDivision.Indivisible.AdditiveValuation N G`
with one field `weight : N → G → ℝ`.

## Lift to abstract valuation

`AdditiveValuation.toValuation` lifts to a generic
[[social_choice.fair_division.indivisible.valuation]]:
$$
(w.\mathrm{toValuation}).\mathrm{val}\ i\ S = \sum_{g \in S} w.\mathrm{weight}\ i\ g.
$$

## Basic properties

Three structural lemmas at the additive layer:

- **`toValuation_empty`** (`@[simp]`):
  $w.\mathrm{toValuation}.\mathrm{val}\ i\ \emptyset = 0$.

- **`toValuation_union`** for disjoint bundles
  ($\mathrm{Disjoint}\ S\ T$, $[\mathrm{DecidableEq}\ G]$):
  $$
  v(i, S \cup T) = v(i, S) + v(i, T).
  $$

- **`toValuation_mono`** for nonnegative weights
  ($\forall i\,g,\ w(i, g) \ge 0$, $[\mathrm{DecidableEq}\ G]$):
  $$
  T \subseteq S \;\Rightarrow\; v(i, T) \le v(i, S).
  $$

## Why additivity matters

The implication chain
([[social_choice.fair_division.indivisible.ef_implies_proportional_additive]],
[[social_choice.fair_division.indivisible.proportional_implies_mms_additive]])
needs additivity to convert a per-bundle inequality
$v_i(B_j) \le v_i(A_i)$ into the total-value comparisons that
proportionality and MMS demand. Monotone but non-additive valuations
support `EF → EFX` but not `EF → PROP`. Additive valuations are the
sweet spot for most positive results in the indivisible setting.

## References

- [AGT Chapter 11] Nisan, Roughgarden, Tardos, and Vazirani, *Algorithmic Game Theory*. Additive valuations.
- Bouveret, Chevaleyre, and Maudet (2016). "Fair Allocation of Indivisible Goods", COMSOC Handbook Ch. 12.
