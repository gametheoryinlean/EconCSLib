---
id: social_choice.fair_division.indivisible.ef_implies_efx_mono
title: EF ⇒ EFX (Monotone Valuations)
kind: theorem
status: staged
primary_topic: social_choice
topics:
  - social_choice
  - social_choice.fair_division
  - social_choice.fair_division.indivisible
uses:
  - social_choice.fair_division.indivisible.efx
lean:
  modules:
    - EconCSLib.SocialChoice.FairDivision.Indivisible.Fairness
  declarations:
    - SocialChoice.FairDivision.Indivisible.IsEnvyFree.isEFX_of_mono
verification:
  statement: accepted
  proof: accepted
  alignment: aligned
tags:
  - fair-division
  - indivisible
  - envy-free
  - efx
  - monotonicity
---

# EF ⇒ EFX (Monotone Valuations)

**Theorem.** Let $v$ be a *monotone* indivisible valuation —
i.e. $T \subseteq S \Rightarrow v_i(T) \le v_i(S)$ for every $i$ — and
let $A$ be envy-free
([[social_choice.fair_division.indivisible.envy_free]]). Then $A$ is
EFX ([[social_choice.fair_division.indivisible.efx]]).

In Lean: `SocialChoice.FairDivision.Indivisible.IsEnvyFree.isEFX_of_mono`.

## Proof

For agents $i \ne j$ and any $g \in A(j)$:
$$
v_i(A(j) \setminus \{g\}) \;\le\; v_i(A(j)) \;\le\; v_i(A(i)).
$$
The first inequality is the monotonicity hypothesis applied to the
sub-bundle inclusion $A(j) \setminus \{g\} \subseteq A(j)$. The second
is envy-freeness at the pair $(i, j)$. Combined they give the EFX
inequality at the element $g$. Quantifying over $g$ gives EFX. $\square$

## Monotonicity as an explicit hypothesis

The Lean signature takes the monotonicity hypothesis as a plain function
hypothesis `(hmono : ∀ i S T, T ⊆ S → v.val i T ≤ v.val i S)` rather
than as a typeclass, because the abstract `Valuation` interface
([[social_choice.fair_division.indivisible.valuation]]) deliberately
does not bake in monotonicity. Additive valuations with nonnegative
weights are monotone (lemma
[[social_choice.fair_division.indivisible.additive_valuation]]'s
`toValuation_mono`), so the implication automatically applies in the
additive setting.

## Significance

Combined with the unconditional EFX ⇒ EF1
([[social_choice.fair_division.indivisible.efx_implies_ef1]]), this
gives the full chain EF ⇒ EFX ⇒ EF1 for monotone valuations.

For non-monotone valuations the implication may fail: an envy-free
allocation can become un-EFX after item removal if removing a low-value
item *increases* the recipient bundle's value (which only happens for
non-monotone valuations).

## References

- [AGT Chapter 11] Nisan, Roughgarden, Tardos, and Vazirani, *Algorithmic Game Theory*. EF-EFX implication for monotone valuations.
