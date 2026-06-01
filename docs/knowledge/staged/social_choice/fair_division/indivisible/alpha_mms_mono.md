---
id: social_choice.fair_division.indivisible.alpha_mms_mono
title: α-MMS — Monotonicity and Endpoint Lemmas
kind: theorem
status: staged
primary_topic: social_choice
topics:
  - social_choice
  - social_choice.fair_division
  - social_choice.fair_division.indivisible
  - social_choice.fair_division.indivisible.mms
uses:
  - social_choice.fair_division.indivisible.mms_iff_alpha_one
lean:
  modules:
    - EconCSLib.SocialChoice.FairDivision.Indivisible.MMS
  declarations:
    - SocialChoice.FairDivision.Indivisible.isAlphaMMS_mono_alpha
    - SocialChoice.FairDivision.Indivisible.isAlphaMMS_zero
    - SocialChoice.FairDivision.Indivisible.IsMaxminShare.isAlphaMMS
verification:
  statement: accepted
  proof: accepted
  alignment: aligned
tags:
  - fair-division
  - indivisible
  - mms
  - alpha-mms
  - monotonicity
---

# α-MMS — Monotonicity and Endpoint Lemmas

Three basic structural results for the α-MMS predicate
([[social_choice.fair_division.indivisible.is_alpha_mms]]).

## Monotonicity in α

`isAlphaMMS_mono_alpha`: if $\alpha_2 \le \alpha_1$ and $A$ is
$\alpha_1$-MMS, then $A$ is also $\alpha_2$-MMS.

*Proof.* For each $i$, $\alpha_2 \cdot \mathrm{MMS}_i \le \alpha_1 \cdot \mathrm{MMS}_i \le v_i(A(i))$.
The first inequality uses $\alpha_2 \le \alpha_1$ and nonnegativity of
$\mathrm{MMS}_i$ ([[social_choice.fair_division.indivisible.mms_value_bounds]]).

## Trivial bottom

`isAlphaMMS_zero`: for any allocation with nonnegative bundle values,
0-MMS holds vacuously.

*Proof.* The predicate becomes $0 \cdot \mathrm{MMS}_i \le v_i(A(i))$,
i.e. $0 \le v_i(A(i))$. Nonnegativity of the values closes this.

## Bridge from exact MMS

`IsMaxminShare.isAlphaMMS`: if $A$ satisfies the exact MMS guarantee
([[social_choice.fair_division.indivisible.maximin_share]]), then for
every $\alpha \in [0, 1]$, $A$ is α-MMS.

*Proof.* Combine `isMaxminShare_iff_isAlphaMMS_one`
([[social_choice.fair_division.indivisible.mms_iff_alpha_one]]) with
the monotonicity lemma above: exact MMS gives 1-MMS, and 1-MMS implies
α-MMS for any $\alpha \le 1$.

## Use

These three lemmas form the *monotonicity scaffolding* that justifies
α-MMS as a coherent approximation hierarchy. Existence results for
$\alpha < 1$ (e.g. Procaccia–Wang $\frac{2}{3}$, GHSSY $\frac{3}{4}$)
are stated in terms of α-MMS and inherit weaker variants for free.

## References

- Procaccia, A. D. and Wang, J. (2014). "Fair Enough: Guaranteeing Approximate Maximin Shares". *EC*.
- [AGT Chapter 11] Nisan, Roughgarden, Tardos, and Vazirani, *Algorithmic Game Theory*. α-MMS approximation.
