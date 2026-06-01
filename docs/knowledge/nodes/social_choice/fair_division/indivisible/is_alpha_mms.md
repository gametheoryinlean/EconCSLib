---
id: social_choice.fair_division.indivisible.is_alpha_mms
title: α-MMS Allocation
kind: definition
status: formalized
primary_topic: social_choice
topics:
  - social_choice
  - social_choice.fair_division
  - social_choice.fair_division.indivisible
  - social_choice.fair_division.indivisible.mms
uses:
  - social_choice.fair_division.indivisible.mms_value
lean:
  modules:
    - EconCSLib.SocialChoice.FairDivision.Indivisible.MMS
  declarations:
    - SocialChoice.FairDivision.Indivisible.IsAlphaMMS
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
tags:
  - fair-division
  - indivisible
  - mms
  - alpha-mms
  - approximation
---

# α-MMS Allocation

For a parameter $\alpha \in [0, 1]$, an allocation $A$ is *α-MMS* if
every agent's bundle value is at least an $\alpha$-fraction of their
maximin share value ([[social_choice.fair_division.indivisible.mms_value]]):
$$
\forall i \in N,\ \alpha \cdot \mathrm{MMS}_i \le v_i(A(i)).
$$

In Lean: `SocialChoice.FairDivision.Indivisible.IsAlphaMMS`, with
hypotheses `[Fintype N] [DecidableEq G]`.

## Special cases

- $\alpha = 1$: exact MMS, equivalent to
  `IsMaxminShare` ([[social_choice.fair_division.indivisible.maximin_share]]).
  The equivalence is proved in
  [[social_choice.fair_division.indivisible.mms_iff_alpha_one]].
- $\alpha = 0$: trivially satisfied by every allocation (the
  hypothesis becomes $0 \le v_i(A(i))$, which holds whenever values
  are nonnegative; see
  [[social_choice.fair_division.indivisible.alpha_mms_mono]]'s
  `isAlphaMMS_zero`).

## Why approximate

Exact MMS allocations *need not exist* — the Procaccia–Wang (2014)
counterexample shows that some additive instances admit no exact-MMS
allocation. The α-MMS notion preserves the "fraction of self-guaranteed
worst piece" intuition while always being achievable for some $\alpha
< 1$:

- $\alpha = \frac{2}{3}$ — Procaccia–Wang (2014).
- $\alpha = \frac{3}{4}$ — Ghodsi–Hajiaghayi–Seddighin–Seddighin–Yami
  (2018), independently improved by Garg–Taki (2020) and others.
- The current state-of-the-art (as of mid-2020s) sits slightly above
  $\frac{3}{4}$ for additive valuations and is an active research
  area.

## Monotonicity in α

Smaller α makes the predicate strictly weaker
([[social_choice.fair_division.indivisible.alpha_mms_mono]]'s
`isAlphaMMS_mono_alpha`): if $A$ is $\alpha_1$-MMS and $\alpha_2 \le
\alpha_1$, then $A$ is also $\alpha_2$-MMS.

## References

- Procaccia, A. D. and Wang, J. (2014). "Fair Enough: Guaranteeing Approximate Maximin Shares". *EC*.
- Budish, E. (2011). "The Combinatorial Assignment Problem". *J. Pol. Econ.*
- [AGT Chapter 11] Nisan, Roughgarden, Tardos, and Vazirani, *Algorithmic Game Theory*.
