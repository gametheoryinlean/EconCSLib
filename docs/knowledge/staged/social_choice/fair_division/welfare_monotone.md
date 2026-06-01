---
id: social_choice.fair_division.welfare_monotone
title: Basic Welfare Lemmas
kind: lemma
status: staged
primary_topic: social_choice
topics:
  - social_choice
  - social_choice.fair_division
  - social_choice.fair_division.core
uses:
  - social_choice.fair_division.utilitarian_welfare
  - social_choice.fair_division.egalitarian_welfare
lean:
  modules:
    - EconCSLib.SocialChoice.FairDivision.Welfare
  declarations:
    - SocialChoice.FairDivision.utilitarianWelfare_mono
    - SocialChoice.FairDivision.utilitarianWelfare_unique
    - SocialChoice.FairDivision.egalitarianWelfare_le
verification:
  statement: accepted
  proof: accepted
  alignment: aligned
tags:
  - fair-division
  - welfare
---

# Basic Welfare Lemmas

Three small lemmas keep the welfare layer self-contained.

**Monotonicity of utilitarian welfare.** If $A$ is pointwise weakly
improved by $B$,
$$
\bigl(\forall i,\ u_i(A(i)) \le u_i(B(i))\bigr) \Rightarrow
W_{\mathrm{util}}(u, A) \le W_{\mathrm{util}}(u, B).
$$
In Lean: `utilitarianWelfare_mono` (immediate from `Finset.sum_le_sum`).

**Unique-agent collapse.** If $N$ has exactly one element (the canonical
`default : N`), then $W_{\mathrm{util}}(u, A) = u_{\mathrm{default}}(A(\mathrm{default}))$.
In Lean: `utilitarianWelfare_unique` (`@[simp]`-tagged).

**Egalitarian lower bound on each agent.** Every agent obtains at least
the egalitarian welfare from their share:
$$
\forall i,\ W_{\mathrm{egal}}(u, A) \le u_i(A(i)).
$$
In Lean: `egalitarianWelfare_le` (immediate from `Finset.inf'_le`).

These are the basic algebraic facts used downstream when comparing
utilitarian and egalitarian objectives (see
[[social_choice.fair_division.egal_le_util]]).

## References

- [AGT Chapter 11] Nisan, Roughgarden, Tardos, and Vazirani, *Algorithmic Game Theory*. Welfare aggregations.
