---
id: social_choice.fair_division.egalitarian_welfare
title: Egalitarian (Maximin) Welfare
kind: definition
status: formalized
primary_topic: social_choice
topics:
  - social_choice
  - social_choice.fair_division
  - social_choice.fair_division.core
uses:
  - social_choice.fair_division.allocation
lean:
  modules:
    - EconCSLib.SocialChoice.FairDivision.Welfare
  declarations:
    - SocialChoice.FairDivision.egalitarianWelfare
    - SocialChoice.FairDivision.IsMaxmin
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
tags:
  - fair-division
  - welfare
  - egalitarian
  - maximin
  - efficiency
---

# Egalitarian (Maximin) Welfare

For a finite nonempty population $N$, a utility profile $u : N \to S \to
\mathbb{R}$, and an allocation $A : N \to S$
([[social_choice.fair_division.allocation]]), the *egalitarian welfare*
is the minimum agent utility:
$$
W_{\mathrm{egal}}(u, A) = \min_{i \in N} u_i(A(i)).
$$

In Lean: `SocialChoice.FairDivision.egalitarianWelfare`, defined via
`Finset.univ.inf'` to handle the minimum over a finite nonempty type.

An allocation $A$ is *maximin* w.r.t. a feasibility predicate $F$ if no
feasible allocation has a strictly larger minimum utility:
$$
\forall B,\ F(B) \Rightarrow W_{\mathrm{egal}}(u, B) \le W_{\mathrm{egal}}(u, A).
$$

In Lean: `SocialChoice.FairDivision.IsMaxmin`.

Basic facts (`Welfare.lean`):

- $W_{\mathrm{egal}}(u, A) \le u_i(A(i))$ for every agent $i$.
- *Egalitarian ≤ utilitarian / n:* if every agent's utility is bounded
  below by $W_{\mathrm{egal}}$, then $|N| \cdot W_{\mathrm{egal}}(u, A) \le
  W_{\mathrm{util}}(u, A)$
  ([[social_choice.fair_division.utilitarian_welfare]]). This is the
  Lean lemma `nsmul_egalitarianWelfare_le_utilitarianWelfare` and matches
  the AM-min inequality.

Egalitarian welfare prioritizes the worst-off agent; utilitarian welfare
maximizes the aggregate. They generally trade off, and a single
allocation rarely maximizes both.

## References

- [AGT Chapter 11] Nisan, Roughgarden, Tardos, and Vazirani, *Algorithmic Game Theory*. Egalitarian (Rawlsian) welfare.
