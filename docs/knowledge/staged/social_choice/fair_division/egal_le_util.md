---
id: social_choice.fair_division.egal_le_util
title: Egalitarian Welfare Lower-Bounds Utilitarian Welfare
kind: lemma
status: staged
primary_topic: social_choice
topics:
  - social_choice
  - social_choice.fair_division
  - social_choice.fair_division.core
uses:
  - social_choice.fair_division.welfare_monotone
lean:
  modules:
    - EconCSLib.SocialChoice.FairDivision.Welfare
  declarations:
    - SocialChoice.FairDivision.nsmul_egalitarianWelfare_le_utilitarianWelfare
verification:
  statement: accepted
  proof: accepted
  alignment: aligned
tags:
  - fair-division
  - welfare
---

# Egalitarian Welfare Lower-Bounds Utilitarian Welfare

**Lemma.** For a finite nonempty population $N$, a utility profile $u$,
and an allocation $A$, if every agent's utility is bounded below by the
egalitarian welfare
([[social_choice.fair_division.egalitarian_welfare]]) — for instance, by
the lemma `egalitarianWelfare_le` from
[[social_choice.fair_division.welfare_monotone]] — then
$$
|N| \cdot W_{\mathrm{egal}}(u, A) \;\le\; W_{\mathrm{util}}(u, A).
$$

In Lean: `SocialChoice.FairDivision.nsmul_egalitarianWelfare_le_utilitarianWelfare`,
stated as `Fintype.card N • egalitarianWelfare u A ≤ utilitarianWelfare u A`
to avoid division.

*Proof.* Summing the agentwise lower bound $W_{\mathrm{egal}} \le u_i(A(i))$
over all $i$ gives the constant sum $|N| \cdot W_{\mathrm{egal}}$ on the
left and the utilitarian welfare on the right. $\square$

This is the standard *minimum ≤ average* inequality for finitely many
real numbers, packaged so that it relates the two welfare aggregations
without scaling. It quantifies the slack between "every agent at least
$W_{\mathrm{egal}}$" (egalitarian) and "agents together at least
$W_{\mathrm{util}}$" (utilitarian).

## References

- [AGT Chapter 11] Nisan, Roughgarden, Tardos, and Vazirani, *Algorithmic Game Theory*. Comparing welfare aggregations.
