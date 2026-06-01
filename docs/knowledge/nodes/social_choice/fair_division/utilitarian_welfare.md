---
id: social_choice.fair_division.utilitarian_welfare
title: Utilitarian Welfare and Utilitarian Optimality
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
    - SocialChoice.FairDivision.utilitarianWelfare
    - SocialChoice.FairDivision.IsUtilitarianOptimal
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
tags:
  - fair-division
  - welfare
  - utilitarian
  - efficiency
---

# Utilitarian Welfare and Utilitarian Optimality

For a finite population $N$, a utility profile $u : N \to S \to \mathbb{R}$,
and an allocation $A : N \to S$ ([[social_choice.fair_division.allocation]]),
the *utilitarian (social) welfare* is the sum of agents' utilities from
their own shares:
$$
W_{\mathrm{util}}(u, A) = \sum_{i \in N} u_i(A(i)).
$$

In Lean: `SocialChoice.FairDivision.utilitarianWelfare` (noncomputable, uses
`∑ i : N` on `Fintype N`).

An allocation $A$ is *utilitarian-optimal* w.r.t. a feasibility predicate
$F$ if no feasible allocation has strictly larger utilitarian welfare:
$$
\forall B,\ F(B) \Rightarrow W_{\mathrm{util}}(u, B) \le W_{\mathrm{util}}(u, A).
$$

In Lean: `SocialChoice.FairDivision.IsUtilitarianOptimal`.

The accompanying basic lemmas in `Welfare.lean` say:

- $W_{\mathrm{util}}$ is monotone in the per-agent utility:
  $\forall i,\ u_i(A_i) \le u_i(B_i) \Rightarrow W_{\mathrm{util}}(u, A) \le W_{\mathrm{util}}(u, B)$.
- For a unique-agent population it collapses to the single agent's
  utility.

Utilitarian-optimal allocations are Pareto optimal
([[social_choice.fair_division.pareto_optimal]]) but the converse fails:
PO is a much weaker condition.

## References

- [AGT Chapter 11] Nisan, Roughgarden, Tardos, and Vazirani, *Algorithmic Game Theory*. Utilitarian social welfare.
