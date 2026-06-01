---
id: social_choice.fair_division.pareto_optimal
title: Pareto Optimal Allocation
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
    - EconCSLib.SocialChoice.FairDivision.Fairness
  declarations:
    - SocialChoice.FairDivision.IsParetoOptimal
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
tags:
  - fair-division
  - pareto
  - efficiency
---

# Pareto Optimal Allocation

For a feasibility predicate $F : \mathrm{Allocation}\ N\ S \to \mathrm{Prop}$,
a utility profile $u : N \to S \to \mathbb{R}$, and an allocation $A$
([[social_choice.fair_division.allocation]]), $A$ is *Pareto optimal* (PO)
if no feasible allocation weakly Pareto-improves on it with at least one
strict improvement:
$$
\neg \exists B,\ F(B) \;\wedge\;
\bigl(\forall i,\ u_i(A(i)) \le u_i(B(i))\bigr) \;\wedge\;
\bigl(\exists i,\ u_i(A(i)) < u_i(B(i))\bigr).
$$

In Lean: `SocialChoice.FairDivision.IsParetoOptimal`. The feasibility
predicate is a plain hypothesis (rather than being baked into a class),
so the same definition applies to divisible and indivisible
specializations
([[social_choice.fair_division.indivisible.pareto_optimal]]).

PO is the classical efficiency yardstick: it asks only that no other
feasible allocation can make every agent at least as well off and someone
strictly better off.

In the indivisible-goods setting, the combination *EF1 + PO* always
exists via the *maximum Nash welfare* allocation
(Caragiannis–Kurokawa–Moulin–Procaccia–Shah–Wang 2019) and (with a
different output) via *envy-cycle elimination*
([[social_choice.fair_division.indivisible.envy_cycle_algorithm]]).

## References

- [AGT Chapter 11] Nisan, Roughgarden, Tardos, and Vazirani, *Algorithmic Game Theory*. Pareto optimality in fair division.
