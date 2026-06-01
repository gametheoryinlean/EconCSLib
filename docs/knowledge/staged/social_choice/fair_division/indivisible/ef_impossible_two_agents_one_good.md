---
id: social_choice.fair_division.indivisible.ef_impossible_two_agents_one_good
title: EF Impossibility — Two Agents, One Good
kind: theorem
status: staged
primary_topic: social_choice
topics:
  - social_choice
  - social_choice.fair_division
  - social_choice.fair_division.indivisible
uses:
  - social_choice.fair_division.indivisible.envy_free
lean:
  modules:
    - EconCSLib.SocialChoice.FairDivision.Indivisible.ImpossibilityEF
  declarations:
    - SocialChoice.FairDivision.Indivisible.ef_impossible_two_agents_one_good
verification:
  statement: accepted
  proof: accepted
  alignment: aligned
tags:
  - fair-division
  - indivisible
  - envy-free
  - impossibility
  - example
---

# EF Impossibility — Two Agents, One Good

**Theorem.** Let $G$ be a type of goods with `[DecidableEq G]`, let
$g \in G$ be a distinguished good, and let $v : \mathrm{Valuation}\ (\mathrm{Fin}\ 2)\ G$
be a valuation such that *both* agents strictly prefer the singleton
$\{g\}$ to the empty bundle:
$$
v_0(\emptyset) < v_0(\{g\}), \qquad v_1(\emptyset) < v_1(\{g\}).
$$

For every complete allocation $A$ of `allGoods = {g}`, $A$ is **not**
envy-free.

In Lean: `SocialChoice.FairDivision.Indivisible.ef_impossible_two_agents_one_good`.

## Proof

By completeness, $g$ must lie in some agent's bundle. By disjointness,
the other agent gets $\emptyset$ (and the lucky one gets exactly
$\{g\}$). Without loss of generality say agent $0$ holds $\{g\}$ and
agent $1$ holds $\emptyset$. Envy-freeness from agent 1's perspective
demands $v_1(A(0)) \le v_1(A(1))$, i.e.\ $v_1(\{g\}) \le v_1(\emptyset)$.
But the hypothesis $v_1(\emptyset) < v_1(\{g\})$ contradicts this.

The proof uses `Finset.disjoint_left` to deduce $A(1) = \emptyset$ from
the partition / completeness facts, and `fin_cases` to split on whether
agent 0 or agent 1 holds $g$.

## Significance

This is the canonical impossibility result for indivisible fair
division: even for the simplest instance — two agents, one item, both
wanting it — there is no envy-free complete allocation. By contrast,
EF for divisible goods is always achievable
([[social_choice.fair_division.divisible.cut_and_choose_ef_exists]]).

It motivates the standard relaxations:

- **EF1** ([[social_choice.fair_division.indivisible.ef1]]): allow
  envy that vanishes after removing some single item. Trivially
  satisfied here (removing $g$ from $\{g\}$ yields $\emptyset$, which
  agent 1 weakly prefers to their own empty share).
- **EFX** ([[social_choice.fair_division.indivisible.efx]]): the
  stronger "any-item" relaxation.
- **MMS** ([[social_choice.fair_division.indivisible.maximin_share]]):
  approximate-fairness in expected-self-partition terms.

## References

- [AGT Chapter 11] Nisan, Roughgarden, Tardos, and Vazirani, *Algorithmic Game Theory*. EF impossibility for indivisible goods.
