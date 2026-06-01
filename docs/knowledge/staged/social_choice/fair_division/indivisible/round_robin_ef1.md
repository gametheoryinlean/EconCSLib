---
id: social_choice.fair_division.indivisible.round_robin_ef1
title: Round-Robin Is EF1
kind: theorem
status: staged
primary_topic: social_choice
topics:
  - social_choice
  - social_choice.fair_division
  - social_choice.fair_division.indivisible
  - social_choice.fair_division.indivisible.algorithms
uses:
  - social_choice.fair_division.indivisible.round_robin_partition
  - social_choice.fair_division.indivisible.ef1
lean:
  modules:
    - EconCSLib.SocialChoice.FairDivision.Indivisible.RoundRobin
  declarations:
    - SocialChoice.FairDivision.Indivisible.roundRobinAllocation_isEF1
    - SocialChoice.FairDivision.Indivisible.roundRobinRule_isEF1
verification:
  statement: accepted
  proof: accepted
  alignment: aligned
tags:
  - fair-division
  - indivisible
  - round-robin
  - ef1
  - existence
---

# Round-Robin Is EF1

**Theorem.** For any additive valuation
([[social_choice.fair_division.indivisible.additive_valuation]]) with
nonnegative weights and any finite good set, the round-robin allocation
([[social_choice.fair_division.indivisible.round_robin_alloc]]) is
envy-free up to one good ([[social_choice.fair_division.indivisible.ef1]]).

In Lean: `SocialChoice.FairDivision.Indivisible.roundRobinAllocation_isEF1`.
The bundled-rule form
`SocialChoice.FairDivision.Indivisible.roundRobinRule_isEF1` packages
the same result against the bundled additive-instance API.

## Proof intuition

Fix two agents $i \ne j$ with $A(j) \ne \emptyset$. Two cases:

- **Agent $i$ moves before agent $j$ in the turn order.** At every
  round where both agents pick, $i$ picks first and $i$'s
  best-remaining value at that round is at least $j$'s next pick (each
  agent picks their own favourite among the remaining items, and the
  set has only shrunk between $i$'s and $j$'s pick within the same
  round). So $v_i(A(i)) \ge v_i(A(j))$ pointwise, i.e. EF (a
  *strictly stronger* condition than EF1).

- **Agent $i$ moves after agent $j$.** In the first round, $j$ picks
  before $i$ — the only round where $j$ has a strict positional
  advantage over $i$. After removing the first item $j$ takes
  (call it $g_1 = $ `bestGood(j, allGoods)`), agent $i$ has a
  first-pick situation for the remaining items, then both alternate
  fairly. So $v_i(A(j) \setminus \{g_1\}) \le v_i(A(i))$, giving
  the EF1 witness $g = g_1$.

Combining both cases gives EF1 for every $(i, j)$ pair.

The Lean proof is much more detailed — the recursive structure of
`roundRobinAux` forces an induction on the number of rounds, with the
case split appearing inside the inductive step. The file
`RoundRobin.lean` carries ~600 lines of partition/value/turn-order
bookkeeping closing all sorries.

## Significance

This is the *headline existence theorem* for EF1: round-robin gives a
deterministic polynomial-time construction of an EF1 allocation for
any additive valuation. Combined with envy-cycle elimination
([[social_choice.fair_division.indivisible.envy_cycle_ef1]]) it
establishes that EF1 is *unconditionally achievable* in the
indivisible setting (in stark contrast to EF, which fails
[[social_choice.fair_division.indivisible.ef_impossible_two_agents_one_good]]).

## References

- [AGT Chapter 11] Nisan, Roughgarden, Tardos, and Vazirani, *Algorithmic Game Theory*. Round-robin EF1 correctness.
- Caragiannis, Kurokawa, Moulin, Procaccia, Shah, and Wang (2019). "The Unreasonable Fairness of Maximum Nash Welfare". *EC*.
