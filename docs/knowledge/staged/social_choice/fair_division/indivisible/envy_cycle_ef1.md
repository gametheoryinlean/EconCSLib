---
id: social_choice.fair_division.indivisible.envy_cycle_ef1
title: Envy-Cycle Elimination Produces EF1
kind: theorem
status: staged
primary_topic: social_choice
topics:
  - social_choice
  - social_choice.fair_division
  - social_choice.fair_division.indivisible
  - social_choice.fair_division.indivisible.algorithms
uses:
  - social_choice.fair_division.indivisible.envy_cycle_algorithm
  - social_choice.fair_division.indivisible.ef1
lean:
  modules:
    - EconCSLib.SocialChoice.FairDivision.Indivisible.EnvyCycle
  declarations:
    - SocialChoice.FairDivision.Indivisible.envyCycleAllocation_isAllocation
    - SocialChoice.FairDivision.Indivisible.envyCycleAllocation_isEF1
    - SocialChoice.FairDivision.Indivisible.envyCycleRule_isEF1
verification:
  statement: accepted
  proof: accepted
  alignment: aligned
tags:
  - fair-division
  - indivisible
  - envy-cycle
  - ef1
  - existence
---

# Envy-Cycle Elimination Produces EF1

**Theorem.** For an additive instance
([[social_choice.fair_division.indivisible.additive_instance]]) with
nonnegative weights on a finite nonempty agent type and a finite good
set, the envy-cycle elimination algorithm
([[social_choice.fair_division.indivisible.envy_cycle_algorithm]])
returns a complete EF1 allocation
([[social_choice.fair_division.indivisible.ef1]]).

In Lean: two paired theorems —

- `envyCycleAllocation_isAllocation`: the output is a complete
  partition ([[social_choice.fair_division.indivisible.allocation]]).
- `envyCycleAllocation_isEF1`: the output is EF1.
- Bundled-rule form: `envyCycleRule_isEF1`.

## Proof intuition

The EF1 invariant — "for every $(i, j)$ with non-empty $A(j)$, some
item $g \in A(j)$ exists whose removal eliminates envy" — is
maintained throughout the loop:

- **Cycle elimination is innocent.** Bundle rotations along envy cycles
  ([[social_choice.fair_division.indivisible.rotate_bundles]]) only
  *improve* per-agent utility. If the pre-rotation allocation was EF1,
  the post-rotation allocation is too (the EF1 witness item for each
  $(i, j)$ pair can be re-mapped through the rotation).

- **Item assignment to a source is innocent.** Adding an item $g$ to
  a source agent $s$ creates new envy at most against $s$. For any
  envier $i \ne s$, removing $g$ from $A(s) \cup \{g\}$ recovers
  $A(s)$; since $s$ was a source pre-assignment, no one envied $s$
  before, so $v_i(A(s)) \le v_i(A(i))$, giving the EF1 witness.

## Strength compared to round-robin

Both round-robin
([[social_choice.fair_division.indivisible.round_robin_ef1]]) and
envy-cycle elimination produce EF1 allocations from an
`AdditiveInstance` with nonneg weights. The differences:

- *Round-robin* is non-adaptive: turn order is fixed in advance,
  every agent picks their favourite remaining item on their turn.
- *Envy-cycle elimination* is adaptive: it gives the next item to a
  "source" agent in the current envy graph, after rotating bundles
  along any envy cycles. The adaptive choice carries the additional
  guarantee that no agent's utility ever decreases
  ([[social_choice.fair_division.indivisible.rotate_bundles]]'s
  `rotateBundles_nondecreasing` lifted through
  [[social_choice.fair_division.indivisible.eliminate_all_cycles]]'s
  `eliminateAllCycles_nondecreasing`).

The original Lipton-Markakis-Mossel-Saberi (2004) theorem applies to
arbitrary (not necessarily additive) valuations; the current Lean
formalisation specialises to additive instances, mirroring round-robin
and matching the bundled `AdditiveInstance` API. Lifting to general
`Valuation` is a planned future refinement.

## References

- Lipton, Markakis, Mossel, and Saberi (2004). "On Approximately Fair Allocations of Indivisible Goods". *EC*. Original EF1 + Pareto-improvement theorem.
- [AGT Chapter 11] Nisan, Roughgarden, Tardos, and Vazirani, *Algorithmic Game Theory*.
