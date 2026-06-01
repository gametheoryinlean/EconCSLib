---
id: social_choice.fair_division.indivisible.rotate_bundles
title: Bundle Rotation
kind: definition
status: formalized
primary_topic: social_choice
topics:
  - social_choice
  - social_choice.fair_division
  - social_choice.fair_division.indivisible
  - social_choice.fair_division.indivisible.algorithms
uses:
  - social_choice.fair_division.indivisible.envy_cycle
lean:
  modules:
    - EconCSLib.SocialChoice.FairDivision.Indivisible.EnvyCycle
  declarations:
    - SocialChoice.FairDivision.Indivisible.rotateBundles
    - SocialChoice.FairDivision.Indivisible.rotateBundles_not_mem
    - SocialChoice.FairDivision.Indivisible.rotateBundles_mem
    - SocialChoice.FairDivision.Indivisible.rotateBundles_isAllocation
    - SocialChoice.FairDivision.Indivisible.rotateBundles_improves
    - SocialChoice.FairDivision.Indivisible.rotateBundles_nondecreasing
verification:
  definition: accepted
  proof: accepted
  alignment: aligned
tags:
  - fair-division
  - indivisible
  - envy-cycle
  - rotation
  - algorithms
---

# Bundle Rotation

Given a list of agents $l = [i_0, i_1, \dots, i_{k-1}]$, the *bundle
rotation* operation shifts bundles cyclically along the list:
$$
\mathrm{rotate}(A, l)(i_j) = A(i_{(j+1)\ \text{mod}\ k}) \text{ for } j < k,
\qquad
\mathrm{rotate}(A, l)(i) = A(i) \text{ for } i \notin l.
$$

In Lean: `rotateBundles A l : Allocation N G`, requiring `[DecidableEq N]`.

## Structural lemmas

- **Non-members keep their bundles.** `rotateBundles_not_mem`:
  $i \notin l \Rightarrow \mathrm{rotate}(A, l)(i) = A(i)$.
- **Members shift cyclically.** `rotateBundles_mem`: for $i \in l$,
  the bundle rotates by one position along $l$.

## Allocation preservation

- `rotateBundles_isAllocation` (with `[Fintype N]`): if $A$ is a
  complete partition of `allGoods` and $l$ is a list of distinct
  agents, then `rotate(A, l)` is also a complete partition of
  `allGoods`.

This is immediate: rotation permutes the bundles, so disjointness and
cover are preserved.

## Utility properties along an envy cycle

When $l$ is an envy cycle
([[social_choice.fair_division.indivisible.envy_cycle]]) every member
*strictly improves* under the rotation:

- `rotateBundles_improves`: for every $i \in l$,
  $v_i(A(i)) < v_i(\mathrm{rotate}(A, l)(i))$.

(The argument: $i$ in the cycle envies its cyclic successor $j$, i.e.
$v_i(A(j)) > v_i(A(i))$; rotation gives $i$ the bundle of $j$, so $i$'s
new utility is exactly $v_i(A(j))$, which strictly exceeds the old.)

For non-members, rotation is trivially nondecreasing:

- `rotateBundles_nondecreasing`: every agent's new utility is at least
  their old utility.

## Why this works

The combination of "members strictly improve" and "non-members
non-decrease" is what makes envy-cycle elimination *monotone* in
utility space. This is the key to using a *Pareto-domination count* as
the termination measure
([[social_choice.fair_division.indivisible.pareto_dom_count]]).

## References

- Lipton, Markakis, Mossel, and Saberi (2004). "On Approximately Fair Allocations of Indivisible Goods". *EC*. Bundle rotation along envy cycles.
