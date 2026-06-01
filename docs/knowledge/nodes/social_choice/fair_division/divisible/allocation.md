---
id: social_choice.fair_division.divisible.allocation
title: Divisible Allocation
kind: definition
status: formalized
primary_topic: social_choice
topics:
  - social_choice
  - social_choice.fair_division
  - social_choice.fair_division.divisible
uses:
  - social_choice.fair_division.allocation
lean:
  modules:
    - EconCSLib.SocialChoice.FairDivision.Divisible.Allocation
  declarations:
    - SocialChoice.FairDivision.Divisible.Allocation
    - SocialChoice.FairDivision.Divisible.IsAllocation
    - SocialChoice.FairDivision.Divisible.IsContiguousAllocation
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
tags:
  - fair-division
  - divisible
  - cake-cutting
  - allocation
---

# Divisible Allocation

A *divisible allocation* on a measurable cake $\Omega$ assigns each agent
$i \in N$ a *piece* $A(i) \subseteq \Omega$. Concretely the type is a
specialization of the generic allocation alias
([[social_choice.fair_division.allocation]]):
$$
\mathrm{Allocation}\ N\ \Omega \;=\;
\mathrm{FairDivision.Allocation}\ N\ (\mathrm{Set}\ \Omega) \;=\; N \to \mathrm{Set}\ \Omega.
$$

In Lean: `SocialChoice.FairDivision.Divisible.Allocation N Ω`.

## Partition predicate

A *complete* divisible allocation is a measurable partition of the cake. In
Lean: `IsAllocation` is a structure with three fields:

- `measurable : ∀ i, MeasurableSet (A i)` — each piece is measurable;
- `disjoint  : ∀ i ≠ j, Disjoint (A i) (A j)` — distinct agents get
  disjoint pieces;
- `cover     : ⋃ i, A i = Set.univ` — every cake-point belongs to some
  agent's piece.

The class hypotheses `[MeasurableSpace Ω]` and `[Fintype N]` are needed for
the union/disjointness conditions to make sense.

A small derived fact `IsAllocation.mem_iUnion` says every $x \in \Omega$
belongs to some $A(i)$.

## Contiguous allocations on $\mathbb{R}$

A specialised predicate `IsContiguousAllocation A` (on $A : N \to
\mathrm{Set}\ \mathbb{R}$) asserts that every piece is *order-connected*
(an interval). This is the natural restriction for Stromquist's EF
existence theorem: the EF allocation constructed by KKM is contiguous.

## References

- [AGT Chapter 13] Nisan, Roughgarden, Tardos, and Vazirani, *Algorithmic Game Theory*. Allocations in cake-cutting.
- Robertson, J. M. and Webb, W. A. (1998). *Cake-Cutting Algorithms*.
