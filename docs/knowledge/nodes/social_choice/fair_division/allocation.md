---
id: social_choice.fair_division.allocation
title: Allocation
kind: definition
status: formalized
primary_topic: social_choice
topics:
  - social_choice
  - social_choice.fair_division
  - social_choice.fair_division.core
uses: []
lean:
  modules:
    - EconCSLib.SocialChoice.FairDivision.Basic
  declarations:
    - SocialChoice.FairDivision.Allocation
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
tags:
  - fair-division
  - allocation
---

# Allocation

For a population $N$ and a share type $S$, an *allocation* is a function
$A : N \to S$ assigning each agent the share they receive.

In Lean: `SocialChoice.FairDivision.Allocation N S := N → S`, a plain type
alias. Structural feasibility (partitioning a cake into disjoint pieces, or
splitting items into disjoint bundles) is *not* baked into this type — it
is stated separately by predicates such as the divisible
`IsAllocation` ([[social_choice.fair_division.divisible.allocation]]) or
the indivisible `IsAllocation`
([[social_choice.fair_division.indivisible.allocation]]).

The separation is deliberate: many algorithms manipulate raw allocations
(round-robin steps, cycle rotations) before establishing that the result
is a valid partition.

## References

- [AGT Chapter 11] Nisan, Roughgarden, Tardos, and Vazirani, *Algorithmic Game Theory*. Allocation as a function from agents to shares.
- [AGT Chapter 13] Nisan et al., *Algorithmic Game Theory*. Allocations for cake-cutting.
