---
id: social_choice.fair_division.divisible.ef_exists_and_proportional
title: EF + Proportional Existence (Stromquist Corollary)
kind: theorem
status: staged
primary_topic: social_choice
topics:
  - social_choice
  - social_choice.fair_division
  - social_choice.fair_division.divisible
uses:
  - social_choice.fair_division.divisible.ef_exists
  - social_choice.fair_division.divisible.ef_implies_proportional
lean:
  modules:
    - EconCSLib.SocialChoice.FairDivision.Divisible.Existence
  declarations:
    - SocialChoice.FairDivision.Divisible.ef_exists_and_proportional
verification:
  statement: accepted
  proof: accepted
  alignment: aligned
tags:
  - fair-division
  - divisible
  - stromquist
  - envy-free
  - proportional
  - existence
---

# EF + Proportional Existence (Stromquist Corollary)

**Theorem.** For every $n \ge 1$ and every family of finite non-atomic
measures $\mu : \mathrm{Fin}\ n \to \mathrm{Measure}\ I$ on $I = [0, 1]$,
there exists a complete measurable partition that is **both**
envy-free and proportional.

In Lean: `SocialChoice.FairDivision.Divisible.ef_exists_and_proportional`.

## Proof

A two-step composition:

1. Stromquist's EF existence
   ([[social_choice.fair_division.divisible.ef_exists]]) yields an EF
   allocation $A$.

2. EF implies proportional for measure valuations
   ([[social_choice.fair_division.divisible.ef_implies_proportional]])
   gives the proportionality bound on the same $A$.

## Why list this as a separate node

Two reasons:

- Many downstream contexts want a single statement asserting both
  fairness notions hold together (typical for textbook statements of
  "fair division exists for cake-cutting").
- It exposes the *strength gap* between EF and PROP in the divisible
  setting: PROP is implied by EF here for free, whereas in the
  indivisible setting the implication only holds for additive
  valuations on complete allocations
  ([[social_choice.fair_division.indivisible.ef_implies_proportional_additive]])
  and EF itself need not exist.

The bundled-instance form sits in
[[social_choice.fair_division.divisible.measure_instance_existence]].

## References

- Stromquist, W. (1980). "How to Cut a Cake Fairly". *Amer. Math. Monthly* 87: 640–644.
- [AGT Chapter 13] Nisan, Roughgarden, Tardos, and Vazirani, *Algorithmic Game Theory*.
