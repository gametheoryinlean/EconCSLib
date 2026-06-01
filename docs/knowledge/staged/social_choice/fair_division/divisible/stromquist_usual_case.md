---
id: social_choice.fair_division.divisible.stromquist_usual_case
title: Stromquist — Usual Case (U Covers the Simplex)
kind: theorem
status: staged
primary_topic: social_choice
topics:
  - social_choice
  - social_choice.fair_division
  - social_choice.fair_division.divisible
  - social_choice.fair_division.divisible.stromquist
uses:
  - social_choice.fair_division.divisible.stromquist_assignment
lean:
  modules:
    - EconCSLib.SocialChoice.FairDivision.Divisible.Existence
  declarations:
    - SocialChoice.FairDivision.Divisible.strom_usual_case
verification:
  statement: accepted
  proof: accepted
  alignment: aligned
tags:
  - fair-division
  - divisible
  - stromquist
  - kkm
  - envy-free
---

# Stromquist — Usual Case (U Covers the Simplex)

**Theorem (usual case).** If the agent-preference unions
$\{U(i) : i \in \mathrm{Fin}\ n\}$
([[social_choice.fair_division.divisible.stromquist_U]]) cover the
division simplex $S$, then there exists a complete measurable
envy-free allocation
([[social_choice.fair_division.divisible.envy_free]]).

## Proof

1. **KKM input.** Each $U(i)$ is open, and $U(i)$ does not meet the face
   opposite vertex $i$. With the assumption that $\{U(i)\}_i$ covers $S$,
   the *KKM lemma in open form* (`EconCSLib.Topology.KKM.kkm_open_cover`)
   applies and yields a point $x^* \in \bigcap_i U(i)$.

2. **Assignment.** Apply the fair-assignment lemma
   ([[social_choice.fair_division.divisible.stromquist_assignment]]) at
   $x^*$ to produce an envy-free allocation
   $A : \mathrm{Fin}\ n \to \mathrm{Set}\ \mathbb{R}$.

The construction goes through *contiguous* pieces (intervals), so the
resulting EF allocation also satisfies the contiguous-allocation
predicate. This is sharper than what the general EF existence theorem
requires.

## Role in the overall proof

This is one of two cases in Stromquist's proof. The "unusual case"
arises when $\{U(i)\}_i$ does *not* cover $S$ — there exist divisions
$x$ where some agent is indifferent between two or more pieces. The
shifted-cell refinement
([[social_choice.fair_division.divisible.stromquist_shifted_cells]],
[[social_choice.fair_division.divisible.stromquist_unusual_case]])
handles that case by approximation and limit-passing.

## References

- Stromquist, W. (1980). "How to Cut a Cake Fairly". *Amer. Math. Monthly* 87: 640–644.
- Su, F. E. (1999). "Rental Harmony: Sperner's Lemma in Fair Division". *Amer. Math. Monthly* 106.
