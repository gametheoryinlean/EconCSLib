---
id: social_choice.fair_division.divisible.stromquist_preference_sets
title: Stromquist Preference Sets A(i, j)
kind: definition
status: formalized
primary_topic: social_choice
topics:
  - social_choice
  - social_choice.fair_division
  - social_choice.fair_division.divisible
  - social_choice.fair_division.divisible.stromquist
uses:
  - social_choice.fair_division.divisible.stromquist_value_continuous
lean:
  modules:
    - EconCSLib.SocialChoice.FairDivision.Divisible.Existence
  declarations:
    - SocialChoice.FairDivision.Divisible.strom_A
    - SocialChoice.FairDivision.Divisible.strom_A_closed
    - SocialChoice.FairDivision.Divisible.strom_A_covers
verification:
  definition: accepted
  proof: accepted
  alignment: aligned
tags:
  - fair-division
  - divisible
  - stromquist
  - kkm
---

# Stromquist Preference Sets A(i, j)

For each agent $j \in \mathrm{Fin}\ n$ and piece index $i \in \mathrm{Fin}\ n$,
the *preference set* $A(i, j)$ is the set of simplex points where piece $i$
is a value-maximizer for agent $j$:
$$
A(i, j) \;=\; \{x \in S \mid \forall k \in \mathrm{Fin}\ n,\ v(x, j, k) \le v(x, j, i)\}.
$$

In Lean: `strom_A i j`.

## Closedness

`strom_A_closed`: $A(i, j)$ is closed in $\mathrm{Fin}\ n \to \mathbb{R}$.

*Proof.* The defining condition is a conjunction of $n$ inequalities of
the form $v(x, j, k) \le v(x, j, i)$. Each inequality cuts out a closed
half-space because both sides are continuous in $x$
([[social_choice.fair_division.divisible.stromquist_value_continuous]]).
The intersection of finitely many closed sets is closed.

## Cover property

`strom_A_covers`: for each fixed $j$, the family $\{A(i, j) : i \in \mathrm{Fin}\ n\}$
covers the simplex $S$.

*Proof.* For any $x \in S$, agent $j$'s values $v(x, j, k)$ over $k$ form
a finite collection of reals; some $i$ achieves the maximum. That $i$
witnesses $x \in A(i, j)$.

## Why this matters for KKM

The pair (closed $A(i, j)$, family that covers the simplex) is exactly
the input shape for a KKM-type argument: combined with the "facets-don't-
touch" property of `strom_A` (`strom_A` does not intersect the face
opposite vertex $i$), this lets the KKM lemma find a common point in
$\bigcap_i \bigcup_j A(i, j)$ — which yields a fair division.

The *unique*-preference refinement
([[social_choice.fair_division.divisible.stromquist_unique_preference_sets]])
strengthens the cover to one with pairwise-disjoint witnesses, giving the
final EF assignment.

## References

- Stromquist, W. (1980). "How to Cut a Cake Fairly". *Amer. Math. Monthly* 87: 640–644.
- Su, F. E. (1999). "Rental Harmony: Sperner's Lemma in Fair Division". *Amer. Math. Monthly* 106.
