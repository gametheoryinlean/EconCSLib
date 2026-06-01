---
id: social_choice.fair_division.divisible.stromquist_assignment
title: Fair Assignment from a Common KKM Point
kind: lemma
status: staged
primary_topic: social_choice
topics:
  - social_choice
  - social_choice.fair_division
  - social_choice.fair_division.divisible
  - social_choice.fair_division.divisible.stromquist
uses:
  - social_choice.fair_division.divisible.stromquist_U
  - social_choice.fair_division.divisible.envy_free
lean:
  modules:
    - EconCSLib.SocialChoice.FairDivision.Divisible.Existence
  declarations:
    - SocialChoice.FairDivision.Divisible.strom_fair_assignment
verification:
  statement: accepted
  proof: accepted
  alignment: aligned
tags:
  - fair-division
  - divisible
  - stromquist
  - envy-free
---

# Fair Assignment from a Common KKM Point

**Lemma (informal).** Given a simplex point $x^* \in \bigcap_{i \in \mathrm{Fin}\ n} U(i)$
([[social_choice.fair_division.divisible.stromquist_U]]), there is an
envy-free assignment of pieces to agents.

The construction: at $x^*$, each piece $i$ has at least one claimant
agent $\sigma(i) \in \mathrm{Fin}\ n$ — some $j$ such that $x^* \in B(i, j)$
([[social_choice.fair_division.divisible.stromquist_unique_preference_sets]]).
Pick one (DecidableEq / choice).

The map $\sigma : \mathrm{Fin}\ n \to \mathrm{Fin}\ n$ is *injective*:
if $\sigma(i_1) = \sigma(i_2) = j$ then $x^* \in B(i_1, j) \cap B(i_2, j)$,
which by `strom_B_disjoint_over_i` (disjointness across pieces at a fixed
agent, [[social_choice.fair_division.divisible.stromquist_unique_preference_sets]])
forces $i_1 = i_2$.

An injection on a finite set of the same cardinality is a bijection, so
$\sigma$ is a permutation.

Define the allocation $A : \mathrm{Fin}\ n \to \mathrm{Set}\ \mathbb{R}$ by
$$
A(j) \;=\; \mathrm{piece}(x^*, \sigma^{-1}(j)).
$$

This is a complete measurable partition by
[[social_choice.fair_division.divisible.stromquist_pieces]], and it is
envy-free because $\sigma^{-1}(j)$ is agent $j$'s value-maximizer at $x^*$:
no other piece can be strictly preferred, so by the bundled EF predicate
([[social_choice.fair_division.divisible.envy_free]]) the allocation is EF.

## Role in the proof

This lemma is the *transducer* that converts the KKM common-point
existence into an actual fair allocation. The "usual case"
([[social_choice.fair_division.divisible.stromquist_usual_case]]) is
precisely the regime where this lemma applies; the "unusual case"
([[social_choice.fair_division.divisible.stromquist_unusual_case]])
arises when the $U(i)$ family does not cover $S$, and needs the
shifted-cell trick to push the data into a configuration where this
lemma can be applied.

## References

- Stromquist, W. (1980). "How to Cut a Cake Fairly". *Amer. Math. Monthly* 87: 640–644.
