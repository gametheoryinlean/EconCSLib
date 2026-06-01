---
id: social_choice.fair_division.divisible.stromquist_unique_preference_sets
title: Stromquist Unique-Preference Sets B(i, j)
kind: definition
status: formalized
primary_topic: social_choice
topics:
  - social_choice
  - social_choice.fair_division
  - social_choice.fair_division.divisible
  - social_choice.fair_division.divisible.stromquist
uses:
  - social_choice.fair_division.divisible.stromquist_preference_sets
lean:
  modules:
    - EconCSLib.SocialChoice.FairDivision.Divisible.Existence
  declarations:
    - SocialChoice.FairDivision.Divisible.strom_B
    - SocialChoice.FairDivision.Divisible.strom_B_open
    - SocialChoice.FairDivision.Divisible.strom_B_disjoint_over_i
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

# Stromquist Unique-Preference Sets B(i, j)

A strengthening of the preference sets
([[social_choice.fair_division.divisible.stromquist_preference_sets]]):
$B(i, j)$ collects the divisions where piece $i$ is agent $j$'s **unique**
value-maximizer:
$$
B(i, j) \;=\; \{x \in S \mid \forall k \ne i,\ v(x, j, k) < v(x, j, i)\}.
$$

In Lean: `strom_B i j`.

## Openness

`strom_B_open`: $B(i, j)$ is open in $\mathrm{Fin}\ n \to \mathbb{R}$.

*Proof.* The defining condition is a conjunction of $n - 1$ strict
inequalities, each of which cuts out an open half-space because both
sides are continuous
([[social_choice.fair_division.divisible.stromquist_value_continuous]]).
A finite intersection of open sets is open.

## Pairwise disjoint across pieces at a fixed agent

`strom_B_disjoint_over_i`: for fixed $j$, the family
$\{B(i, j) : i \in \mathrm{Fin}\ n\}$ is pairwise disjoint.

*Proof.* If $x \in B(i_1, j) \cap B(i_2, j)$ with $i_1 \ne i_2$, then
agent $j$ has piece $i_1$ as their unique value-maximizer (the $B(i_1, j)$
membership) *and* piece $i_2$ as their unique value-maximizer (the
$B(i_2, j)$ membership). Two distinct pieces cannot both be a unique
maximizer, contradiction.

The intuitive content: each agent uniquely prefers at most one piece at
any given division.

## Role in the proof

The KKM-style argument in Stromquist's proof needs *open* covers (for
compactness) and a way to extract a *bijection* between pieces and
agents (for the EF assignment). The pair
$(\text{open } B(i, j),\ \text{disjoint across } j)$ is exactly this
data:

- *Openness* feeds the KKM lemma.
- *Disjointness* across pieces at a fixed agent makes the assignment
  function $\text{piece} \to \text{agent}$ injective: if two pieces had
  the same claimant agent, that agent would uniquely prefer both, a
  contradiction. Injectivity plus counting then forces the assignment to
  be a bijection.

The aggregated *agent-preference union*
([[social_choice.fair_division.divisible.stromquist_U]]) takes
$U(i) = \bigcup_j B(i, j)$, which inherits openness from each $B(i, j)$.

## References

- Stromquist, W. (1980). "How to Cut a Cake Fairly". *Amer. Math. Monthly* 87: 640–644.
