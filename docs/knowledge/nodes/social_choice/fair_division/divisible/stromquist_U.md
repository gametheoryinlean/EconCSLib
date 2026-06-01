---
id: social_choice.fair_division.divisible.stromquist_U
title: Stromquist Agent-Preference Union U(i)
kind: definition
status: formalized
primary_topic: social_choice
topics:
  - social_choice
  - social_choice.fair_division
  - social_choice.fair_division.divisible
  - social_choice.fair_division.divisible.stromquist
uses:
  - social_choice.fair_division.divisible.stromquist_unique_preference_sets
lean:
  modules:
    - EconCSLib.SocialChoice.FairDivision.Divisible.Existence
  declarations:
    - SocialChoice.FairDivision.Divisible.strom_U
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

# Stromquist Agent-Preference Union U(i)

For each piece index $i$, the *agent-preference union* aggregates the
divisions where *some* agent uniquely prefers piece $i$:
$$
U(i) \;=\; \bigcup_{j \in \mathrm{Fin}\ n} B(i, j),
$$
with $B(i, j)$ as in
[[social_choice.fair_division.divisible.stromquist_unique_preference_sets]].

In Lean: `strom_U i`.

## Properties

- **Openness.** $U(i)$ is open as a finite union of open sets.
- **Avoids the empty-piece face.** $U(i) \cap \mathrm{simplexFaceOpp}(i) = \emptyset$:
  on the face $\{x \in S \mid x_i = 0\}$ the piece $i$ is empty
  ([[social_choice.fair_division.divisible.stromquist_pieces]]), so no
  agent values it strictly above the others; in particular nobody
  uniquely prefers it, so $U(i)$ does not meet the face.

The combination (openness + avoids face $i$) is the KKM input for the
"usual case" of Stromquist's proof
([[social_choice.fair_division.divisible.stromquist_usual_case]]): the
KKM lemma applied to the family $\{U(i) : i \in \mathrm{Fin}\ n\}$
produces a common point in $\bigcap_i U(i)$, at which every piece has a
unique claimant.

The "unusual case" arises precisely when $\{U(i)\}_i$ does *not* cover
the simplex
([[social_choice.fair_division.divisible.stromquist_unusual_case]]). The
shifted-cell refinement handles this case.

## References

- Stromquist, W. (1980). "How to Cut a Cake Fairly". *Amer. Math. Monthly* 87: 640–644.
- Su, F. E. (1999). "Rental Harmony: Sperner's Lemma in Fair Division". *Amer. Math. Monthly* 106.
