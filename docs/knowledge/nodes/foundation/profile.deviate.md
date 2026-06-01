---
id: foundation.profile.deviate
title: Standalone Profile and Unilateral Deviation
kind: definition
status: formalized
primary_topic: foundation
topics:
  - foundation
  - foundation.profile
uses: []
lean:
  modules:
    - EconCSLib.Foundation.Profile
  declarations:
    - Profile
    - deviate
    - Profile.deviate_self
    - Profile.deviate_same
    - Profile.deviate_of_ne
verification:
  definition: accepted
  proof: accepted
  alignment: aligned
tags:
  - core
  - profile
  - deviation
---

# Standalone Profile and Unilateral Deviation

For an arbitrary index type `N` and family of strategy types `S : N → Type*`,
a *strategy profile* is a dependent function
$$
  \sigma : \prod_{i : \iota} S(i).
$$

A *unilateral deviation* by player $i$ to $s' \in S(i)$ is the profile that
agrees with $\sigma$ off $i$ and equals $s'$ at $i$. This is exactly
`Function.update`, exposed under the game-theoretic alias
`deviate σ i s'` and the dedicated notation $\sigma[i \mapsto s']$.

The three governing simp lemmas:

- `deviate_self` -- deviating to the current value is the identity:
  $\sigma[i \mapsto \sigma_i] = \sigma$.
- `deviate_same` -- at the deviated index, the new profile returns the new
  value: $\sigma[i \mapsto s']_i = s'$.
- `deviate_of_ne` -- at any other index, the new profile is unchanged:
  $\sigma[i \mapsto s']_j = \sigma_j$ when $j \ne i$.

## Status: long-term compatibility layer

This node is the **standalone** profile vocabulary. The canonical
strategic-game version, `G.Profile` together with `StrategicGame.deviate`
in `StrategicGame.Basic`, is the preferred interface for game-bound code.
The standalone version is preserved indefinitely for two reasons:

1. lemmas about profiles can be stated without committing to a specific
   `StrategicGame` instance (the proofs reduce to `Function.update` facts);
2. legacy student-project code and non-strategic-game profile uses
   (extensive games, social-choice ballots) continue to depend on it.

## References

- [MSZ, Chapter 4] Maschler, Solan, and Zamir, *Game Theory*. Strategy profiles and unilateral deviations.
