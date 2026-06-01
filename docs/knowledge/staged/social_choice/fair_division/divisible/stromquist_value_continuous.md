---
id: social_choice.fair_division.divisible.stromquist_value_continuous
title: Piece-Value Function Is Continuous on the Division Simplex
kind: lemma
status: staged
primary_topic: social_choice
topics:
  - social_choice
  - social_choice.fair_division
  - social_choice.fair_division.divisible
  - social_choice.fair_division.divisible.stromquist
uses:
  - social_choice.fair_division.divisible.stromquist_pieces
  - social_choice.fair_division.divisible.cdf_continuous
lean:
  modules:
    - EconCSLib.SocialChoice.FairDivision.Divisible.Existence
  declarations:
    - SocialChoice.FairDivision.Divisible.strom_value
    - SocialChoice.FairDivision.Divisible.strom_value_continuous
verification:
  statement: accepted
  proof: accepted
  alignment: aligned
tags:
  - fair-division
  - divisible
  - stromquist
  - continuity
---

# Piece-Value Function Is Continuous on the Division Simplex

For each agent $j$ and piece index $i$, the *piece-value function*
assigns to a simplex point $x$ the value agent $j$ places on the $i$-th
piece at division $x$:
$$
v(x, j, i) \;=\; \mu_j\bigl(\mathrm{piece}(x, i)\bigr).
$$

In Lean: `strom_value`.

**Lemma.** For each fixed $(j, i)$, $x \mapsto v(x, j, i)$ is continuous
on $\mathrm{Fin}\ n \to \mathbb{R}$.

In Lean: `strom_value_continuous`.

## Proof sketch

The $i$-th piece is a half-open interval whose endpoints are continuous
linear functions of $x$ (the partial sums $\sum_{j < i} x_j$ and
$\sum_{j \le i} x_j$). Composing with the homeomorphism $\varphi$ yields
half-open intervals in $\mathbb{R}$ whose endpoints depend continuously
on $x$.

The CDF $t \mapsto \mu_j((-\infty, t])$ for the finite non-atomic measure
$\mu_j$ (pushed to $\mathbb{R}$ if needed) is continuous
([[social_choice.fair_division.divisible.cdf_continuous]]). The value of
$\mu_j$ on a half-open interval is the difference of two CDF values at
the endpoints, hence continuous in $x$.

## Where this is used

Continuity of $v$ is what makes the *preference sets*
([[social_choice.fair_division.divisible.stromquist_preference_sets]])
closed and the *unique-preference sets*
([[social_choice.fair_division.divisible.stromquist_unique_preference_sets]])
open — the two topological inputs to the KKM lemma in Stromquist's
proof. Non-atomicity of $\mu_j$ enters here through `cdfRealContinuous`.

## References

- Stromquist, W. (1980). "How to Cut a Cake Fairly". *Amer. Math. Monthly* 87: 640–644.
