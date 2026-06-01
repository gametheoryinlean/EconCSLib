---
id: social_choice.fair_division.divisible.proportional_exists
title: Proportional Existence on [0,1] (n Agents)
kind: theorem
status: staged
primary_topic: social_choice
topics:
  - social_choice
  - social_choice.fair_division
  - social_choice.fair_division.divisible
uses:
  - social_choice.fair_division.divisible.dubins_spanier_proportional
lean:
  modules:
    - EconCSLib.SocialChoice.FairDivision.Divisible.Existence
  declarations:
    - SocialChoice.FairDivision.Divisible.proportional_exists
verification:
  statement: accepted
  proof: accepted
  alignment: aligned
tags:
  - fair-division
  - divisible
  - proportional
  - existence
---

# Proportional Existence on [0,1] (n Agents)

**Theorem.** For every $n \ge 1$ and every family of finite non-atomic
measures $\mu : \mathrm{Fin}\ n \to \mathrm{Measure}\ I$ on the unit
interval $I = [0, 1]$, there exists a complete measurable partition
$A$ that is proportional in the measure sense:
$$
\forall i \in \mathrm{Fin}\ n,\ \mu_i(I) \;\le\; n \cdot \mu_i(A(i)).
$$

In Lean: `SocialChoice.FairDivision.Divisible.proportional_exists`,
declared at the top of `Existence.lean` so the file's main objective
(EF existence) does not pull in Dubins–Spanier directly.

## Proof

A direct delegation to the Dubins–Spanier moving-knife construction
([[social_choice.fair_division.divisible.dubins_spanier_proportional]]).

## Where this sits

In the Stromquist program ([[social_choice.fair_division.divisible.ef_exists]]),
proportionality is the *easier* sister result. EF existence sits a layer
above it and uses a fundamentally different (KKM / shifted-cell)
argument. The two are combined in
[[social_choice.fair_division.divisible.ef_exists_and_proportional]],
which observes that the EF allocation produced by Stromquist is in
particular proportional (via `IsEnvyFree.isProportional` on measure
valuations, [[social_choice.fair_division.divisible.ef_implies_proportional]]).

## References

- Dubins, L. E. and Spanier, E. H. (1961). "How to Cut a Cake Fairly". *Amer. Math. Monthly* 68: 1–17.
- Stromquist, W. (1980). "How to Cut a Cake Fairly". *Amer. Math. Monthly* 87: 640–644.
