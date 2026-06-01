---
id: social_choice.fair_division.divisible.dubins_spanier_proportional
title: Dubins–Spanier Proportional Existence
kind: theorem
status: staged
primary_topic: social_choice
topics:
  - social_choice
  - social_choice.fair_division
  - social_choice.fair_division.divisible
  - social_choice.fair_division.divisible.dubins_spanier
uses:
  - social_choice.fair_division.divisible.ds_step
lean:
  modules:
    - EconCSLib.SocialChoice.FairDivision.Divisible.DubinsSpanier
  declarations:
    - SocialChoice.FairDivision.Divisible.dubinsSpanierProportional
verification:
  statement: accepted
  proof: accepted
  alignment: aligned
tags:
  - fair-division
  - divisible
  - dubins-spanier
  - proportional
  - existence
---

# Dubins–Spanier Proportional Existence

**Theorem.** For every $n \ge 1$ and every family of finite measures
$\mu : \mathrm{Fin}\ n \to \mathrm{Measure}\ I$ on the unit interval $I =
[0, 1]$ with each $\mu_i$ non-atomic, there exists a complete measurable
partition $A : \mathrm{Allocation}\ (\mathrm{Fin}\ n)\ I$ that is
proportional in the measure sense:
$$
\forall i \in \mathrm{Fin}\ n,\ \mu_i(I) \;\le\; n \cdot \mu_i(A(i)).
$$

In Lean: `SocialChoice.FairDivision.Divisible.dubinsSpanierProportional`.

## Proof

By the moving-knife induction ([[social_choice.fair_division.divisible.ds_step]]),
using the IVT-on-measures cut lemma
([[social_choice.fair_division.divisible.cut_exists]]) at each level.

## Significance

Two parts:

1. **Existence with explicit algorithm.** Unlike Stromquist's EF existence
   ([[social_choice.fair_division.divisible.ef_exists]]) — which uses a
   KKM compactness argument — Dubins–Spanier's proportional existence is
   *constructive*: the algorithm can be unfolded to produce the
   allocation step by step.

2. **PROP, not EF.** The output is proportional but in general *not*
   envy-free. EF is a strictly stronger notion for $n \ge 3$ agents and
   requires the deeper Stromquist construction.

The bundled-instance wrapper is
[[social_choice.fair_division.divisible.dubins_spanier_rule]].

## References

- Dubins, L. E. and Spanier, E. H. (1961). "How to Cut a Cake Fairly". *Amer. Math. Monthly* 68: 1–17.
- [AGT Chapter 13] Nisan, Roughgarden, Tardos, and Vazirani, *Algorithmic Game Theory*. Dubins–Spanier moving knife.
