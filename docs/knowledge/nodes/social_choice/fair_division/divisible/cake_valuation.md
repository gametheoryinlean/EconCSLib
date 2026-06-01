---
id: social_choice.fair_division.divisible.cake_valuation
title: Cake Valuation
kind: definition
status: formalized
primary_topic: social_choice
topics:
  - social_choice
  - social_choice.fair_division
  - social_choice.fair_division.divisible
uses: []
lean:
  modules:
    - EconCSLib.SocialChoice.FairDivision.Divisible.Valuation
  declarations:
    - SocialChoice.FairDivision.Divisible.CakeValuation
    - SocialChoice.FairDivision.Divisible.IsNormalized
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
tags:
  - fair-division
  - divisible
  - cake-cutting
  - valuation
---

# Cake Valuation

A *cake valuation* assigns a value in some ordered value type $V$ to each
agent–piece pair $(i, S)$ with $S \subseteq \Omega$:
$$
\mathrm{val} : N \to \mathrm{Set}\ \Omega \to V.
$$

In Lean: structure `SocialChoice.FairDivision.Divisible.CakeValuation N Ω V`
carrying a single field `val`.

The value type $V$ stays polymorphic because the canonical instance —
measure-based valuations
([[social_choice.fair_division.divisible.measure_valuation]]) — takes values
in `ENNReal`, while real-valued bundled interfaces use $\mathbb{R}$.

## Normalization

A cake valuation is *normalized* if every agent values the whole cake at
$1$:
$$
\forall i \in N,\ \mathrm{val}(i, \Omega) = 1.
$$

In Lean: `IsNormalized`, requiring `[One V]`.

For a measure-valuation $\mu_i$, normalization is equivalent to each
$\mu_i$ being a probability measure
([[social_choice.fair_division.divisible.normalized_iff_probability]]).

Normalized cake valuations are the standard setting for comparing
proportionality bounds, MMS values, and welfare aggregates across
agents.

## References

- [AGT Chapter 13] Nisan, Roughgarden, Tardos, and Vazirani, *Algorithmic Game Theory*. Valuations on cake pieces.
- Robertson, J. M. and Webb, W. A. (1998). *Cake-Cutting Algorithms*.
