---
id: social_choice.fair_division.divisible.measure_instance_existence
title: Measure-Instance Existence Wrappers
kind: theorem
status: staged
primary_topic: social_choice
topics:
  - social_choice
  - social_choice.fair_division
  - social_choice.fair_division.divisible
uses:
  - social_choice.fair_division.divisible.measure_instance
  - social_choice.fair_division.divisible.proportional_exists
  - social_choice.fair_division.divisible.ef_exists_and_proportional
lean:
  modules:
    - EconCSLib.SocialChoice.FairDivision.Divisible.Existence
  declarations:
    - SocialChoice.FairDivision.Divisible.MeasureInstance.proportional_exists
    - SocialChoice.FairDivision.Divisible.MeasureInstance.envyFree_exists
    - SocialChoice.FairDivision.Divisible.MeasureInstance.envyFree_and_proportional_exists
verification:
  statement: accepted
  proof: accepted
  alignment: aligned
tags:
  - fair-division
  - divisible
  - measure
  - envy-free
  - proportional
  - existence
---

# Measure-Instance Existence Wrappers

The bundled-instance forms of the three main existence results on
$I = [0, 1]$, all stated against a divisible measure instance
$\mathrm{MeasureInstance}\ (\mathrm{Fin}\ n)\ I$
([[social_choice.fair_division.divisible.measure_instance]]).

| Theorem | Underlying result |
|---|---|
| `MeasureInstance.proportional_exists` | [[social_choice.fair_division.divisible.proportional_exists]] |
| `MeasureInstance.envyFree_exists` | [[social_choice.fair_division.divisible.ef_exists]] |
| `MeasureInstance.envyFree_and_proportional_exists` | [[social_choice.fair_division.divisible.ef_exists_and_proportional]] |

Each wrapper takes a `MeasureInstance` whose underlying measure family
$I.\mathrm{measure}$ is finite and non-atomic, and produces the
corresponding feasible allocation satisfying the named property under
$I.\mathrm{IsProportional}$ / $I.\mathrm{IsEnvyFree}$.

## Why three wrappers

Splitting the existence statements at the bundled-instance level lets
downstream consumers refer to the property they need without dragging
in the entire Stromquist machinery:

- `proportional_exists` is the cheapest (Dubins–Spanier route, fully
  constructive).
- `envyFree_exists` invokes Stromquist's KKM / shifted-cell argument.
- `envyFree_and_proportional_exists` packages both for the common
  textbook statement "fair division exists for cake-cutting".

Each wrapper is a thin definitional bridge from the underlying raw
existence theorem; the substantive content lives in the unwrapped
versions.

## References

- Dubins, L. E. and Spanier, E. H. (1961). "How to Cut a Cake Fairly". *Amer. Math. Monthly* 68: 1–17.
- Stromquist, W. (1980). "How to Cut a Cake Fairly". *Amer. Math. Monthly* 87: 640–644.
- [AGT Chapter 13] Nisan, Roughgarden, Tardos, and Vazirani, *Algorithmic Game Theory*.
