---
id: social_choice.fair_division.indivisible.checker
title: Decidable Fairness Checkers
kind: theorem
status: staged
primary_topic: social_choice
topics:
  - social_choice
  - social_choice.fair_division
  - social_choice.fair_division.indivisible
uses:
  - social_choice.fair_division.indivisible.ef1
  - social_choice.fair_division.indivisible.efx
  - social_choice.fair_division.indivisible.proportional
lean:
  modules:
    - EconCSLib.SocialChoice.FairDivision.Indivisible.Checker
  declarations:
    - SocialChoice.FairDivision.Indivisible.isEnvyFree_iff
    - SocialChoice.FairDivision.Indivisible.isEF1_iff
    - SocialChoice.FairDivision.Indivisible.isEFX_iff
    - SocialChoice.FairDivision.Indivisible.isProportional_iff
verification:
  statement: accepted
  proof: accepted
  alignment: aligned
tags:
  - fair-division
  - indivisible
  - checker
  - decidable
---

# Decidable Fairness Checkers

For finite agent types and decidable equality on goods, each of the
indivisible fairness predicates has a decidable `Bool` checker
together with a soundness `iff`-theorem matching the corresponding
abstract predicate.

In Lean:

| Checker | Iff-theorem | Predicate |
|---|---|---|
| `isEnvyFree v A` | `isEnvyFree_iff` | [[social_choice.fair_division.indivisible.envy_free]] |
| `isEF1 v A` | `isEF1_iff` | [[social_choice.fair_division.indivisible.ef1]] |
| `isEFX v A` | `isEFX_iff` | [[social_choice.fair_division.indivisible.efx]] |
| `isProportional n v allGoods A` | `isProportional_iff` | [[social_choice.fair_division.indivisible.proportional]] |

The class hypotheses (per checker) are some subset of
`[Fintype N]`, `[DecidableEq N]`, `[DecidableEq G]`.

## Pattern: two-layer design

This follows the EconCSLib "two-layer" pattern (CLAUDE.md §Key Design
Principles): for every `Prop`-valued predicate `IsX`, provide a
decidable `Bool` checker `isX` with a soundness theorem
`isX_iff : isX = true ↔ IsX`. The checker lets `native_decide` /
`decide` verify concrete instances at compile time; the soundness
theorem ports any decidable computation result back to the abstract
predicate API.

For example, given a concrete additive instance on `Fin 3 → Fin 4 →
ℝ`, one can write
```lean
#eval isEF1 v A   -- evaluates the checker
-- or
example : IsEF1 v A := by
  rw [← isEF1_iff]; native_decide
```

## Why these four checkers

These are the predicates whose definition is *quantifier-bounded* (i.e.
finite-conjunction / finite-disjunction over `N` and `G`) and hence
decidably checkable when both types are finite. MMS / α-MMS are
omitted from this layer because their definition quantifies over all
*complete partitions* of `allGoods`, which is a large but finite set;
in principle a decidable checker is constructible but more expensive
than the basic EF / EF1 / EFX / PROP family.

## References

- [AGT Chapter 11] Nisan, Roughgarden, Tardos, and Vazirani, *Algorithmic Game Theory*. Algorithmic checking of fairness.
