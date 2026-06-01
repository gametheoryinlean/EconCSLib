---
id: social_choice.fair_division.divisible.measure_valuation
title: Measure Valuation
kind: definition
status: formalized
primary_topic: social_choice
topics:
  - social_choice
  - social_choice.fair_division
  - social_choice.fair_division.divisible
uses:
  - social_choice.fair_division.divisible.cake_valuation
lean:
  modules:
    - EconCSLib.SocialChoice.FairDivision.Divisible.Valuation
  declarations:
    - SocialChoice.FairDivision.Divisible.MeasureValuation
    - SocialChoice.FairDivision.Divisible.MeasureValuation.val_empty
    - SocialChoice.FairDivision.Divisible.MeasureValuation.val_union
    - SocialChoice.FairDivision.Divisible.MeasureValuation.val_iUnion
verification:
  definition: accepted
  proof: accepted
  alignment: aligned
tags:
  - fair-division
  - divisible
  - cake-cutting
  - measure
  - valuation
---

# Measure Valuation

The canonical example of a cake valuation
([[social_choice.fair_division.divisible.cake_valuation]]): each agent's
value for a piece $S \subseteq \Omega$ is given by their personal measure:
$$
\mathrm{val}(i, S) = \mu_i(S).
$$

In Lean: `MeasureValuation μ` constructs a `CakeValuation N Ω ENNReal`
from a family $\mu : N \to \mathrm{Measure}\ \Omega$ on a measurable
cake $\Omega$.

## Basic properties

- **Empty piece is null.** `val_empty` :
  $(\mathrm{MeasureValuation}\ \mu).val\ i\ \emptyset = 0$.

- **Finite additivity.** For disjoint $S, T$ with $T$ measurable,
  $$
  \mathrm{val}(i, S \cup T) = \mathrm{val}(i, S) + \mathrm{val}(i, T).
  $$
  (`val_union`, via `MeasureTheory.measure_union`.)

- **Countable additivity.** For a countable index $N$ and a pairwise
  disjoint measurable family $A : N \to \mathrm{Set}\ \Omega$,
  $$
  \mathrm{val}\bigl(i, \bigcup_{j} A(j)\bigr) = \sum_{j} \mathrm{val}(i, A(j)).
  $$
  (`val_iUnion`, via `MeasureTheory.measure_iUnion`.)

These are exactly the measure-theoretic axioms wrapped at the
`CakeValuation` API level so that downstream proofs (EF-implies-PROP,
Dubins–Spanier, Stromquist) can chain through value-side identities
without dropping into `Measure` lemmas every time.

## References

- [AGT Chapter 13] Nisan, Roughgarden, Tardos, and Vazirani, *Algorithmic Game Theory*. Measure-based cake valuations.
