---
id: social_choice.fair_division.indivisible.valuation
title: Indivisible Valuation
kind: definition
status: formalized
primary_topic: social_choice
topics:
  - social_choice
  - social_choice.fair_division
  - social_choice.fair_division.indivisible
uses: []
lean:
  modules:
    - EconCSLib.SocialChoice.FairDivision.Indivisible.Valuation
  declarations:
    - SocialChoice.FairDivision.Indivisible.Valuation
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
tags:
  - fair-division
  - indivisible
  - valuation
---

# Indivisible Valuation

An *indivisible valuation* assigns a real value to each
agent-bundle pair:
$$
\mathrm{val} : N \to \mathrm{Finset}\ G \to \mathbb{R}.
$$

In Lean: structure `SocialChoice.FairDivision.Indivisible.Valuation N G`
with one field `val`.

## Design

Three deliberate choices in the abstract valuation:

- *Real-valued.* Keeps the public API aligned with the bundled cardinal
  fair-division interface
  ([[social_choice.fair_division.cardinal_instance]]) and avoids
  carrying ordered-algebra typeclasses through every theorem statement.

- *No monotonicity or normalization baked in.* Monotonicity (bundles
  grow ⇒ value weakly grows) appears only where it's actually needed,
  e.g. as an explicit hypothesis in
  [[social_choice.fair_division.indivisible.efx]]'s implication
  `EF ⇒ EFX for monotone valuations`. Additive valuations
  ([[social_choice.fair_division.indivisible.additive_valuation]])
  give monotonicity for free under the nonnegativity-of-weights
  assumption.

- *No coupling to ring-theoretic `Valuation`.* The structure lives in
  namespace `SocialChoice.FairDivision.Indivisible` so it never clashes
  with `Mathlib.RingTheory.Valuation.Basic` (ring → ordered monoid),
  nor with the *coalitional game* characteristic function (`v : Set N
  → ℝ`, valuing coalitions of *agents*).

## References

- [AGT Chapter 11] Nisan, Roughgarden, Tardos, and Vazirani, *Algorithmic Game Theory*. Valuations on bundles of indivisible goods.
