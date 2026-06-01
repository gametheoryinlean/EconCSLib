# Staged Foundation Preference Topic Catalog

Canonical folder topic: `foundation.preference`

## Scope

`foundation.preference` is the vocabulary layer for ordinal preferences shared
across utility theory, social choice, matching, and game theory. The nodes
here are the atomic Lean-anchored definitions and basic lemmas; domain
narratives (e.g. MSZ Ch.2 preferences in `utility/preference_relation.md`)
cross-link to these nodes via `uses`.

## Nodes

- `foundation.preference.indifferent` - the `Indifferent` relation `a ≤ b ∧ b ≤ a`
  on a `Preorder`, plus reflexivity/symmetry/transitivity.
- `foundation.preference.strictly_preferred` - the `StrictlyPreferred` alias for
  `<`, plus asymmetry/transitivity/irreflexivity.
- `foundation.preference.total_preorder` - `class TotalPreorder` (preorder with
  totality but no antisymmetry), comparability, and the
  `LinearOrder → TotalPreorder` instance.
- `foundation.preference.represents_preference` - `RepresentsPreference u` together
  with `lt_iff` and `indifferent_iff`.
- `foundation.preference.abstract_relation` - the relation-style vocabulary
  `strict / indiff / VNM.Completeness / VNM.Transitivity` used to state axioms
  over arbitrary `α → α → Prop` relations.

## Boundary

The bundled `Pref A` interface is part of the shared foundation because
social choice, fair division, and matching all use it. Domain-specific
restrictions belong to their owning topics.
