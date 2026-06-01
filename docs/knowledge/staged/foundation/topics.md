# Staged Foundation Topic Catalog

Canonical folder topic: `foundation`

## Scope

`foundation` covers the shared vocabulary used across all subfields of
EconCSLib: ordinal preferences, the standalone profile/deviation shim, and
noncomputable argmax for total preorders. These nodes capture the atomic
Lean-anchored declarations; downstream topics (`utility`, `strategic_games`,
`social_choice`, `extensive_game`, ...) build domain narratives on top of them.
The standard-simplex utilities are mathematical infrastructure and live under
`math.simplex`, not here.

## Subtopics

- `foundation.preference` - ordinal-preference vocabulary: indifference, strict
  preference, total preorder, utility representation, and the abstract
  relation-style axioms used by social choice.
- `foundation.argmax` - noncomputable `List.argMaxOn` under a `TotalPreorder`,
  used by backward induction on finite game trees.
- `foundation.profile` - long-term compatibility layer for the standalone
  `Profile N S` / `deviate` vocabulary; canonical strategic-game version is
  `G.Profile` in `StrategicGame.Basic`.

## Boundary

- The bundled `Pref A` interface lives in the foundation because it is shared
  by social choice, fair division, and matching. Domain-specific restrictions
  live in their owning topics.
- `Foundation.OrderedGroup` provides payoff/price arithmetic idioms; it is not
  surfaced as blueprint nodes because the lemmas are micro-arithmetic. Cite
  the Mathlib lemmas it documents directly when needed.
