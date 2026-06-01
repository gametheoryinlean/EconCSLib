# Staged Foundation Profile Topic Catalog

Canonical folder topic: `foundation.profile`

## Scope

`foundation.profile` covers the long-term compatibility layer for the standalone
`Profile N S = ∀ i : N, S i` vocabulary and the unilateral-deviation alias
`deviate σ i s'`. The canonical strategic-game version of these constructs
is `G.Profile` together with `G.deviate` in `StrategicGame.Basic`; the
foundation-layer version is preserved indefinitely for code that is not bound
to a specific `StrategicGame`.

## Nodes

- `foundation.profile.deviate` -- the standalone `Profile`, `deviate` notation
  `σ[i ↦ s']`, and the three simp lemmas governing it.

## Boundary

New strategic-game code should prefer `G.Profile` and `G.deviate`. The
foundation profile abstraction is retained so that:

- general lemmas about strategy profiles can be stated without a game in
  scope (e.g. abstract `Function.update` properties);
- legacy student-project code and non-game profile uses continue to compile.
