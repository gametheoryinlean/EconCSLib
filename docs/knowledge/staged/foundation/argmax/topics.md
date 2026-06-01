# Staged Foundation Argmax Topic Catalog

Canonical folder topic: `foundation.argmax`

## Scope

`foundation.argmax` exposes a single workhorse: a noncomputable `List.argMaxOn`
for a function valued in a `TotalPreorder`. Mathlib's `List.argmax` requires
`[LinearOrder]` (antisymmetry plus decidable order) and therefore cannot be
used when ties between distinct alternatives must be allowed. The backward-
induction proof in `ExtensiveGame.BackwardInduction` consumes this version.

## Nodes

- `foundation.argmax.list_arg_max_on` -- existence, the chosen maximizer
  `List.argMaxOn`, membership, and the maximizing property.

## Boundary

If a downstream proof needs decidable argmax, prefer Mathlib's
`List.argmax` directly. The version here exists only to bridge the
`TotalPreorder` / `LinearOrder` gap.
