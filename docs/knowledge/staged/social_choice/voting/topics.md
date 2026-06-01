# Staged Voting Topic Catalog

Canonical folder topic: `social_choice.voting`

## Scope

`social_choice.voting` covers preference-aggregation rules over a fixed
alternative set: social welfare functions (`SWF`), social choice functions
(`SCF`), their standard axioms, and the classical impossibility and
characterization theorems.

The Lean source for this topic lives in `EconCSLib/SocialChoice/Voting/*.lean`.

## Subtopics

- `social_choice.voting.arrow` - decisive-coalition spine and Arrow's
  impossibility theorem.
- `social_choice.voting.gibbard_satterthwaite` - Muller-Satterthwaite and
  Gibbard-Satterthwaite.
- `social_choice.voting.rules` - majority, Condorcet, Borda, plurality, and
  the Condorcet paradox example.

## Expected Nodes (rooted at `social_choice.voting`)

- `social_choice.voting.swf` - social welfare function on a preference profile.
- `social_choice.voting.scf` - social choice function on a preference profile.
- `social_choice.voting.unanimity` - unanimity / Pareto for `SWF` and `SCF`.
- `social_choice.voting.iia` - independence of irrelevant alternatives.
- `social_choice.voting.dictatorial_swf` - dictatorship for `SWF`.
- `social_choice.voting.dictatorial_scf` - dictatorship for `SCF`.
- `social_choice.voting.monotonic_scf` - Maskin monotonicity for `SCF`.
- `social_choice.voting.strategyproof` - strategy-proof / nonmanipulable `SCF`.

## Boundary

Pure preference vocabulary (the bundled `Pref` interface, strict preference,
preference profiles) lives in `social_choice`, not here. Choice problems
with structured outcome spaces (shares of a cake, bundles of indivisible
items, allocations) live in `social_choice.fair_division`, not here.
