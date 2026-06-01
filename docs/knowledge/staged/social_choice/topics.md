# Staged Social Choice Topic Catalog

Canonical folder topic: `social_choice`

## Scope

`social_choice` covers the abstract aggregation of individual preferences into
collective decisions, together with structured choice problems that share that
vocabulary. The Lean library reflects this with one preference and instance
layer in `EconCSLib/SocialChoice/Basic.lean`, then voting and fair-division
specializations on top.

## Subtopics

- `social_choice` - bundled preference relations, preference profiles,
  generic instances, solution concepts, and choice rules / correspondences.
- `social_choice.voting` - social welfare functions, social choice functions,
  axioms (unanimity, IIA, monotonicity, strategy-proofness), decisive
  coalitions, Arrow's theorem, Gibbard-Satterthwaite, and concrete rules
  (majority, Condorcet, Borda, plurality).
- `social_choice.voting.arrow` - decisive-coalition argument for Arrow's
  impossibility theorem.
- `social_choice.voting.gibbard_satterthwaite` - Muller-Satterthwaite chain
  and Gibbard-Satterthwaite theorem on strategy-proof social choice.
- `social_choice.voting.rules` - majority, Condorcet, Borda, plurality, and
  the Condorcet paradox example.
- `social_choice.fair_division` - allocations of shares (divisible or
  indivisible) under each agent's own preference, EF / PROP / EQ / PO and
  welfare objectives, cake cutting (Cut-and-Choose, Dubins-Spanier,
  Stromquist), indivisible-items algorithms (round-robin, envy-cycle), and
  maximin share.

## Boundary

`social_choice` covers ordinal aggregation and structured allocation problems.
Do not put Bayesian mechanism design, transfer-based mechanisms, VCG, Myerson
payment formulae, or auction formats here - those belong under
`mechanism_design.*` and `auction.*`. Coalitional value and bargaining belong
under their own coalitional-game topics rather than `social_choice`.
