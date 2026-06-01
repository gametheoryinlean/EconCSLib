# Staged Simplex Topic Catalog

Canonical folder topic: `math.simplex`

## Scope

`math.simplex` collects neutral utilities over the standard simplex
`stdSimplex 𝕜 I`, the shared substrate underneath mixed strategies, lotteries,
and expected utility. Lemmas here speak only about weighted sums and point
masses; game-theoretic interpretation (mixed Nash equilibrium, expected
payoff, expected utility) is added in the consuming topics.

## Nodes

- `math.simplex.wsum` - the `wsum` weighted-sum operator and its core algebra
  (constant, monotone, non-negative, additive, scalar).
- `math.simplex.wsum_comm` - exchange order of iterated weighted sums.
- `math.simplex.pure` - point-mass simplex elements `stdSimplex.pure i₀`
  and the evaluation lemma `wsum_pure_apply`.
- `math.simplex.bounded_by_value` - bridge between pointwise bounds on a
  payoff and bounds on all simplex weighted sums.
- `math.simplex.continuity` - coordinate and weighted-sum continuity on the
  real simplex.

## Boundary

Game-theoretic constructions built on these utilities (mixed strategy
profiles, expected payoff, mixed Nash equilibrium, expected utility,
compound lottery) live in `strategic_games` and `utility` respectively.
