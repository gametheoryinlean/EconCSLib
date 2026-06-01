# Staged Zero-Sum Topic Catalog

Canonical folder topic: `game_theory.strategic_game.zero_sum`

## Scope

`zero_sum` covers two-player **single-stage** zero-sum game theory: the
matrix-game value, minimax theorems and their proof routes, the
structure of optimal mixed strategies, the special-matrix and
continuous-game variants, fictitious play on a fixed matrix, and
direct applications (Perron-Frobenius, Markov stationary distributions).

State-evolving zero-sum games belong in `stochastic_game.*`, and the
Aumann-Maschler incomplete-information repeated zero-sum branch lives in
`repeated_game.incomplete_info`.

## Subtopics

- `game_theory.strategic_game.zero_sum.core` - zero-sum games, matrix games, values, guarantees,
  saddle points, and supports.
- `game_theory.strategic_game.zero_sum.minimax` - umbrella for minimax theorem statements and proof
  routes. Now split into two siblings for navigation:
  - `game_theory.strategic_game.zero_sum.minimax.structure` - main theorem statements
    (von_neumann_minimax, ordered_field_minimax, loomis_theorem,
    ville_theorem) and structural results about optimal play (saddle
    points, value uniqueness, strong complementarity, common-guarantee
    value, antisymmetric value formula).
  - `game_theory.strategic_game.zero_sum.minimax.proofs` - proof routes and supporting lemmas
    (Loomis induction sub-tree, LP duality, antisymmetric reduction,
    Ville discretization, approachability route, Kakutani fixed-point).
- `game_theory.strategic_game.zero_sum.continuous` - compact/convex minimax, Sion variants, mixed
  strategy pathologies, and boundary counterexamples.
- `game_theory.strategic_game.zero_sum.fictitious_play` - fictitious play, empirical frequencies,
  Robinson proof, and convergence targets.
- `game_theory.strategic_game.zero_sum.operators` - **abstract** value operators on bounded
  functions: nonexpansiveness, directional derivatives, monotone limits.
  The Shapley operator specialization lives under
  `stochastic_game.value`.
- `game_theory.strategic_game.zero_sum.examples` - matching pennies, duels, diagonal games,
  two-by-two formulae, and failure examples.
- `game_theory.strategic_game.zero_sum.lp` - LP formulation of zero-sum games, primal-dual
  correspondence, complementarity and strong-complementarity bridges.
- `game_theory.strategic_game.zero_sum.applications` - Perron-Frobenius for positive matrices,
  Markov stationary distributions, and other classical applications of
  the minimax / LP-duality apparatus.

## Boundary

Use `zero_sum`, not `zerosum`, for new ids and references.
Stochastic games — `stochastic_game.*`; repeated games — `repeated_game.*`;
approachability — `approachability.*`; no-regret / Hannan-set learning —
`strategic_games.learning`.
