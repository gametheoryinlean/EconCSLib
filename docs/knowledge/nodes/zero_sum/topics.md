# Accepted Zero-Sum Topic Catalog

Canonical folder topic: `zero_sum`

## Subtopics

- `zero_sum.core` - zero-sum games, value, payoff negation, mixed
  extension, supports, and matrix-game primitives.
- `zero_sum.minimax` - umbrella for minimax theorems; split into
  `.structure` (theorem statements + structural results about optimal
  play) and `.proofs` (proof routes: Loomis induction subtree,
  LP duality, Ville, antisymmetric reduction,
  approachability, Kakutani).
- `zero_sum.applications` - applications of the minimax / LP-duality
  apparatus to classical results (Perron-Frobenius positive matrix,
  Markov stationary distributions).

## Boundary

Use `zero_sum`, not `zerosum`, for new ids and references.
State-evolving zero-sum games belong in `stochastic_game.*` (Shapley
operator, Big Match, Bewley-Kohlberg, Mertens-Neyman); incomplete-
information repeated zero-sum belongs in `repeated_game.incomplete_info`
(Aumann-Maschler cav-u).
