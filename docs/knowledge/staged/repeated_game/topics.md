# Staged Repeated Game Topic Catalog

Canonical folder topic: `repeated_game`

## Scope

`repeated_game` covers games in which a fixed *stage game* is played
repeatedly over time, with payoffs aggregated across stages. The state
of the world does not evolve (that distinguishes repeated games from
stochastic games — see `stochastic_game.*`); only the play history and
common knowledge about it evolve.

Three historically central branches:

- **Payoff aggregation** — T-stage average, discounted, undiscounted /
  uniform / asymptotic. Each evaluation rule gives a different value
  concept.
- **Folk theorems** — characterisation of equilibrium payoffs in
  long-run interaction. Folk theorems (Aumann-Shapley, Friedman,
  Fudenberg-Maskin) say roughly "any individually rational feasible
  payoff is a subgame-perfect equilibrium payoff".
- **Repeated games with incomplete information** — Aumann-Maschler
  framework (1995 collected work, original from 1968): players have
  private information about a state drawn once at the start, and the
  cav-u theorem characterises the uniform value in the zero-sum case.

## Subtopics

- `repeated_game.core` - stage game, history, behavioural / pure
  strategy, T-stage / discounted / undiscounted evaluations,
  individually rational and feasible payoff sets.
- `repeated_game.folk_theorem` - Nash and subgame-perfect folk theorems
  for discounted and undiscounted repeated games.
- `repeated_game.incomplete_info` - Aumann-Maschler repeated games with
  incomplete information; cav-u theorem (zero-sum); revelation /
  splitting strategies.

## Boundary

`repeated_game` excludes games where the stage game itself changes with
the state — those are `stochastic_game.*`. Zero-sum-specific
single-stage tools (minimax, fictitious play on a fixed matrix) belong
in `zero_sum.*`. Folk-theorem-style results for repeated zero-sum games
are trivial (the value is the same in every stage), so this topic's
zero-sum content concentrates in `repeated_game.incomplete_info`.
