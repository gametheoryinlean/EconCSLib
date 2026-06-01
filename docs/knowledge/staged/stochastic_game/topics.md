# Staged Stochastic Game Topic Catalog

Canonical folder topic: `stochastic_game`

## Scope

`stochastic_game` covers games whose stage payoff depends on a state that
evolves stochastically as a function of the players' actions. Two
historically central branches:

- **Zero-sum stochastic games** (Shapley 1953): each stage is a matrix
  game whose value functions assemble into a contraction operator with a
  unique fixed point — the discounted value.
- **General-sum stochastic games** (Fink 1964): Nash equilibrium
  existence carries over to the multi-state setting, with strategy
  spaces that are Markovian in the state.

Stochastic games sit conceptually between repeated games (no state
dynamics, see `repeated_game.*`) and Markov decision processes (one
player, no opponent). They are the canonical 2-player generalisation of
MDPs and the canonical state-augmented generalisation of matrix games.

## Subtopics

- `stochastic_game.core` - state space, transition kernel, history,
  pure / behaviour / Markovian strategy, finite-horizon vs
  infinite-horizon evaluations.
- `stochastic_game.value` - zero-sum branch: discounted value `v_γ`,
  Shapley operator `T`, fixed-point characterisation `v_γ = T(v_γ)`,
  Shapley iteration.
- `stochastic_game.equilibrium` - general-sum branch: Fink 1964 Nash
  equilibrium existence, Markov-perfect equilibrium, refinement and
  computation in the multi-state setting.
- `stochastic_game.asymptotic` - undiscounted / uniform / asymptotic
  value: Bewley-Kohlberg semialgebraic asymptotic value (1976),
  Mertens-Neyman uniform value (1981), discount-rate convergence.
- `stochastic_game.examples` - Big Match (Blackwell-Ferguson 1968),
  Recursive Games (Everett 1957), MDPs as 1-player stochastic games,
  hidden-state benchmark examples.

## Boundary

`stochastic_game` is **not** about repeated games (no state evolution —
that is `repeated_game.*`). Pure zero-sum matrix-game value theory
stays in `zero_sum.*`; abstract value-operator framework (any
contraction on bounded functions) stays in `zero_sum.operators` and is
shared. Approachability of vector-payoff sets is its own topic
(`approachability.*`).
