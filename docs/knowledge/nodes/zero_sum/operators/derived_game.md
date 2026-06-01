---
id: game_theory.strategic_game.zero_sum.operators.derived_game
title: Derived Game
kind: definition
status: admitted
primary_topic: game_theory.zero_sum
topics:
  - game_theory.zero_sum
  - game_theory.zero_sum.operators
uses:
  - game_theory.strategic_game.zero_sum.operators.value_operator_general
  - game_theory.strategic_game.zero_sum.core.optimal_strategy_sets
source:
  spans:
    - artifact: mfogt
      locator: "Section 3.4, after Proposition 3.4.2"
      format: section
      note: "The game (S(f), T(f), g) is called the derived game of f along g"
verification:
  definition: accepted
  proof: not_applicable
tags:
  - zero-sum
  - value-operator
  - derived-game
---

# Derived Game

Let $S(f)$ and $T(f)$ be the optimal strategy sets of the zero-sum game
$(S,T,f)$. The derived game of $f$ along another payoff function $g$ is the
zero-sum game
$$
  (S(f),T(f),g).
$$
It measures the first-order change of the value of $f$ in the direction $g$.

## References

- [MFoGT, Section 3.4, after Prop. 3.4.2] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. The game (S(f), T(f), g) is called the derived game of f along g.
