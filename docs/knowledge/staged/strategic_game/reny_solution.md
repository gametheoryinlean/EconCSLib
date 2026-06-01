---
id: game_theory.strategic_game.refinements.reny_solution
primary_topic: game_theory.strategic_game
topics:
  - game_theory.strategic_game
  - game_theory.strategic_game.refinements
title: Reny Solution
kind: definition
status: staged
uses:
  - game_theory.strategic_game.strategic_game
verification:
  definition: accepted
  proof: not_applicable
tags:
  - strategic-game
  - discontinuous-game
---

# Reny Solution

For a compact game $G$, let
$$
  \Gamma=\{(s,v)\in S\times\mathbb R^I:v=g(s)\}
$$
and let $\overline\Gamma$ be its closure. A pair
$(s,v)\in\overline\Gamma$ is a Reny solution if, for every player $i$,
$$
  \sup_{t_i\in S_i} \underline g_i(t_i,s_{-i})\le v_i,
$$
where $\underline g_i$ is the lower semicontinuous regularization of $g_i$ with
respect to the opponents' variables.

## References

- [MFoGT, Definitions 4.8.1 and 4.8.2] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Graph closure and Reny solution for discontinuous games.
