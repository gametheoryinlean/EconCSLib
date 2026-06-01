---
id: game_theory.strategic_game.zero_sum.core.duality_gap
title: Duality Gap In A Matrix Game
kind: definition
status: formalized
primary_topic: game_theory.zero_sum
topics:
  - game_theory.zero_sum
  - game_theory.zero_sum.core
uses:
  - game_theory.strategic_game.zero_sum.core.mixed_extension
  - game_theory.strategic_game.zero_sum.maximin_minimax
lean:
  modules:
    - EconCSLib.GameTheory.StrategicGame.ZeroSum.MatrixGame
  declarations:
    - MatrixGame.dualityGap
source:
  spans:
    - artifact: mfogt
      locator: "Section 2.7, proof of Proposition 2.7.3"
      format: section
      note: "L(y), M(x), and W(x,y)=L(y)-M(x) used for continuous fictitious play"
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
tags:
  - zero-sum
  - value
  - fictitious-play
---

# Duality Gap In A Matrix Game

For a finite matrix game with bilinear payoff $g(x,y)=xAy$, define
$$
  L(y)=\max_{x'\in\Delta(I)} g(x',y),
  \qquad
  M(x)=\min_{y'\in\Delta(J)} g(x,y').
$$
The **point-wise duality gap** at $(x,y)$ is
$$
  W(x,y)=L(y)-M(x)\ge 0.
$$

The gap is zero exactly when $x$ and $y$ are optimal strategies: $W(x,y)=0$
says the best payoff player I can obtain against $y$ equals the worst payoff
player I can secure with $x$, so the two one-sided guarantees meet at the
value.

The Lean development uses the finite-mixed-strategy specialisation
`L(y) = A.guarantee_II y` (maximum over pure rows) and
`M(x) = A.guarantee_I x` (minimum over pure columns); the Loomis-style
order-characterisation lemmas turn this into the full bilinear gap.

## References

- [MFoGT, Section 2.7, proof of Prop. 2.7.3] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. L(y), M(x), and W(x,y)=L(y)-M(x) used for continuous fictitious play.
