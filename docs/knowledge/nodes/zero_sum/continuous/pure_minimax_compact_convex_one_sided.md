---
id: game_theory.strategic_game.zero_sum.continuous.pure_minimax_compact_convex_one_sided
title: One-Sided Compact Convex Minimax
kind: proposition
status: admitted
primary_topic: game_theory.zero_sum
topics:
  - game_theory.zero_sum
  - game_theory.zero_sum.continuous
uses:
  - game_theory.strategic_game.zero_sum.continuous.sion_minimax_theorem
source:
  spans:
    - artifact: mfogt
      locator: "Proposition 3.2.5"
      format: section
      note: "Pure minimax with compact player-1 strategy set and convexity replacing topology on T"
verification:
  statement: accepted
  proof: accepted
tags:
  - zero-sum
  - minimax
  - continuous-game
---

# One-Sided Compact Convex Minimax

Let $G=(S,T,g)$ be a zero-sum game. Assume:

1. $S$ is convex and compact;
2. $T$ is convex;
3. for each $t\in T$, $g(\cdot,t)$ is quasi-concave and upper semicontinuous;
4. for each $s\in S$, $g(s,\cdot)$ is convex.

Then
$$
  \sup_{s\in S}\inf_{t\in T}g(s,t)
  =
  \inf_{t\in T}\sup_{s\in S}g(s,t),
$$
and player 1 has an optimal strategy.

*Proof.* Assume a strict gap around $v$. Compactness gives finitely many opponent
strategies that cover $S$ by strict sublevel sets. Perturb these finitely many
strategies toward a relative-interior point so that the payoff becomes continuous
on their convex hull. Sion's theorem applies to the compact convex reduced game,
contradicting the assumed strict gap.

## References

- [MFoGT, Prop. 3.2.5] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Pure minimax with compact player-1 strategy set and convexity replacing topology on T.
