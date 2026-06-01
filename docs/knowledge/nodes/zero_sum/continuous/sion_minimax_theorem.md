---
id: game_theory.strategic_game.zero_sum.continuous.sion_minimax_theorem
title: Sion Minimax Theorem
kind: theorem
status: admitted
primary_topic: game_theory.zero_sum
topics:
  - game_theory.zero_sum
  - game_theory.zero_sum.continuous
uses:
  - game_theory.strategic_game.zero_sum.core.value
  - game_theory.strategic_game.zero_sum.continuous.quasi_concavity_semicontinuity
  - game_theory.strategic_game.zero_sum.continuous.intersection_lemma
source:
  spans:
    - artifact: mfogt
      locator: "Theorem 3.2.4"
      format: section
      note: "Pure-strategy minimax theorem under convexity, compactness, and semicontinuity hypotheses"
verification:
  statement: accepted
  proof: accepted
tags:
  - zero-sum
  - minimax
  - continuous-game
  - sion
---

# Sion Minimax Theorem

Let $G=(S,T,g)$ be a zero-sum game where $S$ and $T$ are subsets of Hausdorff
topological real vector spaces. Assume:

1. $S$ and $T$ are convex;
2. at least one of $S,T$ is compact;
3. for each $t\in T$, $g(\cdot,t)$ is quasi-concave and upper semicontinuous in
   $s$;
4. for each $s\in S$, $g(s,\cdot)$ is quasi-convex and lower semicontinuous in
   $t$.

Then $G$ has a value:
$$
  \sup_{s\in S}\inf_{t\in T}g(s,t)
  =
  \inf_{t\in T}\sup_{s\in S}g(s,t).
$$
Moreover, if $S$ is compact then player 1 has an optimal strategy, and if $T$ is
compact then player 2 has an optimal strategy.

*Proof.* Assume, for example, that $S$ is compact and suppose the two sides are separated
by a real number $v$. Open-cover compactness first reduces to finite subsets of
strategies, then to compact convex hulls. Minimality of the finite reduction and the
intersection lemma produce a point $t_0$ against which all reduced player-1
strategies yield payoff greater than $v$, and symmetrically a point $s_0$ against
which all reduced player-2 strategies yield payoff less than $v$. The value
$g(s_0,t_0)$ gives a contradiction.

## References

- [MFoGT, Thm. 3.2.4] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Pure-strategy minimax theorem under convexity, compactness, and semicontinuity hypotheses.
