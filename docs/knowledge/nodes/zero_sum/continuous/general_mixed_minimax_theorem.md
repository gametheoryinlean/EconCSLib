---
id: game_theory.strategic_game.zero_sum.continuous.general_mixed_minimax_theorem
title: General Mixed Minimax Theorem
kind: theorem
status: admitted
primary_topic: game_theory.zero_sum
topics:
  - game_theory.zero_sum
  - game_theory.zero_sum.continuous
uses:
  - game_theory.strategic_game.zero_sum.continuous.compact_mixed_vs_finite_support_minimax
source:
  spans:
    - artifact: mfogt
      locator: "Theorem 3.3.2"
      format: section
      note: "Mixed minimax theorem for compact Hausdorff strategy spaces"
verification:
  statement: accepted
  proof: accepted
tags:
  - zero-sum
  - mixed-strategy
  - minimax
  - continuous-game
---

# General Mixed Minimax Theorem

Let $G=(S,T,g)$ be a zero-sum game such that:

1. $S$ and $T$ are compact Hausdorff topological spaces;
2. for each $t\in T$, $g(\cdot,t)$ is upper semicontinuous, and for each $s\in S$,
   $g(s,\cdot)$ is lower semicontinuous;
3. $g$ is bounded and measurable for the product Borel sigma-algebra.

Then the mixed extension
$$
  (\Delta(S),\Delta(T),g)
$$
has a value. Each player has a mixed optimal strategy, and for every
$\epsilon>0$ each player has an $\epsilon$-optimal strategy with finite support.

*Proof.* Apply the compact mixed-versus-finite-support minimax proposition twice: once to
$(\Delta(S),\Delta_f(T),g)$ and once dually to $(\Delta_f(S),\Delta(T),g)$. Let
$v^+$ and $v^-$ be the resulting values. Optimal strategies $\sigma$ and $\tau$
for the two one-sided games satisfy inequalities against all pure opponent
strategies. Fubini's theorem gives
$$
  v^+\le \int g\,d(\sigma\otimes\tau)\le v^-.
$$
Since always $v^-\le v^+$, equality follows.

## References

- [MFoGT, Thm. 3.3.2] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Mixed minimax theorem for compact Hausdorff strategy spaces.
