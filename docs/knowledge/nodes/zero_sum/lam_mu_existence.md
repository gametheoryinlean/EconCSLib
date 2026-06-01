---
id: game_theory.strategic_game.zero_sum.lam_mu_existence
title: Existence of Optimal Mixed Strategies (Loomis Foundations)
kind: theorem
status: proved
primary_topic: game_theory.zero_sum
topics:
  - game_theory.zero_sum
  - game_theory.zero_sum.minimax
uses:
  - math.simplex.continuity
  - math.simplex.bounded_by_value
  - game_theory.strategic_game.zero_sum.maximin_minimax
lean:
  modules:
    - EconCSLib.Math.Minimax.MinimaxLoomis
  declarations:
    - MinimaxLoomis.lam.aux.continuous
    - MinimaxLoomis.mu.aux.continuous
    - MinimaxLoomis.lam.aux.bddAbove
    - MinimaxLoomis.mu.aux.bddBelow
    - MinimaxLoomis.lam.aux.le_lam0
    - MinimaxLoomis.mu.aux.ge_mu0
    - MinimaxLoomis.exists_xx_lam0
    - MinimaxLoomis.exists_yy_mu0
    - MinimaxLoomis.lam0_le_mu0
source:
  spans:
    - artifact: mfogt
      locator: "Chapter 2, Section 2.3"
      format: section
      note: "Existence of mixed optimisers and weak duality, prior to the inductive minimax theorem"
verification:
  statement: accepted
  proof: accepted
  alignment: aligned
generality:
  reviewed: true
  prompt: "Why isolate existence + weak duality before the full minimax theorem?"
  verdict: "These statements only need compactness + continuity and hold without the inductive step; isolating them makes the proof graph reusable for other minimax routes."
tags:
  - zero-sum
  - minimax
  - existence
  - weak-duality
---

# Existence of Optimal Mixed Strategies (Loomis Foundations)

For a finite matrix game $A : I \times J \to \mathbb{R}$, the row player's
guarantee function is
$$\lambda_{\mathrm{aux}}(x) = \min_{j \in J} \sum_{i \in I} x_i A(i,j),$$
and the column player's loss-cap function is
$$\mu_{\mathrm{aux}}(y) = \max_{i \in I} \sum_{j \in J} y_j A(i,j).$$
The two scalar values
$$\lambda_0 = \sup_{x \in \Delta(I)} \lambda_{\mathrm{aux}}(x) \quad \text{and} \quad
  \mu_0 = \inf_{y \in \Delta(J)} \mu_{\mathrm{aux}}(y)$$
are the maxmin and minmax values of the game.

This node packages four facts that hold *before* the inductive minimax
identity is established:

1. **Continuity.** Both $\lambda_{\mathrm{aux}}$ and $\mu_{\mathrm{aux}}$ are
   continuous on the (compact) mixed-strategy simplices.
2. **Boundedness.** $\lambda_{\mathrm{aux}}$ is bounded above and
   $\mu_{\mathrm{aux}}$ is bounded below by the obvious extremes of $A$.
3. **Achievement.** There exist mixed strategies $x^\ast$ and $y^\ast$ such
   that $\sum_i x^\ast_i A(i,j) \ge \lambda_0$ for every column $j$ and
   $\sum_j y^\ast_j A(i,j) \le \mu_0$ for every row $i$.
4. **Weak duality.** $\lambda_0 \le \mu_0$.

*Proof.* Continuity of $\lambda_{\mathrm{aux}}$ is the finite infimum of
continuous weighted sums (`Continuous.finset_inf'_apply`); the proof for
$\mu_{\mathrm{aux}}$ is dual. Boundedness follows because each weighted sum
is bounded by the extreme matrix entry. The supremum
$\lambda_0$ is achieved by the extreme-value theorem applied to the compact
mixed-strategy simplex (`IsCompact.exists_isMaxOn`), and the optimiser
realises $\lambda_0$ on every pure column by the infimum definition; the
$\mu_0$ side is symmetric. Weak duality combines the two optimisers in the
bilinear payoff:
$$\lambda_0 \le \sum_{i,j} x^\ast_i y^\ast_j A(i,j) \le \mu_0,$$
using the pointwise-to-weighted bound transfer from
[[node:math.simplex.bounded_by_value]].

## References

- [MFoGT, Chapter 2, Section 2.3] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Existence of mixed optimisers and weak duality, prior to the inductive minimax theorem.
