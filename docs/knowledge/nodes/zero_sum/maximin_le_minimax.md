---
id: game_theory.strategic_game.zero_sum.maximin_le_minimax
title: Maximin is Bounded by Minimax
kind: lemma
status: proved
primary_topic: game_theory.zero_sum
topics:
  - game_theory.zero_sum
  - game_theory.zero_sum.minimax
uses:
  - game_theory.strategic_game.zero_sum.maximin_minimax
lean:
  modules:
    - EconCSLib.GameTheory.StrategicGame.ZeroSum.MatrixGame
  declarations:
    - MatrixGame.maximin_le_minimax
source:
  spans:
    - artifact: mfogt
      locator: "Chapter 2, Lemmas 2.2.4 and 2.2.8"
      format: section
      note: "The lower value never exceeds the upper value"
    - artifact: mfogt
      locator: "Lemma 2.2.4"
      format: section
      note: "Abstract pure-strategy weak duality (merged from zero_sum.core.maxmin_le_minmax)."
verification:
  statement: accepted
  proof: accepted
  alignment: aligned
generality:
  reviewed: true
  prompt: "Is the inequality logically prior to the minimax theorem?"
  verdict: "Yes. The equality theorem strengthens this general weak duality inequality."
tags:
  - zero-sum
  - value
  - minimax
---

# Maximin is Bounded by Minimax

For every finite matrix game,

$$\max_x \min_j E_A(x,j) \le \min_y \max_i E_A(i,y).$$

This is the weak-duality inequality: player I's best guaranteed payoff cannot
exceed player II's best upper bound on player I's payoff.

*Proof.* For every mixed row $x$ and mixed column $y$,
$$
  \min_j E_A(x,j) \le E_A(x,y) \le \max_i E_A(i,y).
$$
Taking the supremum over $x$ on the left preserves the first inequality against
the fixed upper bound $\max_i E_A(i,y)$, so
$$
  \max_x \min_j E_A(x,j) \le \max_i E_A(i,y)
$$
for every $y$. Taking the infimum over $y$ gives
$$
  \max_x \min_j E_A(x,j) \le \min_y \max_i E_A(i,y).
$$

## Abstract pure-strategy form

On arbitrary nonempty strategy sets $I, J$ with payoff $g : I \times J \to
\mathbb{R}$ and pure-strategy extrema (no mixing), the same argument gives
weak duality

$$
  \underline v = \sup_{i \in I} \inf_{j \in J} g(i,j)
              \;\le\; \inf_{j \in J} \sup_{i \in I} g(i,j) = \overline v.
$$

*Proof.* For every pair $(i,j)$,
$$
  \inf_{j' \in J} g(i,j') \le g(i,j) \le \sup_{i' \in I} g(i',j).
$$
Taking the supremum over $i$ on the left and the infimum over $j$ on the right
gives $\underline v \le \overline v$. $\square$

This abstract form is what nodes outside the finite-mixed setting cite. The
Lean formalisation lives in the finite-mixed instantiation above.

## References

- [MFoGT, Chapter 2, Lemmas 2.2.4 and 2.2.8] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. The lower value never exceeds the upper value.
- [MFoGT, Lem. 2.2.4] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Abstract pure-strategy weak duality (merged from `zero_sum.core.maxmin_le_minmax`).
