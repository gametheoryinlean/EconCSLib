---
id: game_theory.strategic_game.zero_sum.maximin_minimax
title: Maximin and Minimax Values
kind: definition
status: formalized
primary_topic: game_theory.zero_sum
topics:
  - game_theory.zero_sum
  - game_theory.zero_sum.minimax
uses:
  - game_theory.strategic_game.zero_sum.mixed_matrix_payoff
lean:
  modules:
    - EconCSLib.GameTheory.StrategicGame.ZeroSum.MatrixGame
    - EconCSLib.GameTheory.StrategicGame.ZeroSum.MatrixGameNash
  declarations:
    - MatrixGame.guarantee_I
    - MatrixGame.guarantee_II
    - MatrixGame.maximin
    - MatrixGame.minimax
    - MatrixGame.value_eq_maximin
    - MatrixGame.value_eq_minimax
source:
  spans:
    - artifact: mfogt
      locator: "Chapter 2, Definitions 2.2.2-2.2.6"
      format: section
      note: "Guarantees, maxmin, minmax, and game value"
    - artifact: mfogt
      locator: "Definition 2.2.3"
      format: section
      note: "Abstract pure-strategy maxmin and minmax (merged from zero_sum.core.maxmin_minmax)."
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
generality:
  reviewed: true
  prompt: "Which pure responses determine the finite mixed guarantees?"
  verdict: "For a finite zero-sum matrix game, it suffices to take the minimum over pure columns and maximum over pure rows."
tags:
  - zero-sum
  - value
  - minimax
---

# Maximin and Minimax Values

For a mixed row strategy $x$, player I's guarantee is the worst expected payoff
against a pure column:

$$\gamma_I(x) = \min_{j \in J} E_A(x,j).$$

For a mixed column strategy $y$, player II's guarantee against player I is the
largest payoff player I can obtain from a pure row:

$$\gamma_{II}(y) = \max_{i \in I} E_A(i,y).$$

The maximin value is \(\sup_x \gamma_I(x)\), and the minimax value is
\(\inf_y \gamma_{II}(y)\).

## Abstract pure-strategy form

The same definition applies on arbitrary nonempty strategy sets $I, J$ and a
payoff $g : I \times J \to \mathbb{R}$, with the inner extremum ranging over
**pure** strategies (no mixing). Then the maxmin is

$$
  \underline v = \sup_{i \in I} \inf_{j \in J} g(i,j),
$$

and the minmax is

$$
  \overline v = \inf_{j \in J} \sup_{i \in I} g(i,j).
$$

The maxmin is the best amount player 1 can guarantee, and the minmax is the
least amount player 2 can guarantee as an upper bound on player 1's payoff.
The Lean library currently formalises the finite mixed-strategy instantiation
above; the abstract form is the common conceptual ancestor and the form used
when reasoning over general (e.g. infinite) strategy spaces.

## References

- [MFoGT, Chapter 2, Definitions 2.2.2-2.2.6] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Guarantees, maxmin, minmax, and game value.
- [MFoGT, Def. 2.2.3] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Abstract pure-strategy maxmin and minmax (merged from `zero_sum.core.maxmin_minmax`).
