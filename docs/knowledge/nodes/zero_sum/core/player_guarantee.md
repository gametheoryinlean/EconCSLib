---
id: game_theory.strategic_game.zero_sum.core.player_guarantee
title: Player Guarantee
kind: definition
status: formalized
primary_topic: game_theory.zero_sum
topics:
  - game_theory.zero_sum
  - game_theory.zero_sum.core
uses:
  - game_theory.strategic_game.zero_sum.matrix_game
lean:
  modules:
    - EconCSLib.GameTheory.StrategicGame.ZeroSum.MatrixGame
  declarations:
    - MatrixGame.IsPlayerIGuarantee
    - MatrixGame.IsPlayerIIGuarantee
source:
  spans:
    - artifact: mfogt
      locator: "Definition 2.2.2"
      format: section
      note: "Guarantees for both players in a zero-sum game"
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
tags:
  - zero-sum
  - value
  - guarantee
---

# Player Guarantee

In the finite mixed-strategy version, $w$ is a **guarantee for player I**
when some $x \in \Delta(I)$ achieves $E_A(x, j) \ge w$ for every pure
$j \in J$. Symmetrically, $w$ is a **guarantee for player II** when some
$y \in \Delta(J)$ achieves $E_A(i, y) \le w$ for every pure $i \in I$.
Equivalently, $w$ is a player I guarantee iff $w \le \operatorname{val}(A)$
(the maximin), and dually for player II with $\operatorname{val}(A) \le w$
(the minimax).

The abstract pure-strategy version ($\exists i, \forall j, g(i, j) \ge w$)
collapses on finite mixed extensions to the same scalar bound via the
simplex-side order characterisation
([[node:math.simplex.bounded_by_value]]).

## References

- [MFoGT, Def. 2.2.2] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Guarantees for both players in a zero-sum game.
