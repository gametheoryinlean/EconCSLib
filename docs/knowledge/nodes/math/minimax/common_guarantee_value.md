---
id: math.minimax.common_guarantee_value
title: Common Guarantee Gives The Value
kind: lemma
status: proved
primary_topic: math
topics:
  - math
  - math.minimax
uses:
  - game_theory.strategic_game.zero_sum.von_neumann_minimax
  - game_theory.strategic_game.zero_sum.core.player_guarantee
  - game_theory.strategic_game.zero_sum.core.value
  - game_theory.strategic_game.zero_sum.maximin_le_minimax
lean:
  modules:
    - EconCSLib.GameTheory.StrategicGame.ZeroSum.MatrixGame
  declarations:
    - MatrixGame.common_guarantee_eq_value
source:
  spans:
    - artifact: mfogt
      locator: "Lemma 2.2.8"
      format: section
      note: "A common guarantee is unique and equal to the value"
verification:
  statement: accepted
  proof: accepted
  alignment: aligned
tags:
  - zero-sum
  - value
  - optimal-strategy
---

# Common Guarantee Gives The Value

If player I and player II both guarantee the same number $w$, then $w$ is
the unique value of the game, and the strategies witnessing the two
guarantees are optimal.

*Proof.* The two guarantees and weak duality give the chain
$$
  w \le \underline v \le \overline v \le w.
$$
Thus $\underline v=\overline v=w$, and the witnessing strategies attain the
value. The minimax theorem ([[node:game_theory.strategic_game.zero_sum.von_neumann_minimax]]) closes the
inner two inequalities, the player-guarantee bound is the outer pair
([[node:game_theory.strategic_game.zero_sum.core.player_guarantee]]).

## References

- [MFoGT, Lem. 2.2.8] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. A common guarantee is unique and equal to the value.
