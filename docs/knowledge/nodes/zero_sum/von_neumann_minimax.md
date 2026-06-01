---
id: game_theory.strategic_game.zero_sum.von_neumann_minimax
title: Von Neumann Minimax Theorem
kind: theorem
status: proved
proved_via_plan: math.minimax.minimax_from_loomis
primary_topic: game_theory.zero_sum
topics:
  - game_theory.zero_sum
  - game_theory.zero_sum.minimax
uses: []
lean:
  modules:
    - EconCSLib.GameTheory.StrategicGame.ZeroSum.MatrixGame
  declarations:
    - MatrixGame.maximin_le_minimax
    - MatrixGame.minimax_theorem
    - MatrixGame.minimax_optimal_strategies
source:
  spans:
    - artifact: mfogt
      locator: "Chapter 2, Theorem 2.3.1"
      format: section
      note: "Von Neumann minimax theorem for finite zero-sum games"
verification:
  statement: accepted
  proof: accepted
  alignment: aligned
generality:
  reviewed: true
  prompt: "Which route closes this theorem in Lean?"
  verdict: "The finite minimax theorem is closed in Lean as the `B = 𝟙` specialisation of the general Loomis theorem, exported as `Loomis.minmax_from_general` and surfaced at the matrix-game layer as `minimax_theorem`; it is fully formalised. (An earlier standalone simplified-Loomis induction, `MinimaxLoomis.minmax_theorem'`, was removed as redundant once the general proof subsumed it.) The ordered-field generalisation (any linearly ordered field) is proved separately, sorry-free, as `Minimax.minimax` by von Neumann symmetrisation."
tags:
  - zero-sum
  - value
  - minimax
  - theorem
---

# Von Neumann Minimax Theorem

Every finite two-player zero-sum matrix game has a value in mixed strategies:

$$\max_x \min_j E_A(x,j) = \min_y \max_i E_A(i,y).$$

Equivalently, there are optimal mixed strategies $x^\ast$ and $y^\ast$ and a
value $v$ such that player I guarantees at least $v$ against every column and
player II holds player I to at most $v$ against every row.

Two proof routes attach to this theorem as separate proof-plan nodes:

- [[node:math.minimax.minimax_from_loomis]] (**selected**): finite
  minimax is the $B = \mathbf{1}$ specialisation of the Loomis theorem
  ([[node:math.minimax.loomis_theorem]]). Fully formalised in Lean
  (`EconCSLib.StrategicGame.MinimaxLoomis`), which inlines the $B = \mathbf{1}$
  case of the Loomis induction
  ([[node:math.minimax.loomis_induction_proof]]) rather than first porting
  the general positive-$B$ Loomis statement. The compactness/continuity
  building blocks it relies on live in the core simplex layer
  ([[node:math.simplex.pure]], [[node:math.simplex.continuity]],
  [[node:math.simplex.bounded_by_value]]) and the existence + weak-duality
  step is [[node:game_theory.strategic_game.zero_sum.lam_mu_existence]]; weak duality
  ([[node:game_theory.strategic_game.zero_sum.maximin_le_minimax]]) supplies one direction of the
  equality.
- `Minimax.minimax` (**proved**, ordered-field-generic): a von Neumann
  symmetrisation proof that works over any linearly ordered field — embed the
  game in a skew-symmetric matrix and read the saddle point off its value-0
  optimal strategy, which exists by the Theorem of the Alternative. Sorry-free,
  needing no compactness or order-completeness
  ([[node:math.minimax.ordered_field_minimax]]).

## References

- [MFoGT, Chapter 2, Thm. 2.3.1] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Von Neumann minimax theorem for finite zero-sum games.
