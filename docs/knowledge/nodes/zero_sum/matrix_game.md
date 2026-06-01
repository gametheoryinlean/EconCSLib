---
id: game_theory.strategic_game.zero_sum.matrix_game
title: Matrix Game
kind: definition
status: formalized
primary_topic: game_theory.zero_sum
topics:
  - game_theory.zero_sum
  - game_theory.zero_sum.core
uses:
  - game_theory.strategic_game.zero_sum.zero_sum_game
lean:
  modules:
    - EconCSLib.GameTheory.StrategicGame.ZeroSum.MatrixGame
  declarations:
    - MatrixGame
source:
  spans:
    - artifact: mfogt
      locator: "Chapter 2, Definition 2.2.1"
      format: section
      note: "Finite two-player zero-sum games in matrix form"
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
generality:
  reviewed: true
  prompt: "What scalar field does the matrix game's payoff live in?"
  verdict: "Field-generic: `MatrixGame (I J : Type*) (𝕜 : Type := ℚ)` has `g : I → J → 𝕜` with the scalar 𝕜 at the trailing position. The structure carries no typeclass on 𝕜 (Bourbaki-minimal data); ordered-field hypotheses are introduced at the use sites that need them (`[Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]` for the bilinear-payoff / saddle layer, `[ConditionallyCompleteLinearOrder 𝕜]` for the `sSup`-based `maximin`/`minimax`/`value` definitions). The default ℚ keeps unannotated `MatrixGame I J` Bourbaki-minimal; reaching for ℝ is an explicit `MatrixGame I J ℝ` at the use site. See #54."
tags:
  - zero-sum
  - matrix-game
  - finite-game
---

# Matrix Game

A finite two-player zero-sum matrix game is specified by finite row and column
sets $I,J$ and a payoff matrix valued in a scalar field $\mathbb{K}$

$$A : I \times J \to \mathbb{K}.$$

Player I chooses a row, player II chooses a column, player I receives
$A(i,j)$, and player II receives $-A(i,j)$. The default scalar in
the Lean structure is $\mathbb{Q}$ (no order completeness assumed); the
canonical instantiations are $\mathbb{Q}$ (where the value still lies in
the field by LP but the `sSup`-based `maximin/minimax`
definitions are unavailable) and $\mathbb{R}$ (where order completeness
gives the full Loomis / minimax theorem).

## References

- [MFoGT, Chapter 2, Def. 2.2.1] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Finite two-player zero-sum games in matrix form.
