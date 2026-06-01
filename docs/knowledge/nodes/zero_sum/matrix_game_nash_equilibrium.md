---
id: game_theory.strategic_game.zero_sum.matrix_game_nash_equilibrium
title: Mixed Nash Equilibrium of a Matrix Game
kind: theorem
status: proved
primary_topic: game_theory.zero_sum
topics:
  - game_theory.zero_sum
  - game_theory.zero_sum.core
uses:
  - game_theory.strategic_game.zero_sum.von_neumann_minimax
  - math.minimax.ordered_field_minimax
  - game_theory.strategic_game.zero_sum.mixed_matrix_payoff
  - math.simplex.bounded_by_value
lean:
  modules:
    - EconCSLib.GameTheory.StrategicGame.ZeroSum.MatrixGame
    - EconCSLib.GameTheory.StrategicGame.MixedStrategy
  declarations:
    - MatrixGame.exists_mixed_nash_equilibrium
    - MatrixGame.expectedPayoff_toStrategicGame_zero
    - MatrixGame.expectedPayoff_toStrategicGame_one
    - MatrixGame.exists_strategic_game_nash_equilibrium
source:
  spans:
    - artifact: msz-game-theory
      locator: "Chapter 5, Theorems 5.11 and 5.13"
      format: section
      note: "Existence of mixed Nash equilibrium in a finite matrix game via the saddle-point equivalence"
verification:
  statement: accepted
  proof: accepted
  alignment: aligned
generality:
  reviewed: true
  prompt: "Can `IsMixedNashEq` be stated over ℚ for matrix games, and is existence available over ordered fields other than ℝ?"
  verdict: "**Statement:** Yes — `MatrixGame.IsMixedNashEq` is field-generic in Lean (#54). It is an inequality predicate that only needs `[Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]`, so it is well-formed over ℚ, ℝ, ℝ((ε)), and any other linearly ordered field. The corresponding value predicate is [[node:zero_sum.minimax.value_predicates]] (`IsValue / IsMaximin / IsMinimax`). **Existence:** now formalised both ways, sorry-free, and `MatrixGame.exists_mixed_nash_equilibrium` is itself field-generic. (a) ℝ — via the simplified-Loomis route ([[node:zero_sum.minimax.minimax_from_loomis]]; compactness / continuity, ℝ-specific). (b) **Any linearly ordered field** — `MatrixGame.exists_mixed_nash_equilibrium` packages the field-generic saddle `Minimax.minimax` ([[node:math.minimax.ordered_field_minimax]]), proved by von Neumann symmetrisation + the Theorem of the Alternative: embed the game in a skew-symmetric matrix whose value-0 optimal strategy exists as a pure feasibility fact — no compactness, no order-completeness, no LP-optimum lemma. The equilibrium and saddle value live in the same field as the payoff matrix."
tags:
  - zero-sum
  - matrix-game
  - mixed-strategy
  - nash-equilibrium
  - saddle-point
---

# Mixed Nash Equilibrium of a Matrix Game

For a finite matrix game $A : I \times J \to \mathbb{R}$, there exist mixed
strategies $x^\ast \in \Delta(I)$ and $y^\ast \in \Delta(J)$ such that

$$E_A(x, y^\ast) \le E_A(x^\ast, y^\ast) \le E_A(x^\ast, y)$$

for every $x \in \Delta(I)$ and $y \in \Delta(J)$ — the standard
saddle-point form of mixed Nash equilibrium in a zero-sum two-player game.

This is the strategy-level packaging of
[[node:game_theory.strategic_game.zero_sum.von_neumann_minimax]] and is what is usually called "the
matrix game has a (mixed) Nash equilibrium".

The Lean development records the equilibrium in two complementary ways and
proves them equivalent in the embedded strategic game:

* `MatrixGame.IsMixedNashEq xx yy` — the saddle-point predicate directly on
  the matrix game, easy to reason about and the form used to prove existence
  (`MatrixGame.exists_mixed_nash_equilibrium`).
* `MatrixGame.toStrategicGame` — the explicit two-player zero-sum strategic
  game (payoffs $A$ and $-A$) whose `StrategicGame.IsMixedNashEq` reduces to
  the saddle-point form. The full bridge theorem
  `MatrixGame.exists_strategic_game_nash_equilibrium` packages a Nash
  equilibrium of the embedded strategic game built from the saddle-point pair,
  using the lemmas `expectedPayoff_toStrategicGame_zero` /
  `expectedPayoff_toStrategicGame_one` that compute the
  `StrategicGame.expectedPayoff` as `±A.E (p 0) (p 1)`.

The supporting `StrategicGame.MixedStrategy` / `MixedProfile` /
`expectedPayoff` / `IsMixedNashEq` API is polymorphic in the payoff field
`U` (any `Field U` with `LinearOrder` and `IsStrictOrderedRing`), so it
specialises to both $\mathbb{Q}$ (for constructive `native_decide` examples
such as Rock–Paper–Scissors) and $\mathbb{R}$ (for the Loomis-based existence
theorem).

*Proof.* Apply `MatrixGame.minimax_optimal_strategies` (closed by the
simplified-Loomis induction) to obtain $x^\ast$, $y^\ast$, and a value $v$
with $E_A(x^\ast, j) \ge v$ for every pure column $j$ and
$E_A(i, y^\ast) \le v$ for every pure row $i$. By
[[node:math.simplex.bounded_by_value]] this transfers to mixed responses:
$E_A(x^\ast, y') \ge v$ for every $y' \in \Delta(J)$ and
$E_A(x', y^\ast) \le v$ for every $x' \in \Delta(I)$. Taking $x' = x^\ast$
and $y' = y^\ast$ shows $E_A(x^\ast, y^\ast) = v$, and the chain
$E_A(x, y^\ast) \le v = E_A(x^\ast, y^\ast) \le E_A(x^\ast, y)$ holds for
every $x$ and $y$, which is exactly the saddle-point form.

## Over ℚ and other ordered fields

The Loomis existence proof goes through the extreme value theorem on the
compact mixed-strategy simplex $\Delta(I) \subseteq \mathbb{R}^{|I|}$. The
required compactness is the standard Heine–Borel statement on $\mathbb{R}^n$
and is not available for $\mathbb{Q}^n$, so *that* route intrinsically
produces real-valued strategies. Existence over $\mathbb{Q}$ and every other
linearly ordered field is nonetheless available, sorry-free, through the
symmetrisation route `Minimax.minimax`
([[node:math.minimax.ordered_field_minimax]]): it embeds the game in a
skew-symmetric matrix and extracts the saddle point as a pure feasibility
fact (the Theorem of the Alternative), needing no compactness or
order-completeness. `MatrixGame.exists_mixed_nash_equilibrium` is built on
that route and is itself field-generic.

## References

- [MSZ, Chapter 5, Thm. 5.11 / 5.13] Maschler, Solan, and Zamir, *Game Theory*. Existence of mixed Nash equilibrium in a finite matrix game via the saddle-point equivalence.
