---
id: math.minimax.minimax_from_loomis
title: Minimax via the All-Ones Specialization of Loomis
kind: proof-plan
status: formalized
primary_topic: math
topics:
  - math
  - math.minimax
target: game_theory.strategic_game.zero_sum.von_neumann_minimax
plan_status: selected
uses:
  - math.minimax.loomis_theorem
  - game_theory.strategic_game.zero_sum.maximin_le_minimax
lean:
  modules:
    - EconCSLib.Math.Minimax.MinimaxLoomis
    - EconCSLib.Math.Minimax.Loomis
  declarations:
    - MinimaxLoomis.singleton_of_card_one
    - MinimaxLoomis.dropEquiv
    - MinimaxLoomis.sum_split_at
    - MinimaxLoomis.extendDropColumn
    - MinimaxLoomis.extendDropRow
    - MinimaxLoomis.wsum_extendDropColumn
    - MinimaxLoomis.wsum_extendDropRow
    - Loomis.minmax_from_general
    - Loomis.lamB0_one
    - Loomis.muB0_one
source:
  spans:
    - artifact: mfogt
      locator: "Chapter 2, Section 2.3, Theorem 2.3.1"
      format: section
      note: "Simplified Loomis induction proof of the finite von Neumann minimax theorem"
verification:
  statement: accepted
  proof: accepted
  alignment: aligned
generality:
  reviewed: true
  prompt: "Why is finite minimax a direct corollary of Loomis, and what does the Lean implementation actually do?"
  verdict: "Minimax is the $B = \\mathbf{1}$ specialisation of Loomis [[node:zero_sum.minimax.loomis_theorem]]: $xB$ and $By$ are the all-ones vectors on $\\Delta(I)$ and $\\Delta(J)$, so $xA \\ge v\\,xB$ and $Ay \\le v\\,By$ collapse to the saddle-point inequalities $\\min_j (xA)_j \\ge v \\ge \\max_i (Ay)_i$. The Lean module `EconCSLib.StrategicGame.Loomis` now formalises the general positive-$B$ Loomis theorem [[node:zero_sum.minimax.loomis_theorem]] and re-derives finite minimax as the corollary `Loomis.minmax_from_general`, which is now the sole route. `EconCSLib.StrategicGame.MinimaxLoomis` keeps only the shared foundational layer (aggregates, attainment, weak duality, column/row drop-extend infra); its earlier inlined induction was removed as redundant once the general proof subsumed it."
tags:
  - zero-sum
  - minimax
  - loomis
  - proof-plan
---

# Minimax via the All-Ones Specialization of Loomis

This proof-plan node records the **selected** route the library uses to close
the finite von Neumann minimax theorem
([[node:game_theory.strategic_game.zero_sum.von_neumann_minimax]]): take the Loomis theorem
([[node:math.minimax.loomis_theorem]]) and specialise the positive matrix
$B$ to the all-ones matrix $\mathbf{1}$. An alternative, ordered-field-generic
route is `Minimax.minimax`
([[node:math.minimax.ordered_field_minimax]]), proved sorry-free by von
Neumann symmetrisation over any linearly ordered field.

*Proof (specialization of Loomis).* Apply the Loomis theorem
[[node:math.minimax.loomis_theorem]] with the positive matrix
$B = \mathbf{1}$ (the all-ones $I \times J$ matrix). It produces
$x \in \Delta(I)$, $y \in \Delta(J)$, and $v \in \mathbb{R}$ with
$$
  xA \ge v \cdot xB \qquad\text{and}\qquad Ay \le v \cdot By.
$$
For every probability vector $x \in \Delta(I)$ and $y \in \Delta(J)$ the
all-ones vectors $xB$ and $By$ are identically $1$. Hence the Loomis
inequalities collapse to
$$
  \sum_i x_i A(i, j) \ge v \quad\text{for every } j \in J,
  \qquad
  \sum_j y_j A(i, j) \le v \quad\text{for every } i \in I.
$$
The first inequality says $x$ guarantees at least $v$ for player I, so
$\lambda_0 \ge v$; the second says $y$ holds player I to at most $v$, so
$\mu_0 \le v$. Weak duality $\lambda_0 \le \mu_0$
([[node:game_theory.strategic_game.zero_sum.maximin_le_minimax]]) closes the sandwich:
$\lambda_0 = \mu_0 = v$, with $(x, y)$ the asserted optimisers.

*Lean implementation note.* The Lean development now formalises the general
positive-$B$ Loomis theorem in `EconCSLib.StrategicGame.Loomis` and
re-derives finite minimax as the one-line corollary
`Loomis.minmax_from_general`, which calls `loomis_value_eq` at the
all-ones matrix `B = fun _ _ => 1` and uses the bridge lemmas
`lamB0_one` and `muB0_one` to translate `lamB0 A 1` back to
`MinimaxLoomis.lam0 A` (resp. `muB0`/`mu0`). This corollary is now the sole
route: the earlier standalone induction in
`EconCSLib.StrategicGame.MinimaxLoomis` was removed as redundant. That module
now contributes only the shared foundational scaffold reused by the general
proof — the aggregates, the existence + weak-duality step
([[node:game_theory.strategic_game.zero_sum.lam_mu_existence]]), and the
column/row drop-extend infrastructure — built on the core simplex layer
([[node:math.simplex.pure]], [[node:math.simplex.continuity]],
[[node:math.simplex.mix]], and [[node:math.simplex.bounded_by_value]]).

## References

- [MFoGT, Chapter 2, Section 2.3, Thm. 2.3.1] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Finite von Neumann minimax theorem.
- [MFoGT, Thm. 2.5.1] Same. Loomis theorem; minimax is the $B = \mathbf{1}$ specialisation.
