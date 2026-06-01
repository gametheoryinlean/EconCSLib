---
id: math.minimax.value_predicates
title: Field-Generic Value Predicates
kind: definition
status: formalized
primary_topic: math
topics:
  - math
  - math.minimax
uses:
  - game_theory.strategic_game.zero_sum.maximin_minimax
lean:
  modules:
    - EconCSLib.GameTheory.StrategicGame.ZeroSum.MatrixGame
  declarations:
    - MatrixGame.IsMaximin
    - MatrixGame.IsMinimax
    - MatrixGame.IsValue
source:
  spans:
    - artifact: mfogt
      locator: "Chapter 2, Section 2.2"
      format: section
      note: "Saddle-point characterisation of maxmin / minmax / value, in field-generic predicate form"
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
generality:
  reviewed: true
  prompt: "Why predicate forms when `maximin` / `minimax` / `value` are already `sSup`-based defs?"
  verdict: "The `sSup`-based defs `MatrixGame.maximin / minimax / value` need `[ConditionallyCompleteLinearOrder 𝕜]`, so they are unavailable over ℚ and other ordered fields without order completeness. The predicate forms `IsMaximin / IsMinimax / IsValue` are pure inequality statements that only need `[Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]`, so they characterise the same quantities over any linearly ordered field. They also let downstream theorems state \"the value is `v`\" without committing to a `sSup` construction. Over ℝ the predicate form is equivalent to the `sSup`-based one; the `IsValue ↔ value = v` bridge is left to a follow-up Lean lemma."
tags:
  - zero-sum
  - value
  - predicate
  - field-generic
---

# Field-Generic Value Predicates

For a finite matrix game $A : I \times J \to \mathbb{K}$ with payoff in any
linearly ordered field $\mathbb{K}$, the maxmin / minmax / saddle-value
notions admit the following predicate characterisations that do **not**
invoke any `sSup` / `sInf`:

**Maximin (predicate form).** $v$ is a *maximin value* of $A$ when

$$
  \bigl(\exists x \in \Delta(I),\ \forall j \in J,\ v \le \sum_i x_i\, A(i,j)\bigr)
  \quad\text{and}\quad
  \bigl(\forall w,\ (\exists x \in \Delta(I),\ \forall j,\ w \le \sum_i x_i\, A(i,j)) \Rightarrow w \le v\bigr).
$$

That is: some row strategy guarantees at least $v$ against every column
(existence), and no strictly larger value is achievable (maximality).

**Minimax (predicate form).** Dual: $v$ is a *minimax value* when some
column strategy caps player I's payoff at $v$, and no strictly smaller
cap is achievable.

**Value (saddle-point form).** $v$ is *the value* of $A$ when there are
row and column strategies $x, y$ with

$$
  \forall j,\ v \le \sum_i x_i\, A(i,j)
  \qquad\text{and}\qquad
  \forall i,\ \sum_j y_j\, A(i,j) \le v.
$$

The saddle-point form is the existential combination of the two one-sided
guarantee statements; it is equivalent to "value exists and equals $v$"
without invoking $\sup$ / $\inf$.

## Relationship to `sSup`-based definitions

When $\mathbb{K}$ admits order completeness (e.g. $\mathbb{K} = \mathbb{R}$
via `Real.instConditionallyCompleteLinearOrder`), the `sSup`-based
[[node:game_theory.strategic_game.zero_sum.maximin_minimax]] definitions are available, and:

- `IsMaximin A v ↔ v = A.maximin` (assuming the supremum is attained),
- `IsMinimax A v ↔ v = A.minimax`,
- `IsValue A v` is equivalent to the conjunction of the above when the
  minimax theorem ([[node:game_theory.strategic_game.zero_sum.von_neumann_minimax]]) holds.

The Lean library realises `IsMaximin`, `IsMinimax`, `IsValue` in
`EconCSLib.StrategicGame.Minimax`. The bridge lemmas between the
predicate and `sSup` forms are tracked as Phase 2 follow-up of #54.

## Why this matters

An ordered-field-generic value route constructs the value as a witness over
any linearly ordered field, not as a supremum, so it is naturally phrased via
`IsValue` rather than via `value`. The symmetrisation route `Minimax.minimax`
([[node:math.minimax.ordered_field_minimax]]) is exactly this: it delivers the
optimal value and strategies over any
`[Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]` without requiring order
completeness, so the predicate forms are the natural interface for it.

## References

- [MFoGT, Chapter 2, Section 2.2] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Saddle-point characterisation of value.
