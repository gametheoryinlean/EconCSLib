---
id: math.simplex.mix
title: Convex Combination of Simplex Points
kind: definition
status: formalized
primary_topic: math
topics:
  - math
  - math.simplex
uses:
  - math.simplex.wsum
lean:
  modules:
    - EconCSLib.Math.Simplex
  declarations:
    - stdSimplex.mix
    - stdSimplex.mix_apply
    - wsum_mix
    - linear_comb_gt_left
    - linear_comb_gt_right
    - linear_comb_gt_of_ge_gt
    - linear_comb_lt_of_le_lt
    - wsum_mix_gt_of_ge_gt
    - wsum_mix_lt_of_le_lt
    - mix_gt_of_gt_nbh
    - mix_lt_of_lt_nbh
source:
  spans:
    - artifact: msz-game-theory
      locator: "Axiom 2.16 (compound lottery simplification)"
      format: section
      note: "Canonical reference, even though the construct is used far beyond utility theory."
verification:
  definition: accepted
  proof: accepted
  alignment: aligned
tags:
  - core
  - simplex
  - convex-combination
  - mixed-strategy
---

# Convex Combination of Simplex Points

The basic vocabulary for blending two mixed strategies. Given
$x, y \in \Delta(I)$ and $\alpha \in [0, 1]$, the *mixed* point

$$
  \mathrm{mix}(\alpha; x, y) \;=\; \alpha \cdot x + (1 - \alpha) \cdot y
$$

is again a simplex point. This is the substrate for compound lotteries (MSZ
Axiom 2.16), the inductive perturbation step in Loomis-style minimax proofs,
and any algorithm that interpolates between two distributions (fictitious
play, no-regret dynamics, Sion-style continuity arguments).

## Statement

For a finite index `I`, a strictly ordered field `𝕜`, and `α ∈ [0, 1]`:

- `stdSimplex.mix α hα₀ hα₁ x y` is the element of `stdSimplex 𝕜 I` whose
  `i`-th coordinate is $\alpha \cdot x_i + (1 - \alpha) \cdot y_i$.
- **Bilinearity of `wsum`** (`wsum_mix`): for any `f : I → 𝕜`,
  $$
    \operatorname{wsum}(\mathrm{mix}(\alpha; x, y), f)
    \;=\; \alpha \cdot \operatorname{wsum}(x, f)
        + (1 - \alpha) \cdot \operatorname{wsum}(y, f).
  $$
- **Strict-monotonicity over a convex combination** (`linear_comb_gt_of_ge_gt`,
  `linear_comb_lt_of_le_lt`, and their `wsum` versions `wsum_mix_gt_of_ge_gt`
  and `wsum_mix_lt_of_le_lt`): if one endpoint of the combination satisfies
  a non-strict bound and the other a strict bound, the combination remains
  strict for any `α < 1`.
- **Neighborhood-of-1 existential** (`mix_gt_of_gt_nbh` and dual
  `mix_lt_of_lt_nbh`): if `c < x`, there is an interior `t ∈ (0, 1)` with
  `c < t · x + (1 - t) · y`. The proof appeals to continuity of
  $s \mapsto s \cdot x + (1 - s) \cdot y$ at $s = 1$.

## Hypothesis convention

Hypotheses for `α` are passed as plain `(α : 𝕜) (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1)`
rather than via a unit-interval subtype, matching Mathlib idioms and avoiding
a Core-level subtype declaration that would not pay for itself. The legacy
`Interval := { t : ℝ // 0 ≤ t ∧ t ≤ 1 }` subtype, previously defined in
`StrategicGame/MinimaxLoomis.lean`, has been retired in favor of this
convention.

## Use

- `EconCSLib.Utility.Lottery`: `Lottery.mix` is a definitional alias of
  `stdSimplex.mix`; `Lottery.expectedValue_mix` is a one-line wrapper around
  `wsum_mix`.
- `EconCSLib.StrategicGame.MinimaxLoomis` (simplified Loomis induction) and
  `EconCSLib.StrategicGame.Loomis` (general-`B` Loomis): the
  inductive step "blend the existing optimiser with the optimiser of the
  smaller restricted game" is the canonical consumer of `stdSimplex.mix`,
  `wsum_mix`, `wsum_mix_*_of_*`, and `mix_*_nbh`.

## References

- [MSZ] Maschler, Solan, Zamir, *Game Theory*, Axiom 2.16 and the surrounding
  discussion of compound lotteries.
- [MFoGT] Laraki, Renault, Sorin, *Mathematical Foundations of Game Theory*,
  Section 2.5 (Loomis induction).
