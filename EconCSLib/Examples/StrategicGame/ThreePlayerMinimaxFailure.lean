/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Polyrith
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# EconCSLib.Examples.StrategicGame.ThreePlayerMinimaxFailure

[MFoGT §2.8, Exercise 2]: a 3-player zero-sum example where the maximin /
minimax equality fails because the two maximisers are constrained to
play **independent** mixed actions.

Setup: players 1 and 2 each choose `T`/`B` resp. `L`/`R` (binary actions),
player 3 chooses `W` or `E`. Pure payoffs to the maximising side are
`g(T,L,W) = 1`, `g(B,R,E) = 1`, all others `0`.

Writing `x = P(T)`, `y = P(L)`, `z = P(W)`, the expected payoff is

$$
  G(x, y, z) = z \cdot xy + (1-z) \cdot (1-x)(1-y).
$$

We prove:

* `maximin = max_{x,y ∈ [0,1]} min_{z ∈ [0,1]} G(x,y,z) = 1/4`
  (attained at `x = y = 1/2`).
* `minimax = min_{z ∈ [0,1]} max_{x,y ∈ [0,1]} G(x,y,z) = 1/2`
  (attained at `z = 1/2`).

Hence `maximin = 1/4 < 1/2 = minimax`. If players 1 and 2 could correlate,
the maximin would rise to `1/2` (matching the minimax) — independent
mixing is what breaks the equality.
-/

namespace EconCSLib.StrategicGame.Examples.ThreePlayerMinimaxFailure

/-- Expected payoff `G(x, y, z) = z · xy + (1 − z) · (1 − x)(1 − y)`. -/
def G (x y z : ℝ) : ℝ := z * (x * y) + (1 - z) * ((1 - x) * (1 - y))

/-- Payoff against pure `W` (`z = 0`): `(1 − x)(1 − y)`. -/
theorem G_pure_E (x y : ℝ) : G x y 0 = (1 - x) * (1 - y) := by
  simp [G]

/-- Payoff against pure `W` (`z = 1`): `xy`. -/
theorem G_pure_W (x y : ℝ) : G x y 1 = x * y := by
  simp [G]

/-- For each `(x, y) ∈ [0,1]²`, the minimiser's best response is at
`z = 0` or `z = 1`, giving `min { xy, (1−x)(1−y) }`. -/
theorem min_over_z (x y : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    ∀ z, 0 ≤ z → z ≤ 1 → min (x * y) ((1 - x) * (1 - y)) ≤ G x y z := by
  intro z hz0 hz1
  have hmin_xy : min (x * y) ((1 - x) * (1 - y)) ≤ x * y := min_le_left _ _
  have hmin_other : min (x * y) ((1 - x) * (1 - y)) ≤ (1 - x) * (1 - y) := min_le_right _ _
  have h1z : 0 ≤ 1 - z := by linarith
  have key : z * min (x * y) ((1 - x) * (1 - y)) + (1 - z) * min (x * y) ((1 - x) * (1 - y))
      ≤ z * (x * y) + (1 - z) * ((1 - x) * (1 - y)) := by
    apply add_le_add
    · exact mul_le_mul_of_nonneg_left hmin_xy hz0
    · exact mul_le_mul_of_nonneg_left hmin_other h1z
  have hconv : z * min (x * y) ((1 - x) * (1 - y))
              + (1 - z) * min (x * y) ((1 - x) * (1 - y))
            = min (x * y) ((1 - x) * (1 - y)) := by ring
  show min (x * y) ((1 - x) * (1 - y)) ≤ G x y z
  unfold G
  linarith [key, hconv]

/-- At `x = y = 1/2`: both `xy` and `(1−x)(1−y)` equal `1/4`, so `min = 1/4`. -/
theorem min_at_half : min ((1/2 : ℝ) * (1/2)) ((1 - 1/2) * (1 - 1/2)) = 1/4 := by
  norm_num

/-- **Maximin lower bound**: at `x = y = 1/2`, the minimiser can do no
better than `1/4`. -/
theorem maximin_lower_bound :
    ∀ z, 0 ≤ z → z ≤ 1 → (1 / 4 : ℝ) ≤ G (1/2) (1/2) z := by
  intro z hz0 hz1
  have := min_over_z (1/2) (1/2) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hz0 hz1
  rw [min_at_half] at this
  exact this

/-- **Maximin upper bound**: for any `(x, y) ∈ [0,1]²`, the minimiser
can force payoff `≤ min{xy, (1−x)(1−y)} ≤ 1/4` (using AM-GM-style:
`xy · (1-x)(1-y) ≤ 1/16`, so `min ≤ 1/4`). -/
theorem maximin_upper_bound (x y : ℝ)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    min (x * y) ((1 - x) * (1 - y)) ≤ (1 / 4 : ℝ) := by
  -- Key inequality: at least one of x*y and (1-x)(1-y) is ≤ 1/4.
  -- Specifically: x(1-x) ≤ 1/4 (AM-GM/quadratic max), so x*y*(1-x)*(1-y) ≤ 1/16.
  -- Then min ≤ sqrt(product) ≤ 1/4.
  -- Direct argument: if x ≤ 1/2 then 1-x ≥ 1/2; combined with cases on y...
  -- Cleaner: 2 * min(a, b) ≤ a + b, so min ≤ (xy + (1-x)(1-y))/2.
  -- And xy + (1-x)(1-y) = 1 - x - y + 2xy ≤ 1/2 at the worst.
  -- Actually let's bound directly: min(xy, (1-x)(1-y)) ≤ sqrt(xy · (1-x)(1-y))
  -- and x(1-x) ≤ 1/4, y(1-y) ≤ 1/4, so the product ≤ 1/16, sqrt ≤ 1/4.
  -- Use 2 * min ≤ a + b: min(a, b) ≤ a, min ≤ b, so 2min ≤ a + b ⇒ min ≤ (a+b)/2.
  -- But (xy + (1-x)(1-y)) can exceed 1/2 (e.g., x=y=0 gives 0+1 = 1). So this doesn't suffice.
  -- Use: min(a, b)² ≤ ab. With ab = xy(1-x)(1-y) ≤ (1/4)² = 1/16, get min ≤ 1/4.
  have hx_sq : x * (1 - x) ≤ 1 / 4 := by nlinarith [sq_nonneg (1 - 2*x)]
  have hy_sq : y * (1 - y) ≤ 1 / 4 := by nlinarith [sq_nonneg (1 - 2*y)]
  have hx_nn : 0 ≤ x * (1 - x) := mul_nonneg hx0 (by linarith)
  have hy_nn : 0 ≤ y * (1 - y) := mul_nonneg hy0 (by linarith)
  have hprod : x * y * ((1 - x) * (1 - y)) ≤ 1 / 16 := by
    have : x * y * ((1 - x) * (1 - y)) = (x * (1 - x)) * (y * (1 - y)) := by ring
    rw [this]
    nlinarith [hx_sq, hy_sq, hx_nn, hy_nn]
  -- min(a, b)² ≤ ab when a, b ≥ 0.
  have ha_nn : 0 ≤ x * y := mul_nonneg hx0 hy0
  have hb_nn : 0 ≤ (1 - x) * (1 - y) := mul_nonneg (by linarith) (by linarith)
  have hmin_nn : 0 ≤ min (x * y) ((1 - x) * (1 - y)) := le_min ha_nn hb_nn
  have hmin_sq : (min (x * y) ((1 - x) * (1 - y))) ^ 2 ≤ 1 / 16 := by
    calc (min (x * y) ((1 - x) * (1 - y))) ^ 2
        = min (x * y) ((1 - x) * (1 - y)) * min (x * y) ((1 - x) * (1 - y)) := sq _
      _ ≤ (x * y) * ((1 - x) * (1 - y)) := by
          apply mul_le_mul (min_le_left _ _) (min_le_right _ _) hmin_nn ha_nn
      _ ≤ 1 / 16 := hprod
  -- min ≤ sqrt(1/16) = 1/4.
  have : min (x * y) ((1 - x) * (1 - y)) ≤ 1 / 4 := by
    by_contra h; push_neg at h
    have : (1 / 4 : ℝ) ^ 2 < (min (x * y) ((1 - x) * (1 - y))) ^ 2 := by
      have := sq_lt_sq' (by linarith) h
      simpa using this
    have hsq : (1 / 4 : ℝ) ^ 2 = 1 / 16 := by norm_num
    linarith [hmin_sq, hsq.symm ▸ this]
  exact this

/-- **Maximin equality**: `max_{x,y ∈ [0,1]} min_{z ∈ [0,1]} G(x,y,z) = 1/4`,
attained at `x = y = 1/2`.

Phrased as a witnessed sup/inf: `(1/4 : ℝ)` is a sup of the "min-over-z"
values over `x, y ∈ [0,1]²`. -/
theorem maximin_eq_one_quarter :
    -- Witness x = y = 1/2 achieves at least 1/4 against every z.
    (∀ z, 0 ≤ z → z ≤ 1 → (1 / 4 : ℝ) ≤ G (1/2) (1/2) z)
    ∧
    -- Upper bound: every (x,y) ∈ [0,1]² has min_z G(x,y,z) ≤ 1/4.
    (∀ x y, 0 ≤ x → x ≤ 1 → 0 ≤ y → y ≤ 1 →
      min (x * y) ((1 - x) * (1 - y)) ≤ (1 / 4 : ℝ)) := by
  exact ⟨maximin_lower_bound, fun x y => maximin_upper_bound x y⟩

/-- For `z ∈ [0,1]`, the maximisers can force payoff ≥ `max{z, 1-z}` by
picking `x = y = 1` (gives `z`) or `x = y = 0` (gives `1 - z`). -/
theorem max_over_xy (z : ℝ) (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    max z (1 - z) ≤ max (G 1 1 z) (G 0 0 z) := by
  have h1 : G 1 1 z = z := by unfold G; ring
  have h2 : G 0 0 z = 1 - z := by unfold G; ring
  rw [h1, h2]

/-- **Minimax upper bound**: at `z = 1/2`, max payoff is `1/2`. -/
theorem minimax_upper_bound (x y : ℝ)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    G x y (1/2) ≤ (1 / 2 : ℝ) := by
  -- G(x, y, 1/2) = (1/2)(xy + (1-x)(1-y)) = (1/2)(1 - x - y + 2xy).
  -- = 1/2 - (x + y)/2 + xy. We want this ≤ 1/2, i.e., xy ≤ (x+y)/2.
  -- xy ≤ (x+y)/2 iff 2xy ≤ x + y iff x + y - 2xy ≥ 0 iff x(1-y) + y(1-x) ≥ 0. ✓
  unfold G
  nlinarith [mul_nonneg hx0 (sub_nonneg.mpr hy1),
             mul_nonneg hy0 (sub_nonneg.mpr hx1),
             mul_nonneg (sub_nonneg.mpr hx1) (sub_nonneg.mpr hy1)]

/-- **Minimax lower bound**: for any `z ∈ [0,1]`, the maximisers can
force payoff `≥ max{z, 1-z} ≥ 1/2`. -/
theorem minimax_lower_bound (z : ℝ) (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    (1 / 2 : ℝ) ≤ max (G 1 1 z) (G 0 0 z) := by
  have hmax_ge : (1 / 2 : ℝ) ≤ max z (1 - z) := by
    by_cases h : z ≤ 1/2
    · exact le_max_of_le_right (by linarith)
    · push_neg at h; exact le_max_of_le_left (by linarith)
  exact le_trans hmax_ge (max_over_xy z hz0 hz1)

/-- **Minimax equality**: `min_{z ∈ [0,1]} max_{x,y} G(x,y,z) = 1/2`. -/
theorem minimax_eq_one_half :
    -- Witness z = 1/2 caps every (x,y) at 1/2.
    (∀ x y, 0 ≤ x → x ≤ 1 → 0 ≤ y → y ≤ 1 → G x y (1/2) ≤ (1 / 2 : ℝ))
    ∧
    -- Lower bound: every z ∈ [0,1] has max_{x,y} G(x,y,z) ≥ 1/2.
    (∀ z, 0 ≤ z → z ≤ 1 → (1 / 2 : ℝ) ≤ max (G 1 1 z) (G 0 0 z)) := by
  exact ⟨minimax_upper_bound, minimax_lower_bound⟩

/-- **The minimax inequality is strict**: `1/4 < 1/2`. -/
theorem maximin_lt_minimax : (1 / 4 : ℝ) < 1 / 2 := by norm_num

end EconCSLib.StrategicGame.Examples.ThreePlayerMinimaxFailure
