/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.StrategicGame.ZeroSum.MatrixGameNash
import EconCSLib.GameTheory.StrategicGame.ZeroSum.StochasticMatrix

/-!
# EconCSLib.Examples.StrategicGame.MatchingPennies

The canonical 2×2 zero-sum game:

```
      L    R
T   [ 1, -1]
B   [-1,  1]
```

Pure maxmin = −1, pure minmax = 1 ⇒ no pure value. Mixed value = 0,
attained by both players' uniform strategy `(1/2, 1/2)`.

[MFoGT Chapter 2, Section 2.2]
-/

open EconCSLib.StrategicGame

namespace EconCSLib.StrategicGame.Examples

/-- The 2×2 Matching Pennies payoff matrix:
`matchingPennies.g i j = 1` if `i = j`, `-1` otherwise. -/
def matchingPennies : MatrixGame (Fin 2) (Fin 2) ℝ where
  g i j := if i = j then 1 else -1

@[simp] theorem matchingPennies_g (i j : Fin 2) :
    matchingPennies.g i j = if i = j then 1 else -1 := rfl

/-- Both players' uniform mixed strategy `(1/2, 1/2)` on `Fin 2`. -/
noncomputable abbrev matchingPenniesUniform : stdSimplex ℝ (Fin 2) :=
  EconCSLib.StrategicGame.uniformDist

/-- Player 1 uniformly mixing guarantees a payoff of at least `0` against
every pure column. -/
theorem matchingPennies_uniform_row_guarantee (j : Fin 2) :
    0 ≤ matchingPennies.Ej matchingPenniesUniform j := by
  show (0 : ℝ) ≤ ∑ i, matchingPenniesUniform.val i * matchingPennies.g i j
  simp only [matchingPennies_g, Fin.sum_univ_two, uniformDist_val,
             Fintype.card_fin]
  fin_cases j <;> norm_num

/-- Player 2 uniformly mixing caps Player 1's payoff at `0` against every
pure row. -/
theorem matchingPennies_uniform_column_guarantee (i : Fin 2) :
    matchingPennies.Ei i matchingPenniesUniform ≤ 0 := by
  show ∑ j, matchingPenniesUniform.val j * matchingPennies.g i j ≤ (0 : ℝ)
  simp only [matchingPennies_g, Fin.sum_univ_two, uniformDist_val,
             Fintype.card_fin]
  fin_cases i <;> norm_num

/-- **Matching Pennies has mixed value `0`** [MFoGT §2.2]. -/
theorem matchingPennies_value : matchingPennies.value = 0 := by
  symm
  apply matchingPennies.common_guarantee_eq_value
  · exact ⟨matchingPenniesUniform, matchingPennies_uniform_row_guarantee⟩
  · exact ⟨matchingPenniesUniform, matchingPennies_uniform_column_guarantee⟩

/-- Player 1's uniform strategy is row-optimal. -/
theorem matchingPennies_uniform_row_optimal :
    matchingPenniesUniform ∈ matchingPennies.optimalRowStrategies := by
  rw [matchingPennies.mem_optimalRowStrategies_iff_E_ge]
  intro y'
  show matchingPennies.value ≤ matchingPennies.E matchingPenniesUniform y'
  rw [matchingPennies_value]
  have heq : matchingPennies.E matchingPenniesUniform y' =
      wsum y' (fun j => matchingPennies.Ej matchingPenniesUniform j) := by
    show wsum matchingPenniesUniform (fun i => wsum y' (matchingPennies.g i))
        = wsum y' (fun j => wsum matchingPenniesUniform (fun i => matchingPennies.g i j))
    exact wsum_wsum_comm matchingPenniesUniform y' matchingPennies.g
  rw [heq]
  calc (0 : ℝ) = wsum y' (fun _ => 0) := (wsum_const y' 0).symm
    _ ≤ wsum y' (fun j => matchingPennies.Ej matchingPenniesUniform j) :=
        wsum_le_wsum y' matchingPennies_uniform_row_guarantee

/-- Player 2's uniform strategy is column-optimal. -/
theorem matchingPennies_uniform_column_optimal :
    matchingPenniesUniform ∈ matchingPennies.optimalColumnStrategies := by
  rw [matchingPennies.mem_optimalColumnStrategies_iff_E_le]
  intro x'
  show matchingPennies.E x' matchingPenniesUniform ≤ matchingPennies.value
  rw [matchingPennies_value]
  have heq : matchingPennies.E x' matchingPenniesUniform =
      wsum x' (fun i => matchingPennies.Ei i matchingPenniesUniform) := rfl
  rw [heq]
  calc wsum x' (fun i => matchingPennies.Ei i matchingPenniesUniform)
      ≤ wsum x' (fun _ => 0) := wsum_le_wsum x' matchingPennies_uniform_column_guarantee
    _ = 0 := wsum_const x' 0

end EconCSLib.StrategicGame.Examples
