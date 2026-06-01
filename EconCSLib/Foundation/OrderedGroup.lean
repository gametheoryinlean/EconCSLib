/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith

/-!
# EconCSLib.Foundation.OrderedGroup

Convenience lemmas for linearly ordered additive commutative groups, the standard
utility/payoff type in game theory.

## Typeclass convention

Throughout EconCSLib, the payoff/utility type `U` uses the **unbundled** pattern
from modern Mathlib:

```
[AddCommGroup U] [LinearOrder U] [IsOrderedAddMonoid U]
```

This is the unbundled equivalent of the former `LinearOrderedAddCommGroup` (which
no longer exists as a standalone class). It provides:
- Subtraction and negation (`AddCommGroup`)
- Total ordering (`LinearOrder`)
- Order-addition compatibility: `a ≤ b → a + c ≤ b + c` (`IsOrderedAddMonoid`)

**No multiplication is needed** for most game theory results (Nash equilibrium,
dominance, Vickrey auction). Only specific results require more:
- Quasi-linear utility `v_i · x_i − p_i` needs `[Ring U]` + `[IsOrderedRing U]`
- Myerson's Lemma needs `ℝ` (interval integration)

Standard instances: `ℤ`, `ℚ`, `ℝ`, and any `LinearOrderedField`.

## Notation

We use `U` consistently for the payoff type throughout the library.

## Key Mathlib lemmas for game theory proofs

The following Mathlib lemmas are especially useful when working with payoffs
in an ordered additive group. They are **not** re-proved here (use the Mathlib
names directly), but listed for reference:

### Sign and comparison
- `sub_nonneg : 0 ≤ a - b ↔ b ≤ a`
- `sub_nonpos : a - b ≤ 0 ↔ a ≤ b`
- `sub_pos : 0 < a - b ↔ b < a`
- `sub_neg : a - b < 0 ↔ a < b`

### Monotonicity of subtraction
- `sub_le_sub_iff_left (a : U) : a - b ≤ a - c ↔ c ≤ b`
- `sub_le_sub_iff_right (c : U) : a - c ≤ b - c ↔ a ≤ b`
- `sub_lt_sub_iff_left (a : U) : a - b < a - c ↔ c < b`

### Shifting by positive/negative
- `sub_lt_self (a : U) (h : 0 < b) : a - b < a`
- `lt_add_of_pos_right (a : U) (h : 0 < b) : a < a + b`
- `add_lt_of_neg_right (a : U) (h : b < 0) : a + b < a`

### Cancellation
- `add_le_add_iff_left (a : U) : a + b ≤ a + c ↔ b ≤ c`
- `add_le_add_iff_right (c : U) : a + c ≤ b + c ↔ a ≤ b`

### Note on `linarith`

The `linarith` tactic does **not** work in abstract ordered additive groups —
it requires `LinearOrderedCommRing` or similar. In proofs over abstract `U`,
use the lemmas above directly, or use `abel` to normalize additive expressions
before applying order lemmas.

## Game-theory-specific lemmas
-/

variable {U : Type*} [AddCommGroup U] [LinearOrder U] [IsOrderedAddMonoid U]

/-- If paying less is better: `price₁ ≤ price₂ → value - price₂ ≤ value - price₁`.
  Useful for comparing utilities when the allocation is the same but payments differ. -/
theorem payoff_anti_payment {value price₁ price₂ : U} (h : price₁ ≤ price₂) :
    value - price₂ ≤ value - price₁ :=
  sub_le_sub_iff_left value |>.mpr h

/-- Winning is profitable iff the value exceeds the price. -/
theorem payoff_nonneg_iff {value price : U} :
    0 ≤ value - price ↔ price ≤ value :=
  sub_nonneg

/-- Winning is unprofitable iff the price exceeds the value. -/
theorem payoff_nonpos_iff {value price : U} :
    value - price ≤ 0 ↔ value ≤ price :=
  sub_nonpos

/-- Lowering the price by a positive amount strictly increases payoff. -/
theorem payoff_lt_of_price_lt {value price₁ price₂ : U} (h : price₁ < price₂) :
    value - price₂ < value - price₁ :=
  sub_lt_sub_iff_left value |>.mpr h

/-- In a zero-sum comparison: if `a + b ≤ a` then `b ≤ 0`. -/
theorem le_zero_of_add_le_self {a b : U} (h : a + b ≤ a) : b ≤ 0 := by
  have := (add_le_add_iff_left a).mp (by rwa [add_zero] : a + b ≤ a + 0)
  exact this

/-- In a zero-sum comparison: if `a ≤ a + b` then `0 ≤ b`. -/
theorem nonneg_of_self_le_add {a b : U} (h : a ≤ a + b) : 0 ≤ b := by
  have := (add_le_add_iff_left a).mp (by rwa [add_zero] : a + 0 ≤ a + b)
  exact this
