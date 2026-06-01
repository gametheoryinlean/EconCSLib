/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic.Linarith

-- The `delta_zero` simp argument in `add_zero`/`zero_add` is flagged as unused
-- by the linter but removing it makes `omega` fail; the unfolding of `(0 : Cells).delta`
-- to `0` is needed before the arithmetic step.
set_option linter.unusedSimpArgs false

/-!
# EconCSLib.Foundation.CostM.Cells

The "tropical-shaped" cost monoid for **peak**-style resource analysis.

A `Cells` value carries two integers, `peak` and `delta`, with invariants
`0 ≤ peak` and `delta ≤ peak`:

* `peak` — maximum occupancy reached during a computation, relative to
  the occupancy at the start of the computation.
* `delta` — net change in occupancy from start to end. Negative if the
  computation ends with fewer live cells than it started (`free` exceeds
  `alloc`).

Composition

```
(p₁, d₁) ⋆ (p₂, d₂) = (max p₁ (d₁ + p₂), d₁ + d₂)
```

encodes sequential semantics: the new peak is whichever was higher —
the first computation's peak, or the second computation's peak shifted
up by the first computation's net offset.

This is **not an additive monoid in the elementwise sense** — `+` does
not just add componentwise; the peak component composes "tropically"
via `max`. But the resulting structure still satisfies the `AddMonoid`
laws, which is all `CostM` requires.

## Primitives

* `alloc n := ⟨n, n, _, _⟩` — claim `n` cells; both peak and delta rise by `n`.
* `free n := ⟨0, -n, _, _⟩` — release `n` cells; peak unchanged, delta drops.

## Bound shape

For an algorithm

```
do alloc K; ⟨body with zero ticks⟩; free K; pure result
```

the resulting cost has `.peak = K`. When `K` is independent of input size
this gives an O(1) (constant-space) bound. The Boyer-Moore example in
`Examples/CostM/BoyerMoore.lean` demonstrates this shape with `K = 2`.
-/

/-- Tropical-style cost record: peak occupancy and net delta. -/
@[ext]
structure Cells where
  /-- Peak occupancy reached during the computation (≥ 0). -/
  peak  : ℤ
  /-- Net change in occupancy from start to end (≤ peak). -/
  delta : ℤ
  /-- Peak is non-negative. -/
  zero_le_peak  : 0 ≤ peak
  /-- Delta never exceeds peak. -/
  delta_le_peak : delta ≤ peak

namespace Cells

instance : Zero Cells := ⟨⟨0, 0, le_refl _, le_refl _⟩⟩

@[simp] theorem peak_zero  : (0 : Cells).peak  = 0 := rfl
@[simp] theorem delta_zero : (0 : Cells).delta = 0 := rfl

instance : Add Cells where
  add a b :=
    { peak  := max a.peak (a.delta + b.peak)
      delta := a.delta + b.delta
      zero_le_peak  := le_max_of_le_left a.zero_le_peak
      delta_le_peak := by
        have hb := b.delta_le_peak
        have : a.delta + b.delta ≤ a.delta + b.peak := by linarith
        exact this.trans (le_max_right _ _) }

@[simp] theorem peak_add (a b : Cells) :
    (a + b).peak = max a.peak (a.delta + b.peak) := rfl

@[simp] theorem delta_add (a b : Cells) :
    (a + b).delta = a.delta + b.delta := rfl

instance : AddMonoid Cells where
  add_assoc a b c := by
    ext
    · -- peak: max(max p₁ (d₁+p₂)) (d₁+d₂+p₃) = max p₁ (d₁ + max p₂ (d₂+p₃))
      simp only [peak_add, delta_add]
      omega
    · -- delta: associative addition
      simp only [delta_add]
      omega
  zero_add a := by
    ext
    · -- max 0 (0 + a.peak) = a.peak, using 0 ≤ a.peak
      have := a.zero_le_peak
      simp only [peak_add, peak_zero, delta_zero]
      omega
    · simp
  add_zero a := by
    ext
    · -- max a.peak (a.delta + 0) = a.peak, using a.delta ≤ a.peak
      have := a.delta_le_peak
      simp only [peak_add, peak_zero, delta_zero]
      omega
    · simp
  nsmul := nsmulRec

/-- Allocate `n` cells: peak and delta both rise by `n`. -/
def alloc (n : ℕ) : Cells where
  peak  := n
  delta := n
  zero_le_peak  := Int.natCast_nonneg _
  delta_le_peak := le_refl _

/-- Release `n` cells: peak unchanged, delta drops by `n`. -/
def free (n : ℕ) : Cells where
  peak  := 0
  delta := -n
  zero_le_peak  := le_refl _
  delta_le_peak := by
    have : (0 : ℤ) ≤ n := Int.natCast_nonneg _
    linarith

@[simp] theorem peak_alloc  (n : ℕ) : (alloc n).peak  = n := rfl
@[simp] theorem delta_alloc (n : ℕ) : (alloc n).delta = n := rfl
@[simp] theorem peak_free   (n : ℕ) : (free n).peak   = 0 := rfl
@[simp] theorem delta_free  (n : ℕ) : (free n).delta  = -n := rfl

end Cells
