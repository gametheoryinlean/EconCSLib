/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Lattice.Lemmas
import Mathlib.Algebra.Group.Defs

/-!
# EconCSLib.Foundation.CostM.Visited

The "memoization-shaped" cost monoid for `CostM`: an `AddMonoid` whose
elements are finite sets of sub-problem indices, with `+ := (· ∪ ·)` and
`0 := ∅`.

The defining feature is **idempotence** (`s + s = s`): repeated visits to
the same sub-problem do not enlarge the recorded cost. This is the
algebraic shadow of memoization — when the cost type is `Visited A`, the
recorded cost is the *distinct* set of sub-problems touched, regardless of
whether the algorithm actually memoizes.

## Type synonym, not direct instance

`Visited A` is a type synonym for `Finset A`. We do **not** give the
union-monoid as a direct instance on `Finset A` because Mathlib's
`Mathlib.Algebra.Group.Pointwise.Finset.Basic` already provides a scoped
`Zero (Finset A) := ⟨{0}⟩` (the *singleton* of the underlying zero, not
`∅`). The two interpretations are incompatible, so we firewall instance
resolution behind a fresh type name. Cf. Mathlib's `Additive` /
`Multiplicative` / `OrderDual`.

## Use site

```
import EconCSLib.Foundation.CostM
import EconCSLib.Foundation.CostM.Visited

def alg : ℕ → CostM (Visited ℕ) Result := …
```

Tick `Visited.singleton i` whenever sub-problem `i` is touched; the
recorded cost will be exactly the set of indices reached. See
`Examples/CostM/MemoFib.lean` for a worked example.
-/

/-- Cost type tracking the **set** of sub-problem indices an algorithm
touches, with `(∪, ∅)` as its `(+, 0)` monoid.

Type synonym for `Finset A`; the type synonym blocks Mathlib's scoped
pointwise instances on `Finset A` from leaking into `CostM` cost
arithmetic. -/
def Visited (A : Type*) : Type _ := Finset A

namespace Visited

variable {A : Type*}

/-- View a `Visited A` as the underlying `Finset A`. -/
def toFinset (v : Visited A) : Finset A := v

/-- View a `Finset A` as a `Visited A`. -/
def ofFinset (s : Finset A) : Visited A := s

@[ext] theorem ext {a b : Visited A} (h : a.toFinset = b.toFinset) : a = b := h

@[simp] theorem toFinset_ofFinset (s : Finset A) :
    (ofFinset s).toFinset = s := rfl

instance : Zero (Visited A) := ⟨(∅ : Finset A)⟩

@[simp] theorem toFinset_zero : (0 : Visited A).toFinset = ∅ := rfl

/-- Mark a single sub-problem `a` as visited. -/
def singleton (a : A) : Visited A := ({a} : Finset A)

@[simp] theorem toFinset_singleton (a : A) :
    (singleton a).toFinset = {a} := rfl

variable [DecidableEq A]

instance : Add (Visited A) :=
  ⟨fun a b => (ofFinset (a.toFinset ∪ b.toFinset))⟩

@[simp] theorem toFinset_add (a b : Visited A) :
    (a + b).toFinset = a.toFinset ∪ b.toFinset := rfl

instance : AddMonoid (Visited A) where
  add_assoc a b c := by ext; simp [Finset.union_assoc]
  zero_add a := by ext; simp
  add_zero a := by ext; simp
  nsmul := nsmulRec

end Visited
