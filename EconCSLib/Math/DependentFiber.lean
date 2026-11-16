/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Logic.Equiv.Basic

/-!
# Dependent-fiber equivalences

Game-independent cast-stable equivalences between dependent fibers.

This module deliberately depends only on Mathlib.  Game-theory morphism and
refinement layers reuse it without forcing neutral dependent type calculus to
depend on any extensive-game relation hierarchy.
-/

namespace Equiv

variable {α β : Type*}
variable {W : α → Type*} {Z : β → Type*}

/-- Transport a dependent fiber equivalence to a propositionally equal target
index. -/
def fiberEquivAt
    (base : α ≃ β)
    (fiber : ∀ source, W source ≃ Z (base source))
    (source : α) (target : β)
    (hindex : base source = target) :
    W source ≃ Z target :=
  (fiber source).trans
    (Equiv.cast (congrArg Z hindex))

@[simp]
theorem fiberEquivAt_apply
    (base : α ≃ β)
    (fiber : ∀ source, W source ≃ Z (base source))
    (source : α) (target : β)
    (hindex : base source = target)
    (value : W source) :
    fiberEquivAt base fiber source target hindex value =
      cast (congrArg Z hindex) (fiber source value) :=
  rfl

/-- Applying dependent fiber transport is stable under composition of the
base and fiber equivalences. -/
theorem fiberEquivAt_trans_apply
    {γ : Type*}
    {V : γ → Type*}
    (baseFirst : α ≃ β)
    (baseSecond : β ≃ γ)
    (fiberFirst :
      ∀ source, W source ≃ Z (baseFirst source))
    (fiberSecond :
      ∀ middle, Z middle ≃ V (baseSecond middle))
    (source : α) (middle : β) (target : γ)
    (hFirst : baseFirst source = middle)
    (hSecond : baseSecond middle = target)
    (value : W source) :
    fiberEquivAt
        (baseFirst.trans baseSecond)
        (fun index =>
          (fiberFirst index).trans
            (fiberSecond (baseFirst index)))
        source target
        ((congrArg baseSecond hFirst).trans hSecond)
        value =
      fiberEquivAt baseSecond fiberSecond middle target hSecond
        (fiberEquivAt baseFirst fiberFirst source middle hFirst value) := by
  subst middle
  subst target
  rfl

/-- Transport a dependent fiber equivalence along a forgetful base map. -/
def fiberEquivOverAt
    (forget : β → α)
    (fiber : ∀ target, W (forget target) ≃ Z target)
    (source : α) (target : β)
    (hindex : source = forget target) :
    W source ≃ Z target :=
  (Equiv.cast (congrArg W hindex)).trans
    (fiber target)

@[simp]
theorem fiberEquivOverAt_apply
    (forget : β → α)
    (fiber : ∀ target, W (forget target) ≃ Z target)
    (source : α) (target : β)
    (hindex : source = forget target)
    (value : W source) :
    fiberEquivOverAt forget fiber source target hindex value =
      fiber target
        (cast (congrArg W hindex) value) :=
  rfl

/-- Applying forgetful dependent fiber transport is stable under composition
of refinements. -/
theorem fiberEquivOverAt_trans_apply
    {γ : Type*}
    {V : γ → Type*}
    (forgetFirst : β → α)
    (forgetSecond : γ → β)
    (fiberFirst :
      ∀ middle, W (forgetFirst middle) ≃ Z middle)
    (fiberSecond :
      ∀ target, Z (forgetSecond target) ≃ V target)
    (source : α) (middle : β) (target : γ)
    (hFirst : source = forgetFirst middle)
    (hSecond : middle = forgetSecond target)
    (value : W source) :
    fiberEquivOverAt
        (forgetFirst ∘ forgetSecond)
        (fun index =>
          (fiberFirst (forgetSecond index)).trans
            (fiberSecond index))
        source target
        (hFirst.trans (congrArg forgetFirst hSecond))
        value =
      fiberEquivOverAt forgetSecond fiberSecond middle target hSecond
        (fiberEquivOverAt forgetFirst fiberFirst
          source middle hFirst value) := by
  subst middle
  subst source
  rfl

/-- Evaluation of `Equiv.piCongr` at an index propositionally equal to the
image of a source index. -/
theorem piCongr_apply_of_eq
    (base : α ≃ β)
    (fiber : ∀ index, W index ≃ Z (base index))
    (function : ∀ index, W index)
    (source : α) (target : β)
    (hindex : base source = target) :
    base.piCongr fiber function target =
      cast (congrArg Z hindex) (fiber source (function source)) := by
  subst target
  simp

end Equiv

/-- Evaluating a dependent function after changing its index agrees with
transporting the value at the original index. -/
theorem dependent_apply_eq_cast
    {α : Type*} {fiber : α → Type*}
    (function : (index : α) → fiber index)
    {source target : α}
    (hindex : source = target) :
    function target =
      cast (congrArg fiber hindex) (function source) := by
  subst target
  rfl
