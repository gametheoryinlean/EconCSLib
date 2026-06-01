/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Basic

/-!
# EconCSLib.Foundation.Preference

Abstract interfaces for agent preferences, shared across the library.

Mathlib already provides `Preorder` (reflexive + transitive) and
`LinearOrder` (total + antisymmetric + decidable). This file adds
domain-specific vocabulary on top, without fixing a specific representation.

The library uses two complementary interfaces:

* ambient order instances such as `[TotalPreorder A]` when a type carries one
  relevant preference order, for example a payoff type;
* bundled preferences `Pref A` when several agents may rank the same outcome
  type differently.

## Design

- **Weak preference** `a ≿ b` = Mathlib's `a ≤ b` on a `Preorder`
- **Strict preference** `a ≻ b` = Mathlib's `a < b` = `a ≤ b ∧ ¬(b ≤ a)`
- **Indifference** `a ∼ b` = `a ≤ b ∧ b ≤ a` (need not imply `a = b` without antisymmetry)
- For social choice (ordinal strict preferences): use `LinearOrder`
- For utility theory (allowing indifference): use `Preorder` + `IsTotal`

## Main definitions

* `Indifferent` — `a ∼ b` iff `a ≤ b ∧ b ≤ a`
* `StrictlyPreferred` — `a ≻ b` iff `a < b` (alias for readability)
* `TotalPreorder` — a preorder where `≤` is total (no antisymmetry required)
* `Pref` — a bundled total preorder, for agent-indexed preferences
* `RepresentsPreference` — utility function `u` represents preference `≤`

## References

* [MSZ] Maschler, Solan, Zamir, *Game Theory*, Chapter 2, Definitions 2.1–2.7
-/

/-! ### Relation-level vocabulary -/

/-- Strict preference derived from a weak preference relation. -/
def strict {A : Type*} (R : A → A → Prop) (a b : A) : Prop :=
  R a b ∧ ¬ R b a

/-- Indifference derived from a weak preference relation. -/
def indiff {A : Type*} (R : A → A → Prop) (a b : A) : Prop :=
  R a b ∧ R b a

/-- Derived strict preference is transitive when the weak relation is transitive. -/
theorem strict_transitive {A : Type*} {R : A → A → Prop}
    (h : Transitive R) : Transitive (strict R) := by
  intro x y z hxy hyz
  constructor
  · exact h hxy.1 hyz.1
  · intro hzx
    exact hxy.2 (h hyz.1 hzx)

/-! ### Indifference and strict preference -/

section PreferenceVocabulary

variable {A : Type*} [Preorder A]

/-- Two outcomes are indifferent under a preorder: `a ≤ b ∧ b ≤ a`.
    In a `PartialOrder` this implies `a = b`; in a general `Preorder` it does not.
    [MSZ 2.5] -/
def Indifferent (a b : A) : Prop := a ≤ b ∧ b ≤ a

/-- Indifference is reflexive. -/
theorem Indifferent.refl (a : A) : Indifferent a a := ⟨le_refl a, le_refl a⟩

/-- Indifference is symmetric. -/
theorem Indifferent.symm {a b : A} (h : Indifferent a b) : Indifferent b a := ⟨h.2, h.1⟩

/-- Indifference is transitive. -/
theorem Indifferent.trans {a b c : A} (h₁ : Indifferent a b) (h₂ : Indifferent b c) :
    Indifferent a c :=
  ⟨le_trans h₁.1 h₂.1, le_trans h₂.2 h₁.2⟩

/-- Strict preference is just `<` from the preorder. [MSZ 2.5] -/
abbrev StrictlyPreferred (a b : A) : Prop := a < b

/-- Strict preference is asymmetric: `a ≻ b → ¬(b ≻ a)`. [MSZ Ex 2.1(a)] -/
theorem StrictlyPreferred.asymm {a b : A} (h : StrictlyPreferred a b) :
    ¬ StrictlyPreferred b a :=
  lt_asymm h

/-- Strict preference is transitive. [MSZ Ex 2.1(a)] -/
theorem StrictlyPreferred.trans {a b c : A}
    (h₁ : StrictlyPreferred a b) (h₂ : StrictlyPreferred b c) :
    StrictlyPreferred a c :=
  lt_trans h₁ h₂

/-- Strict preference is irreflexive. [MSZ Ex 2.1(a)] -/
theorem StrictlyPreferred.irrefl (a : A) : ¬ StrictlyPreferred a a :=
  lt_irrefl a

end PreferenceVocabulary

/-! ### Total preorder -/

/-- A total preorder: a preorder where `≤` is total (complete).
    This is weaker than `LinearOrder` — it does NOT require antisymmetry
    or decidable equality. Two distinct elements can be indifferent.

    This is the appropriate notion for weak preferences in utility theory
    and matching theory. [MSZ 2.1–2.4] -/
class TotalPreorder (A : Type*) extends Preorder A where
  /-- The preference relation is complete: for any `a b`, either `a ≤ b` or `b ≤ a`. -/
  le_total : ∀ (a b : A), a ≤ b ∨ b ≤ a

/-- In a total preorder, any two elements are comparable. -/
theorem TotalPreorder.comparable [TotalPreorder A] (a b : A) :
    a ≤ b ∨ b ≤ a :=
  TotalPreorder.le_total a b

/-- Every `LinearOrder` is a `TotalPreorder`. -/
instance (priority := 100) LinearOrder.toTotalPreorder [LinearOrder A] : TotalPreorder A where
  le_total := LinearOrder.le_total

/-! ### Bundled preferences -/

/-- A weak preference relation is admissible if it is reflexive, transitive,
    and total. -/
class IsPreference {A : Type*} (R : A → A → Prop) : Prop where
  reflexive : Reflexive R
  transitive : Transitive R
  total : ∀ a b : A, R a b ∨ R b a

/-- A bundled weak preference relation.

    Use this interface when several agents may rank the same outcome type
    differently. Use `[TotalPreorder A]` when the outcome type carries one
    relevant ambient preference order. -/
structure Pref (A : Type*) where
  rel : A → A → Prop
  prop : IsPreference rel

instance : CoeFun (Pref A) (fun _ => A → A → Prop) where
  coe p := p.rel

namespace Pref

/-- `p.lt a b`: outcome `a` is strictly preferred to `b` under preference `p`. -/
def lt {A : Type*} (p : Pref A) (a b : A) : Prop :=
  strict p a b

/-- `p.indiff a b`: outcomes `a` and `b` are indifferent under preference `p`. -/
def indifferent {A : Type*} (p : Pref A) (a b : A) : Prop :=
  indiff p a b

/-- Bundle an explicit total preorder as a preference. -/
def ofTotalPreorder {A : Type*} (r : TotalPreorder A) : Pref A where
  rel := fun a b => @LE.le A r.toPreorder.toLE a b
  prop :=
    { reflexive := fun a => r.le_refl a
      transitive := fun _ _ _ => r.le_trans _ _ _
      total := fun a b => r.le_total a b }

/-- Bundle an explicit linear order as a preference. -/
def ofLinearOrder {A : Type*} (r : LinearOrder A) : Pref A where
  rel := fun a b => @LE.le A r.toLE a b
  prop :=
    { reflexive := fun a => r.le_refl a
      transitive := fun _ _ _ => r.le_trans _ _ _
      total := fun a b => r.le_total a b }

end Pref

/-- A preference profile assigns each agent a bundled preference. -/
def PrefProfile (N A : Type*) := N → Pref A

/-! ### Utility representation -/

/-- A utility function `u : A → V` represents the preference `≤` on `A`
    if `a ≤ b ↔ u a ≤ u b`. [MSZ 2.7] -/
structure RepresentsPreference [Preorder A] [Preorder V] (u : A → V) : Prop where
  /-- The representation property: `a ≤ b ↔ u(a) ≤ u(b)`. -/
  le_iff : ∀ a b : A, a ≤ b ↔ u a ≤ u b

/-- A utility representation preserves strict preference. -/
theorem RepresentsPreference.lt_iff [Preorder A] [Preorder V] {u : A → V}
    (h : RepresentsPreference u) (a b : A) :
    a < b ↔ u a < u b := by
  rw [Preorder.lt_iff_le_not_ge, Preorder.lt_iff_le_not_ge, h.le_iff, h.le_iff]

/-- A utility representation preserves indifference. -/
theorem RepresentsPreference.indifferent_iff [Preorder A] [Preorder V] {u : A → V}
    (h : RepresentsPreference u) (a b : A) :
    Indifferent a b ↔ Indifferent (u a) (u b) :=
  ⟨fun ⟨h1, h2⟩ => ⟨(h.le_iff a b).mp h1, (h.le_iff b a).mp h2⟩,
   fun ⟨h1, h2⟩ => ⟨(h.le_iff a b).mpr h1, (h.le_iff b a).mpr h2⟩⟩

/-! ### Preference relation axioms (vNM)

General axioms for preference relations, stated for an arbitrary binary relation.
Lottery-specific axioms (Independence, Continuity) are in `Utility.VNMAxioms`. -/

namespace VNM

variable {A : Type*}

/-- **Completeness**: every pair is comparable. -/
def Completeness (pref : A → A → Prop) : Prop :=
  ∀ a b : A, pref a b ∨ pref b a

/-- **Transitivity**: preference chains compose. -/
def Transitivity (pref : A → A → Prop) : Prop :=
  ∀ a b c : A, pref a b → pref b c → pref a c

end VNM
