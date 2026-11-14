/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.OpenProblem.New.Complexity.WordRAM.FiniteData
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Bitwise



section

/-!
# Unambiguous structural table codes

These laws validate the existing codec without changing its format or machine core.
Prefix uniqueness rules out interpreting one emitted table as different mathematical
data.
-/
namespace EconCSLib.OpenProblem.New.WordRAM.FiniteData

/-- Count the leading true bits and consume the terminating false bit. -/
def scanUnary : Code → Option (ℕ × Code)
  | [] => none
  | false :: tail => some (0, tail)
  | true :: tail => (scanUnary tail).map fun pair => (pair.1 + 1, pair.2)

theorem scanUnary_replicate (n : ℕ) (tail : Code) :
    scanUnary (List.replicate n true ++ false :: tail) = some (n, tail) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, scanUnary, ih]

theorem scanUnary_natCode_append (n : ℕ) (tail : Code) :
    scanUnary (natCode n ++ tail) =
      some (Nat.log2 (n + 1) + 1,
        List.ofFn (fun i : Fin (Nat.log2 (n + 1) + 1) => (n + 1).testBit i.val) ++ tail) := by
  simp only [natCode, List.append_assoc, List.cons_append,
    List.nil_append]
  exact scanUnary_replicate _ _

/-- Bits of equal finite length determine a bounded natural number. -/
theorem testBit_ofFn_injective (length : ℕ) {a b : ℕ}
    (ha : a < 2 ^ length) (hb : b < 2 ^ length)
    (heq : List.ofFn (fun i : Fin length => a.testBit i.val) =
      List.ofFn (fun i : Fin length => b.testBit i.val)) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < length
  · exact congrFun (List.ofFn_injective heq) ⟨i, hi⟩
  · have hpow := Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_of_not_gt hi)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le ha hpow),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hb hpow)]

/-- A natural-number header cannot borrow bits from its suffix. -/
theorem natCode_prefix_unique {a b : ℕ} {left right : Code}
    (h : natCode a ++ left = natCode b ++ right) : a = b ∧ left = right := by
  have header := congrArg scanUnary h
  simp only [scanUnary_natCode_append,
    Option.some.injEq, Prod.mk.injEq] at header
  obtain ⟨hlen, hbits⟩ := header
  have htake := congrArg (List.take (Nat.log2 (a + 1) + 1)) hbits
  have hdata : List.ofFn (fun i : Fin (Nat.log2 (a + 1) + 1) =>
      (a + 1).testBit i.val) =
      List.ofFn (fun i : Fin (Nat.log2 (a + 1) + 1) => (b + 1).testBit i.val) := by
    simpa [← hlen] using htake
  have ha : a + 1 < 2 ^ (Nat.log2 (a + 1) + 1) :=
    (Nat.log2_lt (by omega)).mp (by omega)
  have hb : b + 1 < 2 ^ (Nat.log2 (a + 1) + 1) := by
    rw [hlen]
    exact (Nat.log2_lt (by omega)).mp (by omega)
  have hab : a = b := Nat.add_right_cancel (testBit_ofFn_injective _ ha hb hdata)
  subst b
  exact ⟨rfl, List.append_inj_right h rfl⟩

theorem natCode_injective : Function.Injective natCode := by
  intro a b h
  exact (natCode_prefix_unique (left := []) (right := []) (by simpa using h)).1

/-- The sign and self-delimiting magnitude determine the integer and suffix. -/
theorem intCode_prefix_unique {a b : ℤ} {left right : Code}
    (h : intCode a ++ left = intCode b ++ right) : a = b ∧ left = right := by
  simp only [intCode, List.cons_append, List.cons.injEq] at h
  obtain ⟨hsign, htail⟩ := h
  obtain ⟨habs, hsuffix⟩ := natCode_prefix_unique htail
  refine ⟨?_, hsuffix⟩
  cases a <;> cases b <;> simp_all <;> omega

/-- Normalized numerator and denominator give an unambiguous rational code. -/
theorem ratCode_prefix_unique {a b : ℚ} {left right : Code}
    (h : ratCode a ++ left = ratCode b ++ right) : a = b ∧ left = right := by
  simp only [ratCode, List.append_assoc] at h
  obtain ⟨hnum, htail⟩ := intCode_prefix_unique h
  obtain ⟨hden, hsuffix⟩ := natCode_prefix_unique htail
  exact ⟨Rat.ext hnum hden, hsuffix⟩

/-- Cell tags separate integers, rationals and Booleans. -/
theorem Atom.code_prefix_unique {a b : Atom} {left right : Code}
    (h : a.code ++ left = b.code ++ right) : a = b ∧ left = right := by
  cases a with
  | integer a =>
      cases b with
      | integer b =>
          have hp := intCode_prefix_unique (by simpa [Atom.code] using h)
          exact ⟨congrArg Atom.integer hp.1, hp.2⟩
      | rational b => simp [Atom.code] at h
      | bit b => simp [Atom.code] at h
  | rational a =>
      cases b with
      | integer b => simp [Atom.code] at h
      | rational b =>
          have hp := ratCode_prefix_unique (by simpa [Atom.code] using h)
          exact ⟨congrArg Atom.rational hp.1, hp.2⟩
      | bit b => simp [Atom.code] at h
  | bit a =>
      cases b with
      | integer b => simp [Atom.code] at h
      | rational b => simp [Atom.code] at h
      | bit b =>
          have hp : a = b ∧ left = right := by simpa [Atom.code] using h
          exact ⟨congrArg Atom.bit hp.1, hp.2⟩

/-- A fixed number of tagged cells is prefix-decodable. -/
theorem atoms_prefix_unique {a b : List Atom} {left right : Code}
    (lengths : a.length = b.length)
    (h : a.flatMap Atom.code ++ left = b.flatMap Atom.code ++ right) :
    a = b ∧ left = right := by
  induction a generalizing b with
  | nil =>
      have hb : b = [] := by cases b <;> simp_all
      subst b
      exact ⟨rfl, h⟩
  | cons a tail ih =>
      cases b with
      | nil => simp at lengths
      | cons b rest =>
          have hp := Atom.code_prefix_unique (by
            simpa only [List.flatMap_cons, List.append_assoc] using h)
          obtain ⟨hrest, hsuffix⟩ := ih (by simpa using lengths) hp.2
          exact ⟨by rw [hp.1, hrest], hsuffix⟩

/-- Structural table codes cannot alias two different normalized tables. -/
theorem tableCode_injective : Function.Injective tableCode := by
  intro a b h
  obtain ⟨lengths, bodies⟩ := natCode_prefix_unique h
  exact (atoms_prefix_unique (left := []) (right := []) lengths
    (by simpa using bodies)).1

/-- The fixed semantic codebook is single-valued; no answer-dependent choice remains. -/
theorem Represents.functional {code : Code} {a b : Table}
    (ha : Represents code a) (hb : Represents code b) : a = b := by
  obtain ⟨aa, rfl, hca⟩ := ha
  obtain ⟨bb, rfl, hcb⟩ := hb
  exact congrArg (List.map Atom.denote) (tableCode_injective (hca.trans hcb.symm))

/-- Classical choice in the semantic parser cannot choose a different table. -/
theorem decodeSpec_tableCode (atoms : List Atom) :
    decodeSpec (tableCode atoms) = some (atoms.map Atom.denote) := by
  classical
  have existsAtoms : ∃ other : List Atom, tableCode other = tableCode atoms := ⟨atoms, rfl⟩
  simp only [decodeSpec, dif_pos existsAtoms]
  rw [tableCode_injective (Classical.choose_spec existsAtoms)]

/-- Every represented table has the stated unique semantic decoding. -/
theorem Represents.decodeSpec {code : Code} {table : Table}
    (h : Represents code table) : decodeSpec code = some table := by
  obtain ⟨atoms, rfl, rfl⟩ := h
  exact decodeSpec_tableCode atoms

/-- Framing a pair preserves each component, independently of its interpretation. -/
theorem pairCode_injective {a b c d : Code} (h : pairCode a b = pairCode c d) :
    a = c ∧ b = d := by
  obtain ⟨hlen, hbody⟩ := natCode_prefix_unique (by
    simpa only [pairCode, List.append_assoc] using h)
  have hac : a = c := by
    have := congrArg (List.take a.length) hbody
    simpa [hlen] using this
  subst c
  exact ⟨rfl, List.append_inj_right hbody rfl⟩

end EconCSLib.OpenProblem.New.WordRAM.FiniteData

end
