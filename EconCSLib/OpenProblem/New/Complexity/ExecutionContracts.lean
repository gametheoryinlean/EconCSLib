/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.OpenProblem.New.Complexity.WordRAM.Search



section

/-!
# Representations and execution contracts

`Presentation` specifies input and output decoding. Coverage and polynomial-size names
describe its represented domain. `Realization` relates the decoded output and cost of
a machine execution to the mathematical specification. `HasUniformPolynomialEnvelope`
bounds executions at every input size.
-/
namespace EconCSLib.OpenProblem.New.ExecutionContracts
open WordRAM.FiniteData
universe u v

/-- A polynomial budget depending only on size and bounding every execution. -/
def HasUniformPolynomialEnvelope {Input : Type u}
    (size cost : Input → ℕ) : Prop :=
  ∃ budget : ℕ → ℕ,
    WordRAM.StrictCostCore.IsEventuallyBoundedByPolynomial (fun n : ℕ => n) budget ∧
      ∀ input, cost input ≤ budget (size input)

/-- A fixed finite presentation. Full-real surjectivity is not assumed. -/
structure Presentation (Input : Type u) (Output : Type v) where
  decodeInput : Code → Option Input
  decodeOutput : Code → Option Output

/-- Coverage of an explicitly declared semantic domain. This is a separate obligation: an
empty decoder cannot cover a nonempty domain. -/
def Presentation.Covers {Input : Type u} {Output : Type v}
    (P : Presentation Input Output) (domain : Input → Prop) : Prop :=
  ∀ input, domain input → ∃ code, P.decodeInput code = some input

/-- Polynomial-size names on a stated domain. This prevents a represented algorithm from
obtaining its bound merely by padding every input name. -/
def Presentation.HasPolynomialNames {Input : Type u} {Output : Type v}
    (P : Presentation Input Output) (domain : Input → Prop)
    (size : Input → ℕ) : Prop :=
  ∃ coefficient exponent : ℕ, ∀ input, domain input →
    ∃ code, P.decodeInput code = some input ∧
      code.length ≤ coefficient * (size input + 1) ^ exponent

/-- A polynomial naming bound entails coverage, including at small sizes. -/
theorem Presentation.HasPolynomialNames.covers
    {Input : Type u} {Output : Type v}
    {P : Presentation Input Output} {domain : Input → Prop} {size : Input → ℕ}
    (h : P.HasPolynomialNames domain size) : P.Covers domain := by
  rcases h with ⟨_, _, h⟩
  intro input hi
  obtain ⟨code, hc, _⟩ := h input hi
  exact ⟨code, hc⟩

/-- Codes describing valid semantic inputs. -/
def Presentation.ValidCode {Input : Type u} {Output : Type v}
    (P : Presentation Input Output) (valid : Input → Prop) (code : Code) : Prop :=
  ∃ input, P.decodeInput code = some input ∧ valid input

/-- Search on the stated presentation, with the original solution relation. The decoders
specify representation; they are not machine instructions. -/
def Presentation.searchProblem {Input : Type u} {Output : Type v}
    (P : Presentation Input Output) (valid : Input → Prop)
    (solution : Input → Output → Prop) : WordRAM.Search.Problem where
  valid := P.ValidCode valid
  solution inputCode outputCode :=
    ∃ input output,
      P.decodeInput inputCode = some input ∧
      P.decodeOutput outputCode = some output ∧ solution input output

/-- An actual interpreter implementation on represented inputs. There is no independent
output function or freely annotated execution cost. -/
structure Realization {Input : Type u} {Output : Type v}
    (P : Presentation Input Output) (valid : Input → Prop)
    (solve : Input → Output) where
  model : WordRAM.Model
  program : WordRAM.Program
  fuel : Code → ℕ
  correct : ∀ code input, P.decodeInput code = some input → valid input →
    ∃ outputCode,
      (WordRAM.Search.execution model program (fuel code) code).termination =
        .halted (words outputCode) ∧
      P.decodeOutput outputCode = some (solve input)

/-- Cost from the very execution used in the correctness contract. -/
def Realization.cost {Input : Type u} {Output : Type v}
    {P : Presentation Input Output} {valid : Input → Prop} {solve : Input → Output}
    (W : Realization P valid solve) (code : Code) : ℕ :=
  (WordRAM.Search.execution W.model W.program (W.fuel code) code).cost

/-- Polynomial interpreter cost in the fixed code's bit size. No runtime guarantee is
asserted for unrepresented real inputs. -/
def Realization.IsPolynomialTime {Input : Type u} {Output : Type v}
    {P : Presentation Input Output} {valid : Input → Prop} {solve : Input → Output}
    (W : Realization P valid solve) : Prop :=
  WordRAM.StrictCostCore.IsEventuallyBoundedByPolynomial
    (fun code : {c : Code // P.ValidCode valid c} => bitSize W.model code.1)
    (fun code : {c : Code // P.ValidCode valid c} => W.cost code.1)

end EconCSLib.OpenProblem.New.ExecutionContracts

end
