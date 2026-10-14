/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.OpenProblem.New.OnlineSubmodularWelfare.Problem

/-!
# OnlineSubmodularWelfare: supporting material

Auxiliary definitions and lemmas for the problem statement.
-/

section

/-!
## Online execution schema

A fixed schema executes one finite program for all public dimensions. The driver
reveals each arriving item, answers value queries on the revealed prefix, and advances
after an irrevocable assignment. The accounting contract charges each local transition
as one operation.
-/

namespace EconCSLib.OpenProblem.New.EconCSBench.OnlineSubmodularWelfare
open WordRAM.FiniteData
open scoped BigOperators

/-- Execute from public initialization, never from a valuation-dependent memory state. -/
noncomputable def OnlineExecutionSchema.run (E : OnlineExecutionSchema)
    (program : Code) (agents items budget : ℕ)
    (v : OnlineValuationProfile agents items) (order : Equiv.Perm (Fin items))
    (tape : OnlineRandomTape budget) : OnlineExecutionResult agents items :=
  (E.runFrom v (fun cursor => if h : cursor < budget then some (tape ⟨cursor, h⟩) else none)
    budget (List.ofFn (fun t => order t)) ∅ (E.initial program agents items) 0).charge 0 0

/-- The full-real efficiency target relative to a fixed trusted local-step schema. All
commands and assignments are charged by the interpreter; no query-only time claim is
inferred. -/
def RandomOrderPointFiveOneExecutionSchemaQuestion (E : OnlineExecutionSchema) : Prop :=
  ∃ program : Code, ∃ budget : ℕ → ℕ,
    WordRAM.StrictCostCore.IsEventuallyBoundedByPolynomial id budget ∧
    ∀ agents items : ℕ, 0 < agents → 0 < items →
      ∀ v : OnlineValuationProfile agents items,
        ∃ outcome : Equiv.Perm (Fin items) →
            OnlineRandomTape (budget (agents + items + 1)) → OnlineAssignment agents items,
          (∀ order tape,
            let result := E.run program agents items (budget (agents + items + 1)) v order tape
            result.output = some (List.ofFn (fun t => (order t, outcome order tape (order t)))) ∧
            result.steps ≤ budget (agents + items + 1) ∧
            result.queries ≤ budget (agents + items + 1) ∧
            result.randomBits ≤ budget (agents + items + 1)) ∧
          ∀ alternative, (51 / 100 : ℝ) * assignmentWelfare v alternative ≤
            expectedExecutionWelfare v outcome

end EconCSLib.OpenProblem.New.EconCSBench.OnlineSubmodularWelfare

end


section

/-!
## Presented-domain online Word-RAM executions

A fixed driver invokes the same finite program at each arrival. Only public
dimensions, the revealed prefix, the current label, and the preceding memory bitstream
enter an invocation. The environment rejects future-item queries. Each halt emits one
owner followed by the next memory bitstream. This fixed parser cannot compute an
allocation for the program.

Each invocation uses the actual Word-RAM interpreter. The outer driver's buffer
copy/scan charge is explicit linear accounting. Values must be exactly rational with a
public bit bound; this represented-domain certificate does not cover arbitrary reals.
-/

namespace EconCSLib.OpenProblem.New.EconCSBench.OnlineSubmodularWelfare
open WordRAM.FiniteData

/-- Public dimensions and a bound on each rational scalar reply. -/
structure OnlineParameters where
  agents : ℕ
  items : ℕ
  valueBits : ℕ

/-- The represented domain is stated separately from unrestricted real valuations. -/
def HasOnlineValueBitBound (p : OnlineParameters)
    (v : OnlineValuationProfile p.agents p.items) : Prop :=
  ∀ i S, ∃ q : ℚ, (q : ℝ) = (v i).val S ∧ (ratCode q).length ≤ p.valueBits

/-- Fixed public size code, without the exponential valuation table. -/
def onlinePublicCode (p : OnlineParameters) : Code :=
  unaryPaddedDimensionCode [p.agents, p.items, p.valueBits]

/-- An agent and a bundle are encoded structurally, independently of their value. -/
def prefixQueryCode {agents items : ℕ} (query : Fin agents × Finset (Fin items)) : Code :=
  tableCode (.integer (Int.ofNat query.1.val) ::
    List.ofFn (fun j : Fin items => Atom.bit (decide (j ∈ query.2))))

/-- Fixed query recognition at the oracle boundary. -/
noncomputable def decodePrefixQuery (agents items : ℕ) (code : Code) :
    Option (Fin agents × Finset (Fin items)) := by
  classical
  exact if h : ∃ query : Fin agents × Finset (Fin items), prefixQueryCode query = code then
    some (Classical.choose h) else none

/-- Only arrived bundles can be queried. Each phase reads a disjoint block of fair bits. -/
noncomputable def prefixEnvironment {agents items bits : ℕ}
    (v : OnlineValuationProfile agents items) (seen : Finset (Fin items))
    (phase budget : ℕ) (tape : OnlineRandomTape bits) : WordRAM.Interaction.Environment Unit where
  query _ _ arguments := do
    let code ← ofWords arguments
    let query ← decodePrefixQuery agents items code
    if query.2 ⊆ seen then
      let reply ← encodeSpec [.real ((v query.1).val ⟨query.2, Finset.subset_univ _⟩)]
      pure (words reply)
    else none
  sample _ _ _ := none
  randomTape cursor :=
    if cursor < budget then
      if h : phase * budget + cursor < bits then some (tape ⟨phase * budget + cursor, h⟩)
      else none
    else none

/-- Public prefix metadata plus the exact memory produced by the previous invocation. -/
def onlineStepInput (p : OnlineParameters) (seen : Finset (Fin p.items))
    (current : Fin p.items) (memory : Code) : Code :=
  pairCode (onlinePublicCode p)
    (pairCode (tableCode (.integer (Int.ofNat current.val) ::
      List.ofFn (fun j : Fin p.items => Atom.bit (decide (j ∈ seen))))) memory)

/-- Direct parsing only: one bounded owner word followed by a memory bitstream. -/
def decodeOnlineStep (agents : ℕ) : List ℕ → Option (Fin agents × Code)
  | [] => none
  | owner :: memory =>
      if h : owner < agents then (ofWords memory).map fun code => (⟨owner, h⟩, code)
      else none

/-- One complete driver execution, with explicit invocation and buffer costs. -/
structure OnlineWordRAMResult (agents items : ℕ) where
  output : Option (List (Fin items × Fin agents))
  cost : ℕ
  queries : ℕ
  randomBits : ℕ

/-- Prefix-by-prefix execution; the next arrival is unavailable until the current owner is
output. -/
noncomputable def runOnlineWordRAMFrom (model : WordRAM.Model)
    (program : WordRAM.Interaction.Program Unit) (p : OnlineParameters) (budget : ℕ)
    (v : OnlineValuationProfile p.agents p.items)
    (tape : OnlineRandomTape (p.items * budget)) :
    List (Fin p.items) → Finset (Fin p.items) → Code → ℕ →
      OnlineWordRAMResult p.agents p.items
  | [], _, _, _ => ⟨some [], 0, 0, 0⟩
  | current :: tail, seen, memory, phase =>
      let now := insert current seen
      let input := onlineStepInput p now current memory
      let result := WordRAM.Interaction.run model
        (prefixEnvironment v now phase budget tape) program budget input
      let baseCost := result.cost + input.length + 1
      match result.termination with
      | .halted output =>
          match decodeOnlineStep p.agents output with
          | none => ⟨none, baseCost + output.length, result.state.queries, result.state.randomBits⟩
          | some (owner, nextMemory) =>
              let rest := runOnlineWordRAMFrom model program p budget v tape
                tail now nextMemory (phase + 1)
              ⟨rest.output.map ((current, owner) :: ·), baseCost + output.length + rest.cost,
                result.state.queries + rest.queries, result.state.randomBits + rest.randomBits⟩
      | _ => ⟨none, baseCost, result.state.queries, result.state.randomBits⟩

/-- Execution starts with empty memory; no valuation-dependent advice is supplied. -/
noncomputable def runOnlineWordRAM (model : WordRAM.Model)
    (program : WordRAM.Interaction.Program Unit) (p : OnlineParameters) (budget : ℕ)
    (v : OnlineValuationProfile p.agents p.items) (order : Equiv.Perm (Fin p.items))
    (tape : OnlineRandomTape (p.items * budget)) : OnlineWordRAMResult p.agents p.items :=
  runOnlineWordRAMFrom model program p budget v tape (List.ofFn (fun t => order t)) ∅ [] 0

/-- Actual represented-domain execution, with a uniform program and explicit
driver-accounting convention. -/
def PresentedOnlineWordRAMQuestion : Prop :=
  ∃ model : WordRAM.Model, ∃ program : WordRAM.Interaction.Program Unit,
    ∃ budget : OnlineParameters → ℕ,
      WordRAM.StrictCostCore.IsEventuallyBoundedByPolynomial
        (fun p => bitSize model (onlinePublicCode p)) budget ∧
      ∀ p : OnlineParameters, 0 < p.agents → 0 < p.items →
        ∀ v : OnlineValuationProfile p.agents p.items, HasOnlineValueBitBound p v →
          ∃ outcome : Equiv.Perm (Fin p.items) →
              OnlineRandomTape (p.items * budget p) → OnlineAssignment p.agents p.items,
            (∀ order tape,
              let result := runOnlineWordRAM model program p (budget p) v order tape
              result.output = some (List.ofFn (fun t => (order t, outcome order tape (order t)))) ∧
              result.cost ≤ budget p ∧ result.queries ≤ budget p ∧
              result.randomBits ≤ budget p) ∧
            ∀ alternative, (51 / 100 : ℝ) * assignmentWelfare v alternative ≤
              expectedExecutionWelfare v outcome

end EconCSLib.OpenProblem.New.EconCSBench.OnlineSubmodularWelfare

end


section

/-!
## The 0.51 random-order online-welfare question

The primary efficiency target uses a finite exact-real arithmetic controller, with
fixed primitives and a charged prefix-local oracle interpreter. It has no arbitrary
local transition callback. Exact-real unit-cost arithmetic is an explicit model
convention. Policy, query, trusted-schema and rational Word-RAM variants remain
separately named.
-/

namespace EconCSLib.OpenProblem.New.EconCSBench.OnlineSubmodularWelfare

/-- The online-welfare question under the specified schema accounting contract. -/
def OnlineSubmodularWelfareSchemaQuestion (E : OnlineExecutionSchema) : Prop :=
  RandomOrderPointFiveOneExecutionSchemaQuestion E

end EconCSLib.OpenProblem.New.EconCSBench.OnlineSubmodularWelfare

end
