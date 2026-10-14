/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.OpenProblem.New.SubmodularWelfareDemandOracle.Problem

/-!
# SubmodularWelfareDemandOracle: supporting material

Auxiliary definitions and lemmas for the problem statement.
-/

section

/-!
## Submodular welfare: semantic domain and guarantees

Uses native normalized monotone submodular valuations and complete allocations. The
rational-price interface is a separate finite-code implementation convention; it does
not claim that all real prices admit finite encodings. The full-real value-and-demand
interface is defined in RealOracle. Source: Feige–Vondrak, Theory of Computing 6
(2010), Section 1.
-/
open scoped BigOperators

namespace EconCSLib.OpenProblem.New.EconCSBench.SubmodularWelfareDemandOracle

/-- A rational-price query with no prior magnitude bound; its full representation is
charged by execution. -/
structure RationalDemandQuery (agents items : ℕ) where
  agent : Fin agents
  price : Fin items → ℚ
  nonnegative : ∀ j, 0 ≤ price j

noncomputable def demandUtility {agents items : ℕ} (v : SWMProfile agents items)
    (q : RationalDemandQuery agents items) (S : SWMBundle items) : ℝ :=
  value v q.agent S - ∑ j ∈ S, (q.price j : ℝ)

/-- Every utility-maximizing bundle is legal; maximizing value alone is insufficient. -/
def IsDemandAnswer {agents items : ℕ} (v : SWMProfile agents items)
    (q : RationalDemandQuery agents items) (S : SWMBundle items) : Prop :=
  ∀ T : SWMBundle items, demandUtility v q T ≤ demandUtility v q S

/-- A fixed demand selection function precedes the random tape. Guarantees quantify over
all such legal functions. -/
abbrev SWMDemandOracle (agents items : ℕ) :=
  RationalDemandQuery agents items → SWMBundle items

def IsValidSWMDemandOracle {agents items : ℕ} (v : SWMProfile agents items)
    (oracle : SWMDemandOracle agents items) : Prop :=
  ∀ q, IsDemandAnswer v q (oracle q)

end EconCSLib.OpenProblem.New.EconCSBench.SubmodularWelfareDemandOracle

end


section

/-!
## Welfare-maximization execution schema

A fixed schema executes one finite program for all dimensions. The driver supplies
oracle replies and random bits. The schema's accounting contract determines the cost
of local transitions, and the interpreter records output and accumulated cost.
-/

namespace EconCSLib.OpenProblem.New.EconCSBench.SubmodularWelfareDemandOracle
open WordRAM.FiniteData

/-- Start one finite program with public dimensions and a finite fair-bit tape. -/
noncomputable def RealSWMExecutionSchema.run (E : RealSWMExecutionSchema)
    (program : Code) (agents items budget : ℕ) (v : SWMProfile agents items)
    (oracle : RealDemandOracle agents items) (tape : SWMRandomTape budget) :
    RealSWMExecutionResult agents items :=
  (E.runFrom v oracle (fun cursor => if h : cursor < budget then some (tape ⟨cursor, h⟩)
    else none) budget (E.initial program agents items) 0).charge 0 0

/-- The full-real efficiency target relative to a schema fixed before the solver. The
interpreter charges every local step, both query kinds, and each random bit. -/
def RealSWMExecutionSchemaQuestion (E : RealSWMExecutionSchema) : Prop :=
  ∃ program : Code, ∃ budget : ℕ → ℕ,
    WordRAM.StrictCostCore.IsEventuallyBoundedByPolynomial id budget ∧
    ∀ agents items : ℕ, 0 < agents →
      ∀ (v : SWMProfile agents items) (oracle : RealDemandOracle agents items),
        IsValidRealDemandOracle v oracle →
          ∃ outcome : SWMRandomTape (budget (agents + items + 1)) →
              SWMAssignment agents items,
            (∀ tape,
              let result := E.run program agents items (budget (agents + items + 1)) v oracle tape
              result.output = some (outcome tape) ∧
              result.steps ≤ budget (agents + items + 1) ∧
              result.queries ≤ budget (agents + items + 1) ∧
              result.randomBits ≤ budget (agents + items + 1)) ∧
            MeetsApproximation v outcome

end EconCSLib.OpenProblem.New.EconCSBench.SubmodularWelfareDemandOracle

end


section

/-!
## Explicit finite-code demand conventions

Literal bundle-only, finite-precision bundle-only, and finite-precision
value-reporting variants are kept distinct. A public precision parameter bounds each
rational scalar representation. Actual Word-RAM interaction charges local steps and
exchanged words. Fixed parsers specify the oracle codebook; they are not callbacks
available to the program. These represented-domain variants do not replace the
full-real problem.
-/
namespace EconCSLib.OpenProblem.New.EconCSBench.SubmodularWelfareDemandOracle
open WordRAM.FiniteData

inductive SWMConvention
  | literalBundleOnly
  | finitePrecisionBundleOnly
  | finitePrecisionValueReporting
  deriving DecidableEq

structure PublicParameters where
  agents : ℕ
  items : ℕ
  valueBits : ℕ
  deriving DecidableEq

def ValidParameters (c : SWMConvention) (p : PublicParameters) : Prop :=
  0 < p.agents ∧ (c = .literalBundleOnly → p.valueBits = 0)

/-- A public bit bound on each scalar answer. Polynomial dependence on this bound is
explicit. -/
def HasValueBitBound (p : PublicParameters) (v : SWMProfile p.agents p.items) : Prop :=
  ∀ i S, ∃ q : ℚ, (q : ℝ) = value v i S ∧ (ratCode q).length ≤ p.valueBits

def AdmissibleProfile (c : SWMConvention) (p : PublicParameters)
    (v : SWMProfile p.agents p.items) : Prop :=
  match c with
  | .literalBundleOnly => True
  | _ => HasValueBitBound p v

/-- Public unary padding reflects the n,m,(B) size convention without valuation, optimum,
or advice data. -/
def programInput (c : SWMConvention) (p : PublicParameters) : Code :=
  unaryPaddedDimensionCode <|
    match c with
    | .literalBundleOnly => [p.agents, p.items]
    | _ => [p.agents, p.items, p.valueBits]

def demandQueryCode {agents items : ℕ} (q : RationalDemandQuery agents items) : Code :=
  tableCode (.integer (Int.ofNat q.agent.val) ::
    List.ofFn (fun j : Fin items => Atom.rational (q.price j)))

/-- Recognize exactly the fixed query code, including dimensions and nonnegative prices. -/
noncomputable def decodeDemandQuery (agents items : ℕ) (code : Code) :
    Option (RationalDemandQuery agents items) := by
  classical
  exact if h : ∃ q : RationalDemandQuery agents items, demandQueryCode q = code then
    some (Classical.choose h) else none

def bundleCode {items : ℕ} (S : SWMBundle items) : Code :=
  tableCode (List.ofFn (fun j : Fin items => Atom.bit (decide (j ∈ S))))

def assignmentCode {agents items : ℕ} (A : SWMAssignment agents items) : Code :=
  tableCode (List.ofFn (fun j : Fin items => Atom.integer (Int.ofNat (A j).val)))

/-- A reported scalar is exactly the demanded bundle's value, with no free advice field or
rounding. -/
noncomputable def replyCode {agents items : ℕ} (c : SWMConvention)
    (v : SWMProfile agents items) (q : RationalDemandQuery agents items)
    (S : SWMBundle items) : Option Code := by
  classical
  exact match c with
    | .finitePrecisionValueReporting =>
        if h : ∃ r : ℚ, (r : ℝ) = value v q.agent S then
          some (tableCode ((List.ofFn (fun j : Fin items =>
            Atom.bit (decide (j ∈ S)))) ++ [Atom.rational (Classical.choose h)]))
        else none
    | _ => some (bundleCode S)

/-- Private access is only through explicit demand calls; no hidden sampling or
unrestricted value callback is available. -/
noncomputable def demandEnvironment {agents items bits : ℕ} (c : SWMConvention)
    (v : SWMProfile agents items) (oracle : SWMDemandOracle agents items)
    (tape : SWMRandomTape bits) : WordRAM.Interaction.Environment Unit where
  query _ _ arguments := do
    let code ← ofWords arguments
    let q ← decodeDemandQuery agents items code
    let answer ← replyCode c v q (oracle q)
    pure (words answer)
  sample _ _ _ := none
  randomTape cursor := if h : cursor < bits then some (tape ⟨cursor, h⟩) else none

def IsDemandOnlyProgram (P : WordRAM.Interaction.Program Unit) : Prop :=
  ∀ instruction ∈ P.code.toList,
    match instruction with
    | .sample _ _ _ _ _ => False
    | _ => True

/-- The actual execution returns output, cost, and counts. Fuel or random-tape exhaustion
is not successful termination. -/
noncomputable def runSWM (c : SWMConvention) (model : WordRAM.Model)
    (P : WordRAM.Interaction.Program Unit) (p : PublicParameters) (budget : ℕ)
    (v : SWMProfile p.agents p.items) (oracle : SWMDemandOracle p.agents p.items)
    (tape : SWMRandomTape budget) : WordRAM.Interaction.Result :=
  WordRAM.Interaction.run model (demandEnvironment c v oracle tape) P budget
    (programInput c p)

/-- Every tape halts with the same canonically encoded complete allocation used in the
welfare guarantee; exchanged words are charged. -/
def SolvesInstance (c : SWMConvention) (model : WordRAM.Model)
    (P : WordRAM.Interaction.Program Unit) (p : PublicParameters) (budget : ℕ)
    (v : SWMProfile p.agents p.items) (oracle : SWMDemandOracle p.agents p.items) : Prop :=
  ∃ outcome : SWMRandomTape budget → SWMAssignment p.agents p.items,
    (∀ tape,
      let result := runSWM c model P p budget v oracle tape
      result.termination = .halted (words (assignmentCode (outcome tape))) ∧
      result.cost ≤ budget ∧ result.state.queries ≤ budget ∧
      result.state.randomBits ≤ budget) ∧
    MeetsApproximation v outcome

end EconCSLib.OpenProblem.New.EconCSBench.SubmodularWelfareDemandOracle

end


section

/-!
## Actual Word-RAM value-and-demand access on a presented domain

The representation is fixed independently of the solver: rational nonnegative prices,
rational value replies, explicit bundles and owner arrays. Both query types use
charged Interaction calls. The public bit bound concerns each value. Polynomial
dependence on that bound is explicit.
-/

namespace EconCSLib.OpenProblem.New.EconCSBench.SubmodularWelfareDemandOracle
open WordRAM.FiniteData

/-- The fixed two-operation oracle interface; neither operation is free. -/
inductive ValueDemandOperation
  | value
  | demand
  deriving DecidableEq, Fintype

/-- Structural code for an agent and a bundle, independent of its value. -/
def valueQueryCode {agents items : ℕ} (query : Fin agents × SWMBundle items) : Code :=
  tableCode (.integer (Int.ofNat query.1.val) ::
    List.ofFn (fun j : Fin items => Atom.bit (decide (j ∈ query.2))))

/-- Fixed recognition at the oracle boundary; not a program-callable answer decoder. -/
noncomputable def decodeValueQuery (agents items : ℕ) (code : Code) :
    Option (Fin agents × SWMBundle items) := by
  classical
  exact if h : ∃ query : Fin agents × SWMBundle items, valueQueryCode query = code then
    some (Classical.choose h) else none

/-- Only the exact scalar has a reply code; irrational values cannot be silently rounded. -/
noncomputable def exactRationalReply (value : ℝ) : Option Code := by
  classical
  exact if h : ∃ q : ℚ, (q : ℝ) = value then some (ratCode (Classical.choose h)) else none

/-- Both explicit oracle calls, with the same fixed profile, oracle, and fair-bit tape. -/
noncomputable def valueDemandEnvironment {agents items bits : ℕ}
    (v : SWMProfile agents items) (oracle : SWMDemandOracle agents items)
    (tape : SWMRandomTape bits) : WordRAM.Interaction.Environment ValueDemandOperation where
  query operation _ arguments := do
    let code ← ofWords arguments
    match operation with
    | .value =>
        let query ← decodeValueQuery agents items code
        let reply ← exactRationalReply (value v query.1 query.2)
        pure (words reply)
    | .demand =>
        let query ← decodeDemandQuery agents items code
        pure (words (bundleCode (oracle query)))
  sample _ _ _ := none
  randomTape cursor := if h : cursor < bits then some (tape ⟨cursor, h⟩) else none

/-- Private sample operations are unavailable; randomness consists of charged fair bits
only. -/
def IsValueDemandProgram (P : WordRAM.Interaction.Program ValueDemandOperation) : Prop :=
  ∀ instruction ∈ P.code.toList,
    match instruction with
    | .sample _ _ _ _ _ => False
    | _ => True

/-- The genuine mini Word-RAM interpreter. -/
noncomputable def runValueDemandSWM (model : WordRAM.Model)
    (P : WordRAM.Interaction.Program ValueDemandOperation) (p : PublicParameters) (budget : ℕ)
    (v : SWMProfile p.agents p.items) (oracle : SWMDemandOracle p.agents p.items)
    (tape : SWMRandomTape budget) : WordRAM.Interaction.Result :=
  WordRAM.Interaction.run model (valueDemandEnvironment v oracle tape) P budget
    (programInput .finitePrecisionBundleOnly p)

/-- Same-run output, total cost, total oracle count, and random-bit count on every tape. -/
def SolvesValueDemandInstance (model : WordRAM.Model)
    (P : WordRAM.Interaction.Program ValueDemandOperation) (p : PublicParameters) (budget : ℕ)
    (v : SWMProfile p.agents p.items) (oracle : SWMDemandOracle p.agents p.items) : Prop :=
  ∃ outcome : SWMRandomTape budget → SWMAssignment p.agents p.items,
    (∀ tape,
      let result := runValueDemandSWM model P p budget v oracle tape
      result.termination = .halted (words (assignmentCode (outcome tape))) ∧
      result.cost ≤ budget ∧ result.state.queries ≤ budget ∧
      result.state.randomBits ≤ budget) ∧
    MeetsApproximation v outcome

/-- Uniform finite-precision value-and-demand implementation, polynomial also in the
public bit bound. -/
def FinitePrecisionValueAndDemandSWMWordRAMStatement : Prop :=
  ∃ model : WordRAM.Model, ∃ P : WordRAM.Interaction.Program ValueDemandOperation,
    ∃ budget : PublicParameters → ℕ,
      IsValueDemandProgram P ∧
      WordRAM.StrictCostCore.IsEventuallyBoundedByPolynomial
        (fun p => bitSize model (programInput .finitePrecisionBundleOnly p)) budget ∧
      ∀ p : PublicParameters, 0 < p.agents →
        ∀ v : SWMProfile p.agents p.items, HasValueBitBound p v →
          (∃ oracle, IsValidSWMDemandOracle v oracle) ∧
          ∀ oracle : SWMDemandOracle p.agents p.items,
            IsValidSWMDemandOracle v oracle →
              SolvesValueDemandInstance model P p (budget p) v oracle

end EconCSLib.OpenProblem.New.EconCSBench.SubmodularWelfareDemandOracle

end


section

/-!
## Welfare targets with explicit computational scope

The full-real query target uses value and demand access, following the numerical
oracle convention in Feige–Vondrak (2010), p. 248. Query complexity alone does not
certify polynomial local time. The primary full-real question uses a fixed finite
exact-real arithmetic language with charged oracle interaction. The separate Word-RAM
statements use actual executions on named represented domains, with worst-case time,
query, and fair-bit bounds.
-/
namespace EconCSLib.OpenProblem.New.EconCSBench.SubmodularWelfareDemandOracle
open WordRAM.FiniteData

/-- The arbitrary-transition schema remains explicitly separate. -/
def SubmodularWelfareSchemaQuestion (E : RealSWMExecutionSchema) : Prop :=
  RealSWMExecutionSchemaQuestion E

/-- One finite program and one eventual polynomial bound precede every dimension, profile,
oracle, and random tape; correctness holds on every valid input. -/
def SWMWordRAMQuestion (c : SWMConvention) : Prop :=
  ∃ model : WordRAM.Model, ∃ P : WordRAM.Interaction.Program Unit,
    ∃ budget : PublicParameters → ℕ,
      IsDemandOnlyProgram P ∧
      WordRAM.StrictCostCore.IsEventuallyBoundedByPolynomial
        (fun p => bitSize model (programInput c p)) budget ∧
      ∀ p : PublicParameters, ValidParameters c p →
        ∀ v : SWMProfile p.agents p.items, AdmissibleProfile c p v →
          (∃ oracle, IsValidSWMDemandOracle v oracle) ∧
          ∀ oracle : SWMDemandOracle p.agents p.items,
            IsValidSWMDemandOracle v oracle →
              SolvesInstance c model P p (budget p) v oracle

/-- Literal bundle-only, with no public valuation scale or precision. -/
def LiteralBundleOnlySWMWordRAMStatement : Prop :=
  SWMWordRAMQuestion .literalBundleOnly

/-- Bundle-only with public scalar bit bound B and polynomial dependence on n,m,B; no
valuation table is supplied. -/
def FinitePrecisionBundleOnlySWMWordRAMStatement : Prop :=
  SWMWordRAMQuestion .finitePrecisionBundleOnly

/-- Finite precision with the demanded bundle's exact value included. Nonnegative prices
and the representation restriction remain explicit. -/
def FinitePrecisionValueReportingSWMWordRAMStatement : Prop :=
  SWMWordRAMQuestion .finitePrecisionValueReporting

end EconCSLib.OpenProblem.New.EconCSBench.SubmodularWelfareDemandOracle

end
