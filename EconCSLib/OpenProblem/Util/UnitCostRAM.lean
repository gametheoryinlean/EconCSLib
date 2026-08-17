/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.Foundation.CostM
import EconCSLib.Foundation.CostM.Cells
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring

/-!
# Unit-cost RAM accounting for open problems

This module supplies an explicit *cost-accounting semantics* for algorithms
whose primitive RAM operations are charged one unit.  It deliberately does not
identify word-RAM, real-RAM, and the Blum--Shub--Smale model: the permitted
primitive operations determine which of those interpretations is intended.
The one-unit-per-instruction convention is the unit-cost specialization of
the RAM accounting framework of Cook and Reckhow, *Time Bounded Random Access
Machines*, JCSS 7 (1973), 354--375.  Exact real words and constant-cost field
operations follow the algebraic-computation viewpoint of Blum, Shub, and
Smale, *On a Theory of Computation and Complexity over the Real Numbers*,
Bull. AMS 21 (1989), 1--46.  This file does not silently equate the models:
the selected word type and primitive set state which specialization is used.

The central object is `Cost α := CostM ℕ α`, the natural-number specialization
of EconCSLib's shared cost writer monad.  Compatibility projections
`Cost.value` and `Cost.ops` expose its returned value and charged operation
count.  A costed implementation of a Lean function must both compute the same
mathematical value and have a polynomially bounded operation count.  The
definitions are polymorphic in the input and dependent output types, so they
apply uniformly to ordinary, curried, structure-valued, and dependent
functions.

This is an instrumentation interface, not a syntactic RAM instruction set.
Consequently, correctness review must ensure that a proposed implementation is
built from the declared unit-cost primitives rather than hiding unaccounted
work inside `Cost.pure` or `Cost.map`.  Problems needing machine-enforced
instruction-level complexity should introduce a problem-specific program
syntax and prove that its interpreter realizes a `CostedImplementation`.
`UnitCostRAMMachine` supplies such a finite instruction syntax and interpreter
for claims that require machine-enforced accounting.  The writer-monad proof
style follows Danielsson (POPL 2008) and EconCSLib's `Foundation.CostM`, which
is adapted from `leanprover/cslib`'s `TimeM`.
-/

namespace EconCSLib.OpenProblem.UnitCostRAM

open scoped BigOperators

universe u v w

/-- Unit-cost RAM computations are the natural-number specialization of the
shared `CostM` writer monad. -/
abbrev Cost (α : Type u) := CostM ℕ α

namespace Cost

variable {α : Type u} {β : Type v} {γ : Type w}

/-- Compatibility projection for the returned value of a unit-cost
computation. -/
@[simp] def value (x : Cost α) : α := x.ret

/-- Compatibility projection for the number of charged RAM operations. -/
@[simp] def ops (x : Cost α) : ℕ := x.cost

/-- Inject an already available value without charging an operation.  This is
not permission to hide a nontrivial Lean computation in the argument. -/
def pure (a : α) : Cost α := CostM.pure a

/-- Sequential composition; only the two component computations contribute
to the operation count. -/
def bind (x : Cost α) (f : α → Cost β) : Cost β :=
  let y := f x.value
  ⟨y.value, x.ops + y.ops⟩

/-- Apply a bookkeeping-only transformation.  Nontrivial RAM work must use a
charged primitive instead of `map`. -/
def map (f : α → β) (x : Cost α) : Cost β := ⟨f x.value, x.ops⟩

def seq (f : Cost (α → β)) (x : Unit → Cost α) : Cost β :=
  let x := x ()
  ⟨f.value x.value, f.ops + x.ops⟩

@[simp] theorem value_pure (a : α) : (pure a).value = a := rfl
@[simp] theorem ops_pure (a : α) : (pure a).ops = 0 := rfl
@[simp] theorem value_bind (x : Cost α) (f : α → Cost β) :
    (bind x f).value = (f x.value).value := rfl
@[simp] theorem ops_bind (x : Cost α) (f : α → Cost β) :
    (bind x f).ops = x.ops + (f x.value).ops := rfl
@[simp] theorem value_map (f : α → β) (x : Cost α) :
    (map f x).value = f x.value := rfl
@[simp] theorem ops_map (f : α → β) (x : Cost α) :
    (map f x).ops = x.ops := rfl

/-! ## Charged primitives -/

/-- Charge one operation after an already instrumented computation. -/
def tick (x : Cost α) : Cost α := ⟨x.value, x.ops + 1⟩

/-- A unary primitive operation costs one unit. -/
def liftUnary (op : α → β) (x : Cost α) : Cost β :=
  ⟨op x.value, x.ops + 1⟩

/-- A binary primitive operation costs one unit in addition to the cost of
obtaining its operands. -/
def liftBinary (op : α → β → γ) (x : Cost α) (y : Cost β) : Cost γ :=
  ⟨op x.value y.value, x.ops + y.ops + 1⟩

/-- A ternary primitive operation costs one unit in addition to its operands. -/
def liftTernary {δ : Type*} (op : α → β → γ → δ)
    (x : Cost α) (y : Cost β) (z : Cost γ) : Cost δ :=
  ⟨op x.value y.value z.value, x.ops + y.ops + z.ops + 1⟩

@[simp] theorem ops_tick (x : Cost α) : (tick x).ops = x.ops + 1 := rfl
@[simp] theorem ops_liftUnary (op : α → β) (x : Cost α) :
    (liftUnary op x).ops = x.ops + 1 := rfl
@[simp] theorem ops_liftBinary (op : α → β → γ) (x : Cost α) (y : Cost β) :
    (liftBinary op x y).ops = x.ops + y.ops + 1 := rfl

@[simp] theorem ops_liftTernary {δ : Type*} (op : α → β → γ → δ)
    (x : Cost α) (y : Cost β) (z : Cost γ) :
    (liftTernary op x y z).ops = x.ops + y.ops + z.ops + 1 := rfl

def add [Add α] (x y : Cost α) : Cost α := liftBinary (· + ·) x y
def sub [Sub α] (x y : Cost α) : Cost α := liftBinary (· - ·) x y
def mul [Mul α] (x y : Cost α) : Cost α := liftBinary (· * ·) x y
def div [Div α] (x y : Cost α) : Cost α := liftBinary (· / ·) x y
def neg [Neg α] (x : Cost α) : Cost α := liftUnary Neg.neg x

def le [LE α] [DecidableRel ((· ≤ ·) : α → α → Prop)]
    (x y : Cost α) : Cost Bool :=
  liftBinary (fun a b => decide (a ≤ b)) x y

def lt [LT α] [DecidableRel ((· < ·) : α → α → Prop)]
    (x y : Cost α) : Cost Bool :=
  liftBinary (fun a b => decide (a < b)) x y

def beq [DecidableEq α] (x y : Cost α) : Cost Bool :=
  liftBinary (fun a b => decide (a = b)) x y

/-- A branch decision costs one unit after the condition has been computed;
only the selected branch is executed. -/
def branch (condition : Cost Bool) (ifTrue ifFalse : Unit → Cost α) : Cost α :=
  let result := if condition.value then ifTrue () else ifFalse ()
  ⟨result.value, condition.ops + result.ops + 1⟩

end Cost

/-! ## Unit-cost random-access words and encodings -/

/-- One externally represented word.  A real word stores an exact real number
and is therefore charged according to the BSS/unit-cost real-RAM convention,
not according to a bit approximation.  Discrete control data remain explicit. -/
inductive Word
  | integer (value : Int)
  | real (value : ℝ)
  | bit (value : Bool)

/-- A lossless finite-word representation of an input type.  Complexity in
`Encoding.size` is representation-relative, so the encoding must be fixed by
the problem statement.  Because exact integer/real words have infinite
alphabets, injectivity alone does *not* prevent an artificial encoding from
packing a large discrete object into one word; canonical structural encodings
and the strict instruction set are therefore both essential. -/
structure Encoding (Input : Type u) where
  encode : Input → List Word
  decode : List Word → Option Input
  decode_encode : ∀ input, decode (encode input) = some input

/-- Number of unit-cost RAM words in an encoded input. -/
def Encoding.size {Input : Type u} (encoding : Encoding Input)
    (input : Input) : ℕ := (encoding.encode input).length

theorem Encoding.encode_injective {Input : Type u}
    (encoding : Encoding Input) : Function.Injective encoding.encode := by
  intro left right h
  apply Option.some.inj
  calc
    some left = encoding.decode (encoding.encode left) :=
      (encoding.decode_encode left).symm
    _ = encoding.decode (encoding.encode right) := congrArg encoding.decode h
    _ = some right := encoding.decode_encode right

/-- Lossless representation of an output type that depends on its input. -/
structure DependentEncoding {Input : Type u} (Output : Input → Type v) where
  encode : (input : Input) → Output input → List Word
  decode : (input : Input) → List Word → Option (Output input)
  decode_encode : ∀ input output, decode input (encode input output) = some output

def DependentEncoding.size {Input : Type u} {Output : Input → Type v}
    (encoding : DependentEncoding Output) (input : Input)
    (output : Output input) : ℕ := (encoding.encode input output).length

namespace DependentEncoding

/-- Pull a dependent encoding back along a change of input index. -/
def comap {Input : Type u} {Index : Type v} {Output : Input → Type w}
    (encoding : DependentEncoding Output) (index : Index → Input) :
    DependentEncoding (fun i => Output (index i)) where
  encode i output := encoding.encode (index i) output
  decode i words := encoding.decode (index i) words
  decode_encode i output := encoding.decode_encode (index i) output

end DependentEncoding

namespace Encoding

/-- Regard an ordinary encoding as an input-independent dependent encoding. -/
def dependent {Index : Type v} {Value : Type u}
    (encoding : Encoding Value) :
    DependentEncoding (fun _ : Index => Value) where
  encode _ value := encoding.encode value
  decode _ words := encoding.decode words
  decode_encode _ value := encoding.decode_encode value

@[simp] theorem size_dependent {Index : Type v} {Value : Type u}
    (encoding : Encoding Value) (index : Index) (value : Value) :
    (encoding.dependent.size index value) = encoding.size value := rfl

/-- Canonical length-prefixed encoding of a dependent pair.  This is the
representation used for the decoding stage of strict search reductions: the
source instance is encoded first, followed by a target solution whose type may
depend on that instance. -/
def sigma {Input : Type u} {Output : Input → Type v}
    (input : Encoding Input) (output : DependentEncoding Output) :
    Encoding (Σ i, Output i) where
  encode pair :=
    .integer (input.encode pair.1).length ::
      input.encode pair.1 ++ output.encode pair.1 pair.2
  decode words :=
    match words with
    | .integer length :: rest =>
        if 0 ≤ length then
          let count := length.toNat
          match input.decode (rest.take count) with
          | some i =>
              match output.decode i (rest.drop count) with
              | some value => some ⟨i, value⟩
              | none => none
          | none => none
        else none
    | _ => none
  decode_encode pair := by
    simp [input.decode_encode, output.decode_encode]

@[simp] theorem size_sigma {Input : Type u} {Output : Input → Type v}
    (input : Encoding Input) (output : DependentEncoding Output)
    (pair : Σ i, Output i) :
    (input.sigma output).size pair =
      input.size pair.1 + output.size pair.1 pair.2 + 1 := by
  simp [Encoding.size, sigma, DependentEncoding.size]

end Encoding

namespace Cost

/-! ## Unit-cost random-access memory -/

/-- Unbounded mathematical RAM memory.  A concrete problem chooses its word
type; for example `ℕ` gives an integer unit-cost RAM, while `ℝ` gives a
unit-cost real-arithmetic interpretation. -/
abbrev Memory (Word : Type*) := ℕ → Word

/-- Reading one addressed cell costs one unit. -/
def readMemory {Word : Type*}
    (memory : Cost (Memory Word)) (address : Cost ℕ) : Cost Word :=
  liftBinary (fun m i => m i) memory address

/-- Writing one addressed cell costs one unit and returns the updated memory. -/
def writeMemory {Word : Type*}
    (memory : Cost (Memory Word)) (address : Cost ℕ) (word : Cost Word) :
    Cost (Memory Word) :=
  liftTernary (fun m i value => Function.update m i value)
    memory address word

/-! ## Traversal primitives -/

/-- Sum over a finite collection.  Evaluating each body is charged according
to its annotation and each accumulator visit costs one additional unit. -/
def sumFinset {ι : Type*} [AddCommMonoid α]
    (s : Finset ι) (f : ι → Cost α) : Cost α :=
  ⟨∑ i ∈ s, (f i).value, (∑ i ∈ s, (f i).ops) + s.card⟩

@[simp] theorem value_sumFinset {ι : Type*} [AddCommMonoid α]
    (s : Finset ι) (f : ι → Cost α) :
    (sumFinset s f).value = ∑ i ∈ s, (f i).value := rfl

@[simp] theorem ops_sumFinset {ι : Type*} [AddCommMonoid α]
    (s : Finset ι) (f : ι → Cost α) :
    (sumFinset s f).ops = (∑ i ∈ s, (f i).ops) + s.card := rfl

/-- Product counterpart of `sumFinset`. -/
def prodFinset {ι : Type*} [CommMonoid α]
    (s : Finset ι) (f : ι → Cost α) : Cost α :=
  ⟨∏ i ∈ s, (f i).value, (∑ i ∈ s, (f i).ops) + s.card⟩

@[simp] theorem value_prodFinset {ι : Type*} [CommMonoid α]
    (s : Finset ι) (f : ι → Cost α) :
    (prodFinset s f).value = ∏ i ∈ s, (f i).value := rfl

@[simp] theorem ops_prodFinset {ι : Type*} [CommMonoid α]
    (s : Finset ι) (f : ι → Cost α) :
    (prodFinset s f).ops = (∑ i ∈ s, (f i).ops) + s.card := rfl

/-- Filter a finite collection, charging the predicate and one visit per
element. -/
def filterFinset {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (p : ι → Cost Bool) : Cost (Finset ι) :=
  ⟨s.filter (fun i => (p i).value), (∑ i ∈ s, (p i).ops) + s.card⟩

@[simp] theorem ops_filterFinset {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (p : ι → Cost Bool) :
    (filterFinset s p).ops = (∑ i ∈ s, (p i).ops) + s.card := rfl

/-! ## Sequential loop combinators -/

/-- Stateful left fold over a list. Each iteration charges the annotated body
cost and one additional unit for loop control. -/
def foldlList (step : β → α → Cost β) : List α → β → Cost β
  | [], state => pure state
  | item :: items, state =>
      let next := step state item
      let tail := foldlList step items next.value
      ⟨tail.value, next.ops + tail.ops + 1⟩

/-- Map an annotated computation over a list, charging one loop-control step
per element in addition to the element computation. -/
def mapList (f : α → Cost β) : List α → Cost (List β)
  | [] => pure []
  | item :: items =>
      let head := f item
      let tail := mapList f items
      ⟨head.value :: tail.value, head.ops + tail.ops + 1⟩

/-- Execute a state transition exactly `iterations` times. -/
def iterate (iterations : ℕ) (step : α → Cost α) (initial : α) : Cost α :=
  match iterations with
  | 0 => pure initial
  | n + 1 =>
      let next := step initial
      let tail := iterate n step next.value
      ⟨tail.value, next.ops + tail.ops + 1⟩

/-- Result of a fuel-bounded while loop. -/
inductive WhileResult (α : Type u)
  | done (state : α)
  | exhausted (state : α)

/-- Total semantics for a while loop. Fuel is an explicit termination
certificate; conditions, selected bodies, and control decisions are charged. -/
def whileFuel (fuel : ℕ) (condition : α → Cost Bool)
    (body : α → Cost α) (initial : α) : Cost (WhileResult α) :=
  match fuel with
  | 0 => pure (.exhausted initial)
  | n + 1 =>
      let test := condition initial
      if test.value then
        let next := body initial
        let tail := whileFuel n condition body next.value
        ⟨tail.value, test.ops + next.ops + tail.ops + 1⟩
      else
        ⟨.done initial, test.ops + 1⟩

@[simp] theorem ops_foldlList_nil (step : β → α → Cost β) (state : β) :
    (foldlList step [] state).ops = 0 := rfl

@[simp] theorem ops_foldlList_cons (step : β → α → Cost β)
    (item : α) (items : List α) (state : β) :
    (foldlList step (item :: items) state).ops =
      (step state item).ops +
        (foldlList step items (step state item).value).ops + 1 := rfl

@[simp] theorem ops_mapList (f : α → Cost β) (items : List α) :
    (mapList f items).ops =
      (items.map fun item => (f item).ops).sum + items.length := by
  induction items with
  | nil => rfl
  | cons item items ih =>
      change (f item).ops + (mapList f items).ops + 1 =
        (f item).ops + (items.map fun x => (f x).ops).sum +
          (items.length + 1)
      rw [ih]
      omega

/-- A counted loop has the expected multiplicative bound when every state
transition has a common upper bound. -/
theorem ops_iterate_le (iterations bodyBound : ℕ) (step : α → Cost α)
    (initial : α) (hstep : ∀ state, (step state).ops ≤ bodyBound) :
    (iterate iterations step initial).ops ≤ iterations * (bodyBound + 1) := by
  induction iterations generalizing initial with
  | zero => simp [iterate, ops, pure, CostM.pure]
  | succ n ih =>
      simp only [iterate]
      calc
        (step initial).ops + (iterate n step (step initial).value).ops + 1
            ≤ bodyBound + n * (bodyBound + 1) + 1 := by
                exact Nat.add_le_add_right
                  (Nat.add_le_add (hstep initial) (ih (step initial).value)) 1
        _ = (n + 1) * (bodyBound + 1) := by ring

/-- Cost bound for a stateful list fold. -/
theorem ops_foldlList_le (step : β → α → Cost β) (items : List α)
    (initial : β) (bodyBound : ℕ)
    (hstep : ∀ state item, (step state item).ops ≤ bodyBound) :
    (foldlList step items initial).ops ≤
      items.length * (bodyBound + 1) := by
  induction items generalizing initial with
  | nil =>
      simp only [ops_foldlList_nil, List.length_nil, Nat.zero_mul]
      exact le_rfl
  | cons item items ih =>
      rw [ops_foldlList_cons]
      calc
        (step initial item).ops +
              (foldlList step items (step initial item).value).ops + 1
            ≤ bodyBound + items.length * (bodyBound + 1) + 1 := by
                exact Nat.add_le_add_right
                  (Nat.add_le_add (hstep initial item)
                    (ih (step initial item).value)) 1
        _ = (item :: items).length * (bodyBound + 1) := by
          simp only [List.length_cons]
          ring

/-- A fuelled while loop is bounded by fuel times the worst cost of one test,
one body execution, and one control decision. -/
theorem ops_whileFuel_le (fuel conditionBound bodyBound : ℕ)
    (condition : α → Cost Bool) (body : α → Cost α) (initial : α)
    (hcondition : ∀ state, (condition state).ops ≤ conditionBound)
    (hbody : ∀ state, (body state).ops ≤ bodyBound) :
    (whileFuel fuel condition body initial).ops ≤
      fuel * (conditionBound + bodyBound + 1) := by
  induction fuel generalizing initial with
  | zero =>
      simp only [whileFuel, ops_pure, Nat.zero_mul]
      exact le_rfl
  | succ remaining ih =>
      simp only [whileFuel]
      split
      · have htest := hcondition initial
        have hnext := hbody initial
        have hrest := ih (body initial).value
        calc
          (condition initial).ops + (body initial).ops +
                (whileFuel remaining condition body
                  (body initial).value).ops + 1
              ≤ conditionBound + bodyBound +
                    remaining * (conditionBound + bodyBound + 1) + 1 := by
                  omega
          _ = (remaining + 1) * (conditionBound + bodyBound + 1) := by ring
      · have htest := hcondition initial
        have hbase : conditionBound + 1 ≤
            conditionBound + bodyBound + 1 := by omega
        calc
          (condition initial).ops + 1 ≤ conditionBound + 1 := by omega
          _ ≤ conditionBound + bodyBound + 1 := hbase
          _ ≤ (remaining + 1) *
                (conditionBound + bodyBound + 1) := by
              exact Nat.le_mul_of_pos_left _ (Nat.succ_pos remaining)

end Cost

/-! ## Simultaneous resource accounting -/

/-- Additive resources accumulated by a sequential unit-cost real-RAM run.

`steps` counts local RAM operations. The other fields count resources whose
complexity is often studied independently in EconCS. Peak live memory is not
stored here because it is not additive; it is tracked by `Cells` below. -/
@[ext]
structure ResourceCounts where
  steps : ℕ
  oracleQueries : ℕ
  distributionSamples : ℕ
  randomBits : ℕ
  communicationUnits : ℕ
  deriving DecidableEq

namespace ResourceCounts

instance : Zero ResourceCounts := ⟨⟨0, 0, 0, 0, 0⟩⟩

instance : Add ResourceCounts where
  add left right :=
    ⟨left.steps + right.steps,
      left.oracleQueries + right.oracleQueries,
      left.distributionSamples + right.distributionSamples,
      left.randomBits + right.randomBits,
      left.communicationUnits + right.communicationUnits⟩

instance : AddCommMonoid ResourceCounts where
  add_assoc _ _ _ := by ext <;> exact Nat.add_assoc _ _ _
  zero_add _ := by ext <;> exact Nat.zero_add _
  add_zero _ := by ext <;> exact Nat.add_zero _
  add_comm _ _ := by ext <;> exact Nat.add_comm _ _
  nsmul := nsmulRec

@[simp] theorem steps_zero : (0 : ResourceCounts).steps = 0 := rfl
@[simp] theorem queries_zero : (0 : ResourceCounts).oracleQueries = 0 := rfl
@[simp] theorem samples_zero : (0 : ResourceCounts).distributionSamples = 0 := rfl
@[simp] theorem randomBits_zero : (0 : ResourceCounts).randomBits = 0 := rfl
@[simp] theorem communicationUnits_zero :
    (0 : ResourceCounts).communicationUnits = 0 := rfl

@[simp] theorem steps_add (left right : ResourceCounts) :
    (left + right).steps = left.steps + right.steps := rfl
@[simp] theorem queries_add (left right : ResourceCounts) :
    (left + right).oracleQueries =
      left.oracleQueries + right.oracleQueries := rfl
@[simp] theorem samples_add (left right : ResourceCounts) :
    (left + right).distributionSamples =
      left.distributionSamples + right.distributionSamples := rfl
@[simp] theorem randomBits_add (left right : ResourceCounts) :
    (left + right).randomBits = left.randomBits + right.randomBits := rfl
@[simp] theorem communicationUnits_add (left right : ResourceCounts) :
    (left + right).communicationUnits =
      left.communicationUnits + right.communicationUnits := rfl

/-- One ordinary real-RAM instruction. -/
def localStep : ResourceCounts := ⟨1, 0, 0, 0, 0⟩

/-- A block of ordinary real-RAM instructions.  The strict machine uses this
for operations whose surface syntax is one instruction but whose semantics
transfers a variable number of words. -/
def localSteps (steps : ℕ) : ResourceCounts := ⟨steps, 0, 0, 0, 0⟩

/-- One unit-time oracle invocation. -/
def oracleQuery : ResourceCounts := ⟨1, 1, 0, 0, 0⟩

/-- One oracle invocation together with the RAM work needed to transfer its
argument and answer.  The oracle's internal work is excluded, but a long
answer cannot be installed in RAM in constant local time. -/
def oracleQueryTransfer (argumentWords answerWords : ℕ) : ResourceCounts :=
  ⟨argumentWords + answerWords + 1, 1, 0, 0, 0⟩

/-- One call to a distribution-sampling oracle.  This is distinct from
reading finitely many random bits because an exact real sample may have
continuous support. -/
def distributionSample : ResourceCounts := ⟨1, 0, 1, 0, 0⟩

/-- One sampling-oracle invocation plus the word-transfer cost of its
parameters and returned sample. -/
def distributionSampleTransfer
    (parameterWords sampleWords : ℕ) : ResourceCounts :=
  ⟨parameterWords + sampleWords + 1, 0, 1, 0, 0⟩

/-- Reading `bits` independent random bits, also charged as one local action. -/
def randomness (bits : ℕ) : ResourceCounts := ⟨1, 0, 0, bits, 0⟩

/-- Sending a message of the advertised bit length. -/
def communication (units : ℕ) : ResourceCounts := ⟨1, 0, 0, 0, units⟩

end ResourceCounts

/-- A fully profiled sequential computation. The first component tracks
additive resources; `Cells` tracks peak live memory and net allocation. -/
abbrev ProfiledCost (α : Type u) := CostM (ResourceCounts × Cells) α

namespace ProfiledCost

variable {α : Type u} {β : Type v}

/-- Return a value with no resource charge. -/
def pure (value : α) : ProfiledCost α := CostM.pure value

/-- Charge an arbitrary, auditable resource vector and memory event. -/
def charge (resources : ResourceCounts) (cells : Cells) (value : α) :
    ProfiledCost α := ⟨value, (resources, cells)⟩

/-- One ordinary unit-cost RAM operation. -/
def localOperation (operation : α → β)
    (input : ProfiledCost α) : ProfiledCost β :=
  ⟨operation input.ret, input.cost + (ResourceCounts.localStep, 0)⟩

/-- Invoke an oracle once. Computing the query itself is represented by
`query.cost`; obtaining the answer costs one unit and one query. -/
def oracleCall {Query Answer : Type*} (oracle : Query → Answer)
    (query : ProfiledCost Query) : ProfiledCost Answer :=
  ⟨oracle query.ret, query.cost + (ResourceCounts.oracleQuery, 0)⟩

/-- Draw once from an externally supplied distribution sampler. -/
def sampleCall {Parameter Sample : Type*} (sampler : Parameter → Sample)
    (parameter : ProfiledCost Parameter) : ProfiledCost Sample :=
  ⟨sampler parameter.ret,
    parameter.cost + (ResourceCounts.distributionSample, 0)⟩

/-- Consume supplied random bits and return the deterministic bits they
encode. Probability laws remain separate mathematical data. -/
def consumeRandomBits (bits : List Bool) : ProfiledCost (List Bool) :=
  charge (ResourceCounts.randomness bits.length) 0 bits

/-- Send a bitstring and return it unchanged. -/
def send (message : List Bool) : ProfiledCost (List Bool) :=
  charge (ResourceCounts.communication message.length) 0 message

/-- Send exact unit-cost RAM words.  This is the real-RAM communication
counterpart of `send`; it counts words rather than pretending an exact real
has a finite binary expansion. -/
def sendWords (message : List Word) : ProfiledCost (List Word) :=
  charge (ResourceCounts.communication message.length) 0 message

/-- Allocate live RAM words. -/
def alloc (cells : ℕ) : ProfiledCost PUnit :=
  charge 0 (Cells.alloc cells) ()

/-- Release live RAM words. -/
def free (cells : ℕ) : ProfiledCost PUnit :=
  charge 0 (Cells.free cells) ()

def steps (run : ProfiledCost α) : ℕ := run.cost.1.steps
def oracleQueries (run : ProfiledCost α) : ℕ := run.cost.1.oracleQueries
def distributionSamples (run : ProfiledCost α) : ℕ :=
  run.cost.1.distributionSamples
def randomBits (run : ProfiledCost α) : ℕ := run.cost.1.randomBits
def communicationUnits (run : ProfiledCost α) : ℕ :=
  run.cost.1.communicationUnits
/-- Compatibility projection when each communication unit is specifically one
bit. -/
def communicatedBits (run : ProfiledCost α) : ℕ := communicationUnits run
def peakCells (run : ProfiledCost α) : ℕ := Int.toNat run.cost.2.peak

@[simp] theorem oracleQueries_oracleCall {Query Answer : Type*}
    (oracle : Query → Answer) (query : ProfiledCost Query) :
    oracleQueries (oracleCall oracle query) = oracleQueries query + 1 := rfl

@[simp] theorem distributionSamples_sampleCall {Parameter Sample : Type*}
    (sampler : Parameter → Sample) (parameter : ProfiledCost Parameter) :
    distributionSamples (sampleCall sampler parameter) =
      distributionSamples parameter + 1 := rfl

@[simp] theorem communicatedBits_send (message : List Bool) :
    communicatedBits (send message) = message.length := rfl

@[simp] theorem communicationUnits_sendWords (message : List Word) :
    communicationUnits (sendWords message) = message.length := rfl

@[simp] theorem randomBits_consumeRandomBits (bits : List Bool) :
    randomBits (consumeRandomBits bits) = bits.length := rfl

@[simp] theorem peakCells_alloc (cells : ℕ) :
    peakCells (alloc cells) = cells := by simp [peakCells, alloc, charge]

end ProfiledCost

/-! ## Parallel work and span -/

/-- Work/span pair for fork-join parallel algorithms. Sequential composition
adds both coordinates; parallel composition adds work and takes maximum span. -/
@[ext]
structure WorkSpan where
  work : ℕ
  span : ℕ
  deriving DecidableEq

namespace WorkSpan

instance : Zero WorkSpan := ⟨⟨0, 0⟩⟩
instance : Add WorkSpan :=
  ⟨fun left right =>
    ⟨left.work + right.work, left.span + right.span⟩⟩
instance : AddCommMonoid WorkSpan where
  add_assoc _ _ _ := by ext <;> exact Nat.add_assoc _ _ _
  zero_add _ := by ext <;> exact Nat.zero_add _
  add_zero _ := by ext <;> exact Nat.add_zero _
  add_comm _ _ := by ext <;> exact Nat.add_comm _ _
  nsmul := nsmulRec

/-- Combine independent computations in parallel. -/
def parallel {α : Type u} {β : Type v}
    (left : CostM WorkSpan α) (right : CostM WorkSpan β) :
    CostM WorkSpan (α × β) :=
  ⟨(left.ret, right.ret),
    ⟨left.cost.work + right.cost.work,
      max left.cost.span right.cost.span⟩⟩

end WorkSpan

/-! ## Polynomial bounds -/

/-- A natural-valued cost is uniformly polynomially bounded in the chosen
scalar input size. -/
def IsPolyBound {Input : Type u}
    (sizeOf : Input → ℕ) (cost : Input → ℕ) : Prop :=
  ∃ coefficient exponent : ℕ,
    ∀ input, cost input ≤ coefficient * (sizeOf input + 1) ^ exponent

/-- Aggregate a fixed list of size parameters.  Polynomial bounds in this sum
are the standard multivariate-polynomial interface used by the benchmark. -/
def aggregateSize (sizes : List ℕ) : ℕ := sizes.sum

/-- Polynomial boundedness for a vector of size parameters. -/
def IsPolyBoundInSizes {Input : Type u}
    (sizes : Input → List ℕ) (cost : Input → ℕ) : Prop :=
  IsPolyBound (fun input => aggregateSize (sizes input)) cost

/-- Polynomial boundedness restricted to the valid inputs of a promise
problem.  The constants are uniform over all inputs satisfying `valid`; no
condition is imposed outside the promise. -/
def IsPolyBoundOn {Input : Type u}
    (valid : Input → Prop) (sizeOf : Input → ℕ) (cost : Input → ℕ) : Prop :=
  ∃ coefficient exponent : ℕ,
    ∀ input, valid input →
      cost input ≤ coefficient * (sizeOf input + 1) ^ exponent

/-- Multivariate-size version of `IsPolyBoundOn`. -/
def IsPolyBoundInSizesOn {Input : Type u}
    (valid : Input → Prop) (sizes : Input → List ℕ)
    (cost : Input → ℕ) : Prop :=
  IsPolyBoundOn valid (fun input => aggregateSize (sizes input)) cost

/-- A family of cost-annotated computations itself has polynomial operation
count, independently of whether it is attached to a named mathematical
function. -/
def IsPolyTime {Input : Type u} {Output : Input → Type v}
    (sizeOf : Input → ℕ) (run : (input : Input) → Cost (Output input)) : Prop :=
  IsPolyBound sizeOf (fun input => (run input).ops)

/-- Multivariate-size version of `IsPolyTime`. -/
def IsPolyTimeInSizes {Input : Type u} {Output : Input → Type v}
    (sizes : Input → List ℕ) (run : (input : Input) → Cost (Output input)) : Prop :=
  IsPolyBoundInSizes sizes (fun input => (run input).ops)

namespace IsPolyBound

variable {Input : Type u} {sizeOf : Input → ℕ}

theorem const (n : ℕ) : IsPolyBound sizeOf (fun _ => n) :=
  ⟨n, 0, fun _ => by simp⟩

theorem self : IsPolyBound sizeOf sizeOf :=
  ⟨1, 1, fun input => by simp⟩

theorem of_le {f g : Input → ℕ} (hg : IsPolyBound sizeOf g)
    (hfg : ∀ input, f input ≤ g input) : IsPolyBound sizeOf f := by
  obtain ⟨c, k, hg⟩ := hg
  exact ⟨c, k, fun input => (hfg input).trans (hg input)⟩

theorem add {f g : Input → ℕ} (hf : IsPolyBound sizeOf f)
    (hg : IsPolyBound sizeOf g) :
    IsPolyBound sizeOf (fun input => f input + g input) := by
  obtain ⟨cf, kf, hf⟩ := hf
  obtain ⟨cg, kg, hg⟩ := hg
  refine ⟨cf + cg, max kf kg, fun input => ?_⟩
  have hbase : 1 ≤ sizeOf input + 1 := by omega
  have hpowf :
      (sizeOf input + 1) ^ kf ≤ (sizeOf input + 1) ^ max kf kg :=
    Nat.pow_le_pow_right hbase (le_max_left _ _)
  have hpowg :
      (sizeOf input + 1) ^ kg ≤ (sizeOf input + 1) ^ max kf kg :=
    Nat.pow_le_pow_right hbase (le_max_right _ _)
  calc
    f input + g input
        ≤ cf * (sizeOf input + 1) ^ kf +
            cg * (sizeOf input + 1) ^ kg := Nat.add_le_add (hf input) (hg input)
    _ ≤ cf * (sizeOf input + 1) ^ max kf kg +
          cg * (sizeOf input + 1) ^ max kf kg := by gcongr
    _ = (cf + cg) * (sizeOf input + 1) ^ max kf kg := by ring

theorem mul {f g : Input → ℕ} (hf : IsPolyBound sizeOf f)
    (hg : IsPolyBound sizeOf g) :
    IsPolyBound sizeOf (fun input => f input * g input) := by
  obtain ⟨cf, kf, hf⟩ := hf
  obtain ⟨cg, kg, hg⟩ := hg
  refine ⟨cf * cg, kf + kg, fun input => ?_⟩
  calc
    f input * g input
        ≤ (cf * (sizeOf input + 1) ^ kf) *
            (cg * (sizeOf input + 1) ^ kg) := Nat.mul_le_mul (hf input) (hg input)
    _ = cf * cg * (sizeOf input + 1) ^ (kf + kg) := by
      rw [pow_add]
      ring

end IsPolyBound

/-! ## Loop-composition rules -/

/-- A finite sum is polynomial-time when both its iteration count and a
uniform per-iteration cost bound are polynomial. -/
theorem isPolyTime_sumFinset
    {Input Index Value : Type*} [AddCommMonoid Value]
    {sizeOf : Input → ℕ} {indices : Input → Finset Index}
    {body : (input : Input) → Index → Cost Value}
    {bodyBound : Input → ℕ}
    (hcard : IsPolyBound sizeOf (fun input => (indices input).card))
    (hbodyBound : IsPolyBound sizeOf bodyBound)
    (hbody : ∀ input index, index ∈ indices input →
      (body input index).ops ≤ bodyBound input) :
    IsPolyTime sizeOf
      (fun input => Cost.sumFinset (indices input) (body input)) := by
  show IsPolyBound sizeOf
    (fun input => (Cost.sumFinset (indices input) (body input)).ops)
  have htotal : IsPolyBound sizeOf
      (fun input => (indices input).card * (bodyBound input + 1)) :=
    IsPolyBound.mul hcard
      (IsPolyBound.add hbodyBound (IsPolyBound.const 1))
  refine IsPolyBound.of_le htotal (fun input => ?_)
  have hsum :
      (∑ index ∈ indices input, (body input index).ops) ≤
        ∑ _index ∈ indices input, bodyBound input :=
    Finset.sum_le_sum (fun index hindex => hbody input index hindex)
  calc
    (Cost.sumFinset (indices input) (body input)).ops
        = (∑ index ∈ indices input, (body input index).ops) +
            (indices input).card := rfl
    _ ≤ (∑ _index ∈ indices input, bodyBound input) +
          (indices input).card := Nat.add_le_add_right hsum _
    _ = (indices input).card * bodyBound input +
          (indices input).card := by
      rw [Finset.sum_const]
      simp
    _ = (indices input).card * (bodyBound input + 1) := by ring

/-- Filtering a finite set is polynomial-time under the analogous uniform
predicate-cost and cardinality bounds. -/
theorem isPolyTime_filterFinset
    {Input Index : Type*} [DecidableEq Index]
    {sizeOf : Input → ℕ} {indices : Input → Finset Index}
    {predicate : (input : Input) → Index → Cost Bool}
    {predicateBound : Input → ℕ}
    (hcard : IsPolyBound sizeOf (fun input => (indices input).card))
    (hpredicateBound : IsPolyBound sizeOf predicateBound)
    (hpredicate : ∀ input index, index ∈ indices input →
      (predicate input index).ops ≤ predicateBound input) :
    IsPolyTime sizeOf
      (fun input => Cost.filterFinset (indices input) (predicate input)) := by
  show IsPolyBound sizeOf
    (fun input =>
      (Cost.filterFinset (indices input) (predicate input)).ops)
  have htotal : IsPolyBound sizeOf
      (fun input => (indices input).card * (predicateBound input + 1)) :=
    IsPolyBound.mul hcard
      (IsPolyBound.add hpredicateBound (IsPolyBound.const 1))
  refine IsPolyBound.of_le htotal (fun input => ?_)
  have hsum :
      (∑ index ∈ indices input, (predicate input index).ops) ≤
        ∑ _index ∈ indices input, predicateBound input :=
    Finset.sum_le_sum
      (fun index hindex => hpredicate input index hindex)
  calc
    (Cost.filterFinset (indices input) (predicate input)).ops
        = (∑ index ∈ indices input, (predicate input index).ops) +
            (indices input).card := rfl
    _ ≤ (∑ _index ∈ indices input, predicateBound input) +
          (indices input).card := Nat.add_le_add_right hsum _
    _ = (indices input).card * predicateBound input +
          (indices input).card := by
      rw [Finset.sum_const]
      simp
    _ = (indices input).card * (predicateBound input + 1) := by ring

/-- A stateful fold is polynomial when its list length and a uniform body-cost
bound are polynomial. -/
theorem isPolyTime_foldlList
    {Input Item State : Type*}
    {sizeOf : Input → ℕ} {items : Input → List Item}
    {initial : Input → State}
    {step : (input : Input) → State → Item → Cost State}
    {bodyBound : Input → ℕ}
    (hlength : IsPolyBound sizeOf (fun input => (items input).length))
    (hbodyBound : IsPolyBound sizeOf bodyBound)
    (hstep : ∀ input state item,
      (step input state item).ops ≤ bodyBound input) :
    IsPolyTime sizeOf fun input =>
      Cost.foldlList (step input) (items input) (initial input) := by
  show IsPolyBound sizeOf fun input =>
    (Cost.foldlList (step input) (items input) (initial input)).ops
  apply IsPolyBound.of_le
    (IsPolyBound.mul hlength
      (IsPolyBound.add hbodyBound (IsPolyBound.const 1)))
  intro input
  exact Cost.ops_foldlList_le _ _ _ _ (hstep input)

/-- Mapping an instrumented body over a polynomial-length list preserves
polynomial time. -/
theorem isPolyTime_mapList
    {Input Item Value : Type*}
    {sizeOf : Input → ℕ} {items : Input → List Item}
    {body : (input : Input) → Item → Cost Value}
    {bodyBound : Input → ℕ}
    (hlength : IsPolyBound sizeOf (fun input => (items input).length))
    (hbodyBound : IsPolyBound sizeOf bodyBound)
    (hbody : ∀ input item, (body input item).ops ≤ bodyBound input) :
    IsPolyTime sizeOf fun input => Cost.mapList (body input) (items input) := by
  show IsPolyBound sizeOf fun input =>
    (Cost.mapList (body input) (items input)).ops
  apply IsPolyBound.of_le
    (IsPolyBound.mul hlength
      (IsPolyBound.add hbodyBound (IsPolyBound.const 1)))
  intro input
  rw [Cost.ops_mapList]
  have hsum :
      ((items input).map fun item => (body input item).ops).sum ≤
        (items input).length * bodyBound input := by
    calc
      ((items input).map fun item => (body input item).ops).sum
          ≤ ((items input).map fun _ => bodyBound input).sum := by
              exact List.sum_le_sum fun item _ => hbody input item
      _ = (items input).length * bodyBound input := by simp
  calc
    ((items input).map fun item => (body input item).ops).sum +
          (items input).length
        ≤ (items input).length * bodyBound input +
            (items input).length := Nat.add_le_add_right hsum _
    _ = (items input).length * (bodyBound input + 1) := by ring

/-- A polynomially bounded counted iteration with polynomially bounded body
cost is polynomial. -/
theorem isPolyTime_iterate
    {Input State : Type*} {sizeOf : Input → ℕ}
    {iterations bodyBound : Input → ℕ}
    {step : (input : Input) → State → Cost State}
    {initial : Input → State}
    (hiterations : IsPolyBound sizeOf iterations)
    (hbodyBound : IsPolyBound sizeOf bodyBound)
    (hstep : ∀ input state, (step input state).ops ≤ bodyBound input) :
    IsPolyTime sizeOf fun input =>
      Cost.iterate (iterations input) (step input) (initial input) := by
  show IsPolyBound sizeOf fun input =>
    (Cost.iterate (iterations input) (step input) (initial input)).ops
  apply IsPolyBound.of_le
    (IsPolyBound.mul hiterations
      (IsPolyBound.add hbodyBound (IsPolyBound.const 1)))
  intro input
  exact Cost.ops_iterate_le _ _ _ _ (hstep input)

/-- Dependent-state version of `isPolyTime_iterate`.  This is needed for
algorithms whose arrays, vertices, or certificates have a type indexed by an
input size, such as a state over `Fin input.vertexCount`. -/
theorem isPolyTime_dependentIterate
    {Input : Type u} {State : Input → Type v} {sizeOf : Input → ℕ}
    {iterations bodyBound : Input → ℕ}
    {step : (input : Input) → State input → Cost (State input)}
    {initial : (input : Input) → State input}
    (hiterations : IsPolyBound sizeOf iterations)
    (hbodyBound : IsPolyBound sizeOf bodyBound)
    (hstep : ∀ input state, (step input state).ops ≤ bodyBound input) :
    IsPolyTime sizeOf fun input =>
      Cost.iterate (iterations input) (step input) (initial input) := by
  show IsPolyBound sizeOf fun input =>
    (Cost.iterate (iterations input) (step input) (initial input)).ops
  apply IsPolyBound.of_le
    (IsPolyBound.mul hiterations
      (IsPolyBound.add hbodyBound (IsPolyBound.const 1)))
  intro input
  exact Cost.ops_iterate_le _ _ _ _ (hstep input)

/-- The corresponding composition theorem for total fuelled while loops. -/
theorem isPolyTime_whileFuel
    {Input State : Type*} {sizeOf : Input → ℕ}
    {fuel conditionBound bodyBound : Input → ℕ}
    {condition : (input : Input) → State → Cost Bool}
    {body : (input : Input) → State → Cost State}
    {initial : Input → State}
    (hfuel : IsPolyBound sizeOf fuel)
    (hconditionBound : IsPolyBound sizeOf conditionBound)
    (hbodyBound : IsPolyBound sizeOf bodyBound)
    (hcondition : ∀ input state,
      (condition input state).ops ≤ conditionBound input)
    (hbody : ∀ input state,
      (body input state).ops ≤ bodyBound input) :
    IsPolyTime sizeOf fun input =>
      Cost.whileFuel (fuel input) (condition input) (body input)
        (initial input) := by
  show IsPolyBound sizeOf fun input =>
    (Cost.whileFuel (fuel input) (condition input) (body input)
      (initial input)).ops
  have hperIteration : IsPolyBound sizeOf fun input =>
      conditionBound input + bodyBound input + 1 :=
    IsPolyBound.add (IsPolyBound.add hconditionBound hbodyBound)
      (IsPolyBound.const 1)
  apply IsPolyBound.of_le (IsPolyBound.mul hfuel hperIteration)
  intro input
  exact Cost.ops_whileFuel_le _ _ _ _ _ _
    (hcondition input) (hbody input)

/-! ## Generic function interfaces -/

/-- A unit-cost RAM implementation of an arbitrary dependent Lean function.
The output type may depend on the input. -/
structure CostedImplementation
    {Input : Type u} {Output : Input → Type v}
    (function : (input : Input) → Output input) where
  run : (input : Input) → Cost (Output input)
  correct : ∀ input, (run input).value = function input

/-- A costed implementation that is required to agree with a mathematical
function only on inputs satisfying a promise.  The implementation remains
total as a Lean function, but its behavior outside `valid` is irrelevant. -/
structure CostedImplementationOn
    {Input : Type u} {Output : Input → Type v}
    (valid : Input → Prop)
    (function : (input : Input) → Output input) where
  run : (input : Input) → Cost (Output input)
  correct : ∀ input, valid input → (run input).value = function input

/-- A costed solver for a dependent search relation.  Unlike
`CostedImplementation`, correctness need not single out a canonical output. -/
structure CostedSearchImplementation
    {Input : Type u} {Output : Input → Type v}
    (solution : (input : Input) → Output input → Prop) where
  run : (input : Input) → Cost (Output input)
  correct : ∀ input, solution input (run input).value

/-- The supplied implementation runs in polynomially many unit-cost
operations. -/
def CostedImplementation.IsPolynomial
    {Input : Type u} {Output : Input → Type v}
    {function : (input : Input) → Output input}
    (implementation : CostedImplementation function)
    (sizeOf : Input → ℕ) : Prop :=
  IsPolyBound sizeOf (fun input => (implementation.run input).ops)

/-- The same predicate with several named size parameters. -/
def CostedImplementation.IsPolynomialInSizes
    {Input : Type u} {Output : Input → Type v}
    {function : (input : Input) → Output input}
    (implementation : CostedImplementation function)
    (sizes : Input → List ℕ) : Prop :=
  IsPolyBoundInSizes sizes (fun input => (implementation.run input).ops)

/-- Polynomial operation count for a promise-preserving implementation. -/
def CostedImplementationOn.IsPolynomial
    {Input : Type u} {Output : Input → Type v}
    {valid : Input → Prop} {function : (input : Input) → Output input}
    (implementation : CostedImplementationOn valid function)
    (sizeOf : Input → ℕ) : Prop :=
  IsPolyBoundOn valid sizeOf (fun input => (implementation.run input).ops)

/-- Multivariate-size version of `CostedImplementationOn.IsPolynomial`. -/
def CostedImplementationOn.IsPolynomialInSizes
    {Input : Type u} {Output : Input → Type v}
    {valid : Input → Prop} {function : (input : Input) → Output input}
    (implementation : CostedImplementationOn valid function)
    (sizes : Input → List ℕ) : Prop :=
  IsPolyBoundInSizesOn valid sizes
    (fun input => (implementation.run input).ops)

/-- Polynomial operation count for a search-relation solver. -/
def CostedSearchImplementation.IsPolynomial
    {Input : Type u} {Output : Input → Type v}
    {solution : (input : Input) → Output input → Prop}
    (implementation : CostedSearchImplementation solution)
    (sizeOf : Input → ℕ) : Prop :=
  IsPolyBound sizeOf (fun input => (implementation.run input).ops)

/-- Multivariate-size version of `CostedSearchImplementation.IsPolynomial`. -/
def CostedSearchImplementation.IsPolynomialInSizes
    {Input : Type u} {Output : Input → Type v}
    {solution : (input : Input) → Output input → Prop}
    (implementation : CostedSearchImplementation solution)
    (sizes : Input → List ℕ) : Prop :=
  IsPolyBoundInSizes sizes (fun input => (implementation.run input).ops)

/-- Legacy trusted-instrumentation predicate for an arbitrary dependent
function.  This says that a supplied `CostM` annotation is polynomial; it does
*not* by itself establish instruction-level RAM computability.  Complexity
class statements should use the fixed-encoding strict machine interface. -/
def RunsInPolynomialTime
    {Input : Type u} {Output : Input → Type v}
    (sizeOf : Input → ℕ) (function : (input : Input) → Output input) : Prop :=
  ∃ implementation : CostedImplementation function,
    implementation.IsPolynomial sizeOf

/-- Multivariate-size version of `RunsInPolynomialTime`. -/
def RunsInPolynomialTimeInSizes
    {Input : Type u} {Output : Input → Type v}
    (sizes : Input → List ℕ) (function : (input : Input) → Output input) : Prop :=
  ∃ implementation : CostedImplementation function,
    implementation.IsPolynomialInSizes sizes

/-- Promise-restricted legacy trusted-instrumentation predicate. -/
def RunsInPolynomialTimeOn
    {Input : Type u} {Output : Input → Type v}
    (valid : Input → Prop) (sizeOf : Input → ℕ)
    (function : (input : Input) → Output input) : Prop :=
  ∃ implementation : CostedImplementationOn valid function,
    implementation.IsPolynomial sizeOf

/-- Multivariate-size version of `RunsInPolynomialTimeOn`. -/
def RunsInPolynomialTimeInSizesOn
    {Input : Type u} {Output : Input → Type v}
    (valid : Input → Prop) (sizes : Input → List ℕ)
    (function : (input : Input) → Output input) : Prop :=
  ∃ implementation : CostedImplementationOn valid function,
    implementation.IsPolynomialInSizes sizes

/-- Legacy trusted-instrumentation predicate for a dependent search solver.
Use `StrictRAMSearchableInPolyTime` for machine-enforced search complexity. -/
def SearchRunsInPolynomialTime
    {Input : Type u} {Output : Input → Type v}
    (sizeOf : Input → ℕ)
    (solution : (input : Input) → Output input → Prop) : Prop :=
  ∃ implementation : CostedSearchImplementation solution,
    implementation.IsPolynomial sizeOf

/-- Multivariate-size version of `SearchRunsInPolynomialTime`. -/
def SearchRunsInPolynomialTimeInSizes
    {Input : Type u} {Output : Input → Type v}
    (sizes : Input → List ℕ)
    (solution : (input : Input) → Output input → Prop) : Prop :=
  ∃ implementation : CostedSearchImplementation solution,
    implementation.IsPolynomialInSizes sizes

/-- Convenience wrapper for an ordinary two-argument function. -/
def RunsInPolynomialTime₂
    {α : Type u} {β : Type v} {γ : Type w}
    (sizeOf : α × β → ℕ) (function : α → β → γ) : Prop :=
  RunsInPolynomialTime sizeOf (fun input => function input.1 input.2)

/-- Uniform polynomial bound in the presence of an adversarial seed, oracle,
or execution path.  The polynomial constants cannot depend on that auxiliary
choice. -/
def IsUniformPolyBound
    {Input : Type u} {Choice : Input → Type v}
    (sizeOf : Input → ℕ)
    (cost : (input : Input) → Choice input → ℕ) : Prop :=
  ∃ coefficient exponent : ℕ,
    ∀ input choice,
      cost input choice ≤ coefficient * (sizeOf input + 1) ^ exponent

/-- Multivariate-size version of `IsUniformPolyBound`.  It is appropriate for
worst-case bounds over random seeds, legal oracle implementations,
tie-breaking rules, or execution paths. -/
def IsUniformPolyBoundInSizes
    {Input : Type u} {Choice : Input → Type v}
    (sizes : Input → List ℕ)
    (cost : (input : Input) → Choice input → ℕ) : Prop :=
  IsUniformPolyBound (fun input => aggregateSize (sizes input)) cost

/-- Uniform polynomial boundedness restricted to legal auxiliary choices.
This is the appropriate interface for promise oracles, valid transcripts, and
other adversarial choices whose legality may depend on the ordinary input. -/
def IsUniformPolyBoundOn
    {Input : Type u} {Choice : Input → Type v}
    (valid : (input : Input) → Choice input → Prop)
    (sizeOf : Input → ℕ)
    (cost : (input : Input) → Choice input → ℕ) : Prop :=
  ∃ coefficient exponent : ℕ,
    ∀ input choice, valid input choice →
      cost input choice ≤
        coefficient * (sizeOf input + 1) ^ exponent

/-- Multivariate-size version of `IsUniformPolyBoundOn`. -/
def IsUniformPolyBoundInSizesOn
    {Input : Type u} {Choice : Input → Type v}
    (valid : (input : Input) → Choice input → Prop)
    (sizes : Input → List ℕ)
    (cost : (input : Input) → Choice input → ℕ) : Prop :=
  IsUniformPolyBoundOn valid
    (fun input => aggregateSize (sizes input)) cost

/-- A costed implementation with an auxiliary choice such as a random seed,
an oracle, or an adversarial tie-breaking rule.  The output type may depend on
both the input and that choice. -/
structure CostedImplementationWithChoice
    {Input : Type u} {Choice : Input → Type v}
    {Output : (input : Input) → Choice input → Type w}
    (function : (input : Input) →
      (choice : Choice input) → Output input choice) where
  /-- Every input has at least one legal execution choice, preventing
  correctness and complexity claims from becoming vacuous. -/
  choice_nonempty : ∀ input, Nonempty (Choice input)
  run : (input : Input) →
    (choice : Choice input) → Cost (Output input choice)
  correct : ∀ input choice,
    (run input choice).value = function input choice

/-- Worst-case polynomial operation count, uniform over the auxiliary
choice.  In particular, the polynomial constants cannot depend on a seed or
oracle. -/
def CostedImplementationWithChoice.IsPolynomial
    {Input : Type u} {Choice : Input → Type v}
    {Output : (input : Input) → Choice input → Type w}
    {function : (input : Input) →
      (choice : Choice input) → Output input choice}
    (implementation : CostedImplementationWithChoice function)
    (sizeOf : Input → ℕ) : Prop :=
  IsUniformPolyBound sizeOf
    (fun input choice => (implementation.run input choice).ops)

/-- Multivariate-size version of
`CostedImplementationWithChoice.IsPolynomial`. -/
def CostedImplementationWithChoice.IsPolynomialInSizes
    {Input : Type u} {Choice : Input → Type v}
    {Output : (input : Input) → Choice input → Type w}
    {function : (input : Input) →
      (choice : Choice input) → Output input choice}
    (implementation : CostedImplementationWithChoice function)
    (sizes : Input → List ℕ) : Prop :=
  IsUniformPolyBoundInSizes sizes
    (fun input choice => (implementation.run input choice).ops)

/-- A function with a seed/oracle/adversarial choice has a unit-cost RAM
implementation whose worst-case running time is polynomial uniformly over
that choice. -/
def RunsInPolynomialTimeUniformly
    {Input : Type u} {Choice : Input → Type v}
    {Output : (input : Input) → Choice input → Type w}
    (sizeOf : Input → ℕ)
    (function : (input : Input) →
      (choice : Choice input) → Output input choice) : Prop :=
  ∃ implementation : CostedImplementationWithChoice function,
    implementation.IsPolynomial sizeOf

/-- Multivariate-size version of `RunsInPolynomialTimeUniformly`. -/
def RunsInPolynomialTimeInSizesUniformly
    {Input : Type u} {Choice : Input → Type v}
    {Output : (input : Input) → Choice input → Type w}
    (sizes : Input → List ℕ)
    (function : (input : Input) →
      (choice : Choice input) → Output input choice) : Prop :=
  ∃ implementation : CostedImplementationWithChoice function,
    implementation.IsPolynomialInSizes sizes

/-- A concrete query-count function is polynomially bounded. -/
abbrev UsesPolynomiallyManyQueries := @IsPolyBound

/-- A concrete communication-bit count is polynomially bounded. -/
abbrev UsesPolynomialCommunication := @IsPolyBound

/-! ## Small checked example -/

def sumOfSquares (n : ℕ) : ℕ := ∑ i ∈ Finset.range n, i * i

def sumOfSquaresCost (n : ℕ) : Cost ℕ :=
  Cost.sumFinset (Finset.range n)
    (fun i => Cost.mul (Cost.pure i) (Cost.pure i))

def sumOfSquaresImplementation : CostedImplementation sumOfSquares where
  run := sumOfSquaresCost
  correct := fun _ => rfl

theorem sumOfSquaresImplementation_isPolynomial :
    sumOfSquaresImplementation.IsPolynomial (fun n => n) := by
  refine ⟨2, 1, fun n => ?_⟩
  simp [sumOfSquaresImplementation, sumOfSquaresCost,
    Cost.sumFinset, Cost.mul, Cost.liftBinary, Cost.pure, CostM.pure]
  omega

end EconCSLib.OpenProblem.UnitCostRAM
