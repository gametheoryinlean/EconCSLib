/-
Copyright (c) 2025 Sorrachai Yingchareonthawornhcai. All rights reserved.
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Adapted from `TimeM` in the `leanprover/cslib` project, file
`Cslib/Algorithms/Lean/TimeM.lean` (Apache 2.0). The monad core,
`Pure`/`Bind`/`Functor`/`Seq` instances, `Monad`/`LawfulMonad`
instances, `tick`, and the `✓` notation closely follow the upstream
design. Modifications by EconCSLib contributors (generalization from
time to general cost monoids; `par`/`parList`; `Bounded`/`IsPolyBounded`
predicates; `CoeHead` projection).

Original authors:    Sorrachai Yingchareonthawornhcai, Eric Wieser
Upstream:            https://github.com/leanprover/cslib
Pinned upstream rev: c7944a9fb44c3298f1a960a5e574ab23a6ab8ed5
Upstream file:       Cslib/Algorithms/Lean/TimeM.lean
-/

import Mathlib.Algebra.Group.Defs
import Mathlib.Order.Lattice
import Mathlib.Order.BoundedOrder.Basic

/-!
# EconCSLib.Foundation.CostM

`CostM C A` is the writer monad over an arbitrary additive monoid `C`: a value of
type `A` together with an accumulated cost in `C`. Sequential composition
(`>>=`) adds the cost components via the monoid operation.

## Design

The cost type `C` is deliberately abstract. Picking `C` is what selects *which*
resource is being measured; the monad itself is the same for all of them.

* `C := ℕ` — count comparisons, recursive calls, or any single additive
  resource. This is the conventional "time complexity" instance.
* `C := A × B` — track two costs at once. `Prod.instAddMonoid` makes this
  automatic; no extra wiring needed.
* `C := Finset A` with `+ := (· ∪ ·)`, `0 := ∅` — track the **set** of
  subproblems touched by a recursive algorithm. The monoid is *idempotent*
  (`s + s = s`); this is the algebraic shadow of memoization.
* `C := { c : ℕ × ℤ // c.2 ≤ c.1 }` (peak/delta) — a non-additive monoid for
  **peak** memory. This is the only resource shape that additive cost
  fundamentally cannot express.

The structure field is `cost`, not `time`: time is one cost among many and
has no architectural privilege.

This is the standard writer-monad-over-a-monoid pattern; see Danielsson,
*Lightweight Semiformal Time Complexity Analysis for Purely Functional Data
Structures* (POPL 2008).

## Discipline

Cost annotations are **trusted**: the elaborator does not check that `tick`
calls correspond to actual work. Each algorithm file must document its cost
model — what counts as a unit, what is free, whether recursive calls are
charged — and the author must `tick` accordingly.

Proofs separate cleanly:

* Functional correctness lives on `m.ret` (alias `⟪m⟫`).
* Complexity bounds live on `m.cost`.

The two are independent: changing the cost model never disturbs correctness
proofs, and refactoring the algorithm preserves cost annotations by
construction.

## Main definitions

* `CostM C A` — the monad.
* `CostM.pure`, `CostM.bind`, `CostM.tick` — primitives.
* `Monad (CostM C)` for `[Zero C] [Add C]`.
* `LawfulMonad (CostM C)` for `[AddMonoid C]`.
* `CostM.par` — independent (parallel) composition; cost combined via `⊔`.
  Requires `[SemilatticeSup C]`.
* `CostM.Bounded` / `CostM.IsPolyBounded` — bound predicates over `[LE C]`
  (and the `C = ℕ` polynomial specialization).

## Notation

* `tick c` — charge cost `c`.
* `✓[c] body` — sugar for `do tick c; body` inside a `do`-block.
* `✓ body` — `✓[1] body`; requires `[OfNat C 1]` at the use site.
* implicit coercion `(m : A)` — a `Coe (CostM C A) A` instance projects
  `m.ret`. Use the `.cost` field explicitly to get the cost.

## Attribution

The monad core of this file is **adapted from `TimeM`** in the
[`leanprover/cslib`](https://github.com/leanprover/cslib) project,
file [`Cslib/Algorithms/Lean/TimeM.lean`][upstream] (Apache License 2.0).

[upstream]: https://github.com/leanprover/cslib/blob/c7944a9fb44c3298f1a960a5e574ab23a6ab8ed5/Cslib/Algorithms/Lean/TimeM.lean

Original authors of `TimeM`: **Sorrachai Yingchareonthawornhcai** and
**Eric Wieser**. Original copyright © 2025 Sorrachai Yingchareonthawornhcai.

### What is adapted from upstream

* the `structure CostM` layout (`ret`, accumulated-cost field) ↔ `TimeM` (`ret`, `time`);
* `protected def pure` / `protected def bind` and the matching
  `instance : Pure / Bind / Functor / Seq` typeclass instances;
* `instance : Monad` and `instance : LawfulMonad`;
* the `simp`-lemma layout for `ret_*` / `cost_*` projections;
* `def tick`, the `✓[c] body` and `✓ body` doElem macros;
* the writer-over-additive-monoid design pattern and the Danielsson
  POPL 2008 reference.

### What is added in this file (not upstream as of the pinned commit)

* **Generalization of vocabulary** from "time" to "cost"; the field is
  `cost`, the type parameter is `C`. This makes room for cost shapes
  that are not time — set-of-cells-touched (`Visited`, idempotent
  monoid), peak / delta memory (`Cells`, tropical monoid), product
  costs (work × depth), etc.
* `def par` (binary parallel composition) and `def parList` (n-ary
  parallel composition over `List`), with cost combined via the
  semilattice join `⊔`; corresponding `simp` lemmas.
* The complexity-bound predicates `Bounded` and `IsPolyBounded` over
  `[LE C]` and `C = ℕ` respectively.
* `instance instCoeHead : CoeHead (CostM C A) A` projecting `m.ret`,
  giving `(m : A)` shorthand at use sites.
* Companion modules `Foundation/CostM/Cells.lean` (tropical / peak
  memory) and `Foundation/CostM/Visited.lean` (idempotent / footprint).
-/

/-- Writer monad over an arbitrary additive monoid `C`.

A `CostM C A` is a return value of type `A` together with an accumulated cost
in `C`. The `cost` field aggregates via `+` and `0` of `C`. See the file
docstring for the design rationale and for the choices of `C` that recover
specific complexity measures. -/
@[ext]
structure CostM (C : Type*) (A : Type*) where
  /-- The result of the computation. -/
  ret  : A
  /-- The accumulated cost in `C`. -/
  cost : C

namespace CostM

universe u
variable {C : Type*} {A B : Type u}

/-- Lift a pure value at zero cost. -/
protected def pure [Zero C] (a : A) : CostM C A := ⟨a, 0⟩

instance instPure [Zero C] : Pure (CostM C) := ⟨CostM.pure⟩

/-- Sequential composition. The cost of `m >>= f` is `m.cost + (f m.ret).cost`. -/
protected def bind [Add C] (m : CostM C A) (f : A → CostM C B) : CostM C B :=
  let r := f m.ret
  ⟨r.ret, m.cost + r.cost⟩

instance instBind [Add C] : Bind (CostM C) := ⟨CostM.bind⟩

instance instFunctor : Functor (CostM C) where
  map f x := ⟨f x.ret, x.cost⟩

instance instSeq [Add C] : Seq (CostM C) where
  seq f x := ⟨f.ret (x ()).ret, f.cost + (x ()).cost⟩

instance instSeqLeft [Add C] : SeqLeft (CostM C) where
  seqLeft x y := ⟨x.ret, x.cost + (y ()).cost⟩

instance instSeqRight [Add C] : SeqRight (CostM C) where
  seqRight x y := ⟨(y ()).ret, x.cost + (y ()).cost⟩

instance instMonad [Zero C] [Add C] : Monad (CostM C) where
  pure := Pure.pure
  bind := Bind.bind
  map := Functor.map
  seq := Seq.seq
  seqLeft := SeqLeft.seqLeft
  seqRight := SeqRight.seqRight

/-! ### `simp` lemmas — return component -/

@[simp] theorem ret_pure [Zero C] (a : A) : (pure a : CostM C A).ret = a := rfl

@[simp] theorem ret_bind [Add C] (m : CostM C A) (f : A → CostM C B) :
    (m >>= f).ret = (f m.ret).ret := rfl

@[simp] theorem ret_map (f : A → B) (x : CostM C A) :
    (f <$> x).ret = f x.ret := rfl

@[simp] theorem ret_seqLeft [Add C] (x : CostM C A) (y : Unit → CostM C B) :
    (SeqLeft.seqLeft x y).ret = x.ret := rfl

@[simp] theorem ret_seqRight [Add C] (x : CostM C A) (y : Unit → CostM C B) :
    (SeqRight.seqRight x y).ret = (y ()).ret := rfl

@[simp] theorem ret_seq [Add C] (f : CostM C (A → B)) (x : Unit → CostM C A) :
    (Seq.seq f x).ret = f.ret (x ()).ret := rfl

/-! ### `simp` lemmas — cost component -/

@[simp] theorem cost_pure [Zero C] (a : A) : (pure a : CostM C A).cost = 0 := rfl

@[simp] theorem cost_bind [Add C] (m : CostM C A) (f : A → CostM C B) :
    (m >>= f).cost = m.cost + (f m.ret).cost := rfl

@[simp] theorem cost_map (f : A → B) (x : CostM C A) :
    (f <$> x).cost = x.cost := rfl

@[simp] theorem cost_seqLeft [Add C] (x : CostM C A) (y : Unit → CostM C B) :
    (SeqLeft.seqLeft x y).cost = x.cost + (y ()).cost := rfl

@[simp] theorem cost_seqRight [Add C] (x : CostM C A) (y : Unit → CostM C B) :
    (SeqRight.seqRight x y).cost = x.cost + (y ()).cost := rfl

@[simp] theorem cost_seq [Add C] (f : CostM C (A → B)) (x : Unit → CostM C A) :
    (Seq.seq f x).cost = f.cost + (x ()).cost := rfl

/-- `CostM C` is a lawful monad whenever `C` is an additive monoid. -/
instance instLawfulMonad [AddMonoid C] : LawfulMonad (CostM C) := .mk'
  (id_map := fun _ => rfl)
  (pure_bind := fun _ _ => by ext <;> simp)
  (bind_assoc := fun _ _ _ => by ext <;> simp [add_assoc])
  (seqLeft_eq := fun _ _ => by ext <;> simp)
  (bind_pure_comp := fun _ _ => by ext <;> simp)

/-! ### `tick` and notation -/

/-- Charge a cost of `c`, returning unit. Use inside a `do`-block. -/
def tick (c : C) : CostM C PUnit := ⟨.unit, c⟩

@[simp] theorem ret_tick (c : C) : (tick c).ret = () := rfl
@[simp] theorem cost_tick (c : C) : (tick c).cost = c := rfl

/-- `✓[c] body` adds a cost of `c` and then runs `body`. -/
macro "✓[" c:term "]" body:doElem : doElem =>
  `(doElem| do CostM.tick $c; $body:doElem)

/-- `✓ body` is `✓[1] body`. The use site must provide `[OfNat C 1]`. -/
macro "✓" body:doElem : doElem => `(doElem| ✓[1] $body)

/-- Coerce a `CostM C A` to its return value, dropping the cost. Use this in
contexts where the expected type is `A`; pair with `.cost` for complexity
proofs. The pattern mirrors `Subtype.val`-style projection. -/
instance instCoeHead : CoeHead (CostM C A) A := ⟨CostM.ret⟩

/-! ### Parallel composition

`par m₁ m₂` runs two independent `CostM` computations side by side; the cost
is combined via `⊔` (sup). This is **not** a monadic operation — neither
operand's value feeds into the other. Use this only when the two sides are
data-independent.

The choice of `⊔` for the cost models the "depth" / branch-worst-case view:
both branches run concurrently, so the joint cost is the worse of the two.
For combined work-and-depth tracking (cost type `ℕ × ℕ` with `+` on work and
`⊔` on depth), a custom combining function per cost type is required; this
file does not provide it. -/

/-- Independent (parallel) composition of two `CostM` computations. The
return is the pair of return values; the cost is the sup of the two costs. -/
def par [SemilatticeSup C] (m₁ : CostM C A) (m₂ : CostM C B) : CostM C (A × B) :=
  ⟨(m₁.ret, m₂.ret), m₁.cost ⊔ m₂.cost⟩

@[simp] theorem ret_par [SemilatticeSup C] (m₁ : CostM C A) (m₂ : CostM C B) :
    (par m₁ m₂).ret = (m₁.ret, m₂.ret) := rfl

@[simp] theorem cost_par [SemilatticeSup C] (m₁ : CostM C A) (m₂ : CostM C B) :
    (par m₁ m₂).cost = m₁.cost ⊔ m₂.cost := rfl

/-! ### N-ary parallel composition

`parList ms` extends `par` from a binary combinator to an arbitrary `List` of
operands. All operands run independently (no data dependency between them);
returns are collected into a `List`; costs are combined by the sup-semilattice
join (`⊔`). The empty list has cost `⊥` (`= 0` for `C = ℕ`).

`parList` requires `[OrderBot C]` in addition to `[SemilatticeSup C]` because
the empty list needs an identity element for `⊔`.

For `n` independent operations each charging `c_i`, the joint parallel cost is
`c_1 ⊔ c_2 ⊔ ⋯ ⊔ c_n` (the max for `C = ℕ`). This corresponds to a flat
"fan-out / fan-in" depth-1 schedule with `n` workers. -/

/-- N-ary parallel composition over a `List` of independent `CostM`
operands. Returns are paired into a list in the original order; the cost is
the sup of all operand costs (or `⊥` for the empty list). -/
def parList [SemilatticeSup C] [OrderBot C] (ms : List (CostM C A)) :
    CostM C (List A) :=
  ⟨ms.map (·.ret), ms.foldr (fun m acc => m.cost ⊔ acc) ⊥⟩

@[simp] theorem ret_parList [SemilatticeSup C] [OrderBot C]
    (ms : List (CostM C A)) :
    (parList ms).ret = ms.map (·.ret) := rfl

@[simp] theorem cost_parList [SemilatticeSup C] [OrderBot C]
    (ms : List (CostM C A)) :
    (parList ms).cost = ms.foldr (fun m acc => m.cost ⊔ acc) ⊥ := rfl

@[simp] theorem parList_nil [SemilatticeSup C] [OrderBot C] :
    (parList ([] : List (CostM C A))) = ⟨[], ⊥⟩ := rfl

@[simp] theorem cost_parList_cons [SemilatticeSup C] [OrderBot C]
    (m : CostM C A) (ms : List (CostM C A)) :
    (parList (m :: ms)).cost = m.cost ⊔ (parList ms).cost := rfl

/-! ### Complexity bound predicates

`Bounded alg size bound` says "for every input `i`, the cost of `alg i` is at
most `bound (size i)`". The `size` function reduces the input to a natural
number (the conventional complexity-theoretic notion of "input size"). The
`bound` function maps that size to an expected cost in `C`.

`IsPolyBounded` specializes to `C = ℕ` and existentially quantifies over the
polynomial coefficient and degree: `∃ c k, cost ≤ c * size^k`. -/

/-- The cost of `alg i` is bounded by `bound (size i)` for every input `i`. -/
def Bounded {Input Output : Type*} [LE C]
    (alg : Input → CostM C Output) (size : Input → ℕ) (bound : ℕ → C) : Prop :=
  ∀ i, (alg i).cost ≤ bound (size i)

/-- Specialization of `Bounded` for `C = ℕ`: cost is polynomial in input size. -/
def IsPolyBounded {Input Output : Type*}
    (alg : Input → CostM ℕ Output) (size : Input → ℕ) : Prop :=
  ∃ c k, Bounded alg size (fun n => c * n^k)

end CostM
