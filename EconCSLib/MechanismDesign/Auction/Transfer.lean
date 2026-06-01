/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.MechanismDesign.Auction.MechBasic

/-!
# EconCSLib.MechanismDesign.Auction.Transfer

Mechanisms with monetary transfers.

## Design

This file separates the roles that were previously collapsed into one scalar type:

- `T i` — report/type space for agent `i`
- `A` — allocation space
- `P` — payment space
- `V` — valuation type
- `U` — utility type

The transfer mechanism itself stores only an allocation rule and a payment rule.
Utility construction is external: quasi-linearity is one important specialization,
but it is not baked into the most general structure.

## Structure hierarchy

```
Mechanism I T O                                  -- outcome-only direct mechanism
  └─ MechanismWithTransfers I T A P              -- allocation + payment rules
       └─ SingleParameterMechanism I R           -- T i = R, A = I → R, P = R

MechanismWithTransfers I (fun _ => A → V) A P    -- valuation reports over A
  └─ MultipleParameterMechanism I A V P          -- named multiple-parameter layer
```

## Main definitions

* `MechanismWithTransfers` — allocation rule + payment rule
* `MechanismWithTransfers.quasiLinearUtility` — utility induced by a value extractor
  and payment embedding
* `SingleParameterMechanism` — scalar reports, scalar-vector allocations, scalar payments
* `MultipleParameterMechanism` — valuation-function reports over an allocation space
* `MechanismWithTransfers.toMechanism` — forget the decomposition
* `MechanismWithTransfers.toStrategicGame` — induced strategic game under external utility
* `MechanismWithTransfers.isDSIC` — DSIC specialized to the induced game
* `MechanismWithTransfers.isExPostIR` — ex-post IR specialized to the induced game

## References

* [Nisan et al., *Algorithmic Game Theory*, Ch. 9]
* [Maschler, Solan, Zamir, *Game Theory*, Ch. 11–12]
-/

/-- A mechanism with monetary transfers.

  - `I` — agents
  - `T` — report/type space of each agent
  - `A` — allocation space
  - `P` — payment space

  The mechanism stores only how reports determine allocations and payments.
  Utility is imposed later, for example by quasi-linear utility or some richer
  domain-specific construction. -/
structure MechanismWithTransfers
    (I : Type*) (T : I → Type*) (A : Type*) (P : Type*) where
  /-- The allocation rule: given reports, choose an allocation. -/
  allocationRule : (∀ i, T i) → A
  /-- The payment rule: given reports, determine each agent's payment. -/
  paymentRule : (∀ i, T i) → I → P

namespace MechanismWithTransfers

variable {I : Type*} [DecidableEq I] {T : I → Type*} {A P V U : Type*}
variable (M : MechanismWithTransfers I T A P)

/-- Quasi-linear utility induced by:
  - a valuation function on allocations
  - an embedding of payments into utility space
  - subtraction in the utility space

  This permits, for example:
  - `V = U` with identity payment embedding
  - valuation codomains and payment codomains that differ but both map into `U`. -/
def quasiLinearUtility [Sub U]
    (val : A → (∀ i, T i) → I → V)
    (valueToUtility : V → U) (paymentToUtility : P → U)
    (r : ∀ i, T i) (trueTypes : ∀ i, T i) (i : I) : U :=
  valueToUtility (val (M.allocationRule r) trueTypes i) -
    paymentToUtility (M.paymentRule r i)

/-- Viewing `MechanismWithTransfers` as a general `Mechanism`.

  The outcome type is `A × (I → P)` (allocation, payment vector). -/
def toMechanism :
    Mechanism I T (A × (I → P)) where
  outcome r := (M.allocationRule r, M.paymentRule r)

/-- The strategic game induced by a transfer mechanism and an external utility rule.

  Utility is supplied as a function of:
  - allocation
  - payment vector
  - true type profile
  - agent index -/
def toStrategicGame
    (u : A → (I → P) → (∀ i, T i) → I → U)
    (trueTypes : ∀ i, T i) : StrategicGame I U where
  strategy := T
  payoff r i := u (M.allocationRule r) (M.paymentRule r) trueTypes i

/-- DSIC for a mechanism with transfers, relative to an externally supplied utility rule. -/
def isDSIC [Preorder U]
    (u : A → (I → P) → (∀ i, T i) → I → U) : Prop :=
  ∀ trueTypes : (∀ i, T i), ∀ i : I,
    IsWeaklyDominant (M.toStrategicGame u trueTypes) i (trueTypes i)

/-- Ex-post individual rationality for a mechanism with transfers, relative to
    an externally supplied utility rule. -/
def isExPostIR [Preorder U] [Zero U]
    (u : A → (I → P) → (∀ i, T i) → I → U) : Prop :=
  ∀ trueTypes : (∀ i, T i), ∀ i : I, ∀ r : (∀ i, T i),
    0 ≤ u (M.allocationRule (Function.update r i (trueTypes i)))
      (M.paymentRule (Function.update r i (trueTypes i))) trueTypes i

/-- The standard quasi-linear specialization of `toStrategicGame`. -/
def toQuasiLinearGame [Sub U]
    (val : A → (∀ i, T i) → I → V)
    (valueToUtility : V → U) (paymentToUtility : P → U)
    (trueTypes : ∀ i, T i) : StrategicGame I U :=
  M.toStrategicGame
    (fun a pay types i => valueToUtility (val a types i) - paymentToUtility (pay i))
    trueTypes

/-- DSIC for quasi-linear utility, as a specialization of `isDSIC`. -/
def isQuasiLinearDSIC [Sub U] [Preorder U]
    (val : A → (∀ i, T i) → I → V)
    (valueToUtility : V → U) (paymentToUtility : P → U) : Prop :=
  M.isDSIC (fun a pay types i => valueToUtility (val a types i) - paymentToUtility (pay i))

/-- Ex-post IR for quasi-linear utility, as a specialization of `isExPostIR`. -/
def isQuasiLinearExPostIR [Sub U] [Preorder U] [Zero U]
    (val : A → (∀ i, T i) → I → V)
    (valueToUtility : V → U) (paymentToUtility : P → U) : Prop :=
  M.isExPostIR (fun a pay types i => valueToUtility (val a types i) - paymentToUtility (pay i))

end MechanismWithTransfers

/-! ## Standard transfer-mechanism specializations -/

/-- A single-parameter mechanism.

  Each agent `i` has a single private type `θ_i : R` (their "value per unit").
  The allocation gives each agent a scalar `x_i : R` (typically in `[0, 1]`,
  interpreted as probability of winning or fractional quantity received).
  Payments are of the same scalar type `R`; utility is quasi-linear: `θ_i · x_i - p_i`.

  In practice `R = ℝ`. The structure is kept polymorphic for generality.

  This is the canonical setting for Myerson's revenue-optimal auction theorem and
  for characterizing implementable (DSIC) allocation rules via monotonicity. -/
structure SingleParameterMechanism (I : Type*) (R : Type*)
    extends MechanismWithTransfers I (fun _ => R) (I → R) R

namespace SingleParameterMechanism

variable {I : Type*} [DecidableEq I] {R : Type*}
variable (M : SingleParameterMechanism I R)

/-- Allocation feasibility: each agent's allocation lies in `[0, 1]`.

  Requires `Zero R`, `One R`, and `LE R` (e.g., any linearly ordered field). -/
def IsAllocFeasible [Zero R] [One R] [LE R] : Prop :=
  ∀ (b : I → R) (i : I), 0 ≤ M.allocationRule b i ∧ M.allocationRule b i ≤ 1

/-- Monotonicity of the allocation rule.

  Agent `i`'s allocation is non-decreasing in `i`'s reported type, holding all
  other reports fixed.

  This is Myerson's necessary and sufficient condition for DSIC in the single-parameter
  setting (with quasi-linear utility and the appropriate payment formula).
  [Myerson 1981; AGT Thm 9.36] -/
def IsMonotone [Preorder R] : Prop :=
  ∀ (i : I) (θ θ' : R), θ ≤ θ' →
    ∀ (b : I → R),
      M.allocationRule (Function.update b i θ) i ≤
      M.allocationRule (Function.update b i θ') i

/-- The payment vector induced by a bid profile in a single-parameter mechanism.

This is just the inherited `MechanismWithTransfers.paymentRule`, restated with
single-parameter terminology. -/
abbrev payment (b : I → R) : I → R :=
  M.paymentRule b

/-- Quasi-linear value in the single-parameter setting:
agent `i` with true type `θᵢ` gets allocation `xᵢ`, worth `θᵢ * xᵢ`. -/
def quasiLinearValue [Mul R]
    (x θ : I → R) (i : I) : R :=
  θ i * x i

/-- Quasi-linear utility in the single-parameter setting:
`uᵢ(θ, b) = θᵢ * xᵢ(b) - pᵢ(b)`. -/
def quasiLinearUtility [Mul R] [Sub R]
    (b θ : I → R) (i : I) : R :=
  quasiLinearValue (M.allocationRule b) θ i - M.payment b i

omit [DecidableEq I] in
/-- The single-parameter quasi-linear utility is the specialization of the
generic transfer-mechanism quasi-linear utility to
`val a θ i = θᵢ * aᵢ` and identity payment embedding. -/
lemma quasiLinearUtility_eq_transferQuasiLinearUtility [Mul R] [Sub R]
    (b θ : I → R) (i : I) :
    M.quasiLinearUtility b θ i =
      MechanismWithTransfers.quasiLinearUtility
        (I := I) (T := fun _ => R) (A := I → R) (P := R) (V := R) (U := R)
        ({ allocationRule := M.allocationRule
           paymentRule := M.paymentRule } :
          MechanismWithTransfers I (fun _ => R) (I → R) R)
        (fun a types j => types j * a j)
        id id b θ i := rfl

/-- Dominant-strategy incentive compatibility in the single-parameter,
quasi-linear setting.

Truthful reporting `θᵢ` is weakly dominant for every agent under utility
`θᵢ * xᵢ(b) - pᵢ(b)`. -/
def IsDSIC [Mul R] [Sub R] [Preorder R] : Prop :=
  ({ allocationRule := M.allocationRule
     paymentRule := M.paymentRule } :
    MechanismWithTransfers I (fun _ => R) (I → R) R).isDSIC
      (fun a pay types i => types i * a i - pay i)

/-- An allocation rule is implementable if there exists some payment rule such
that the resulting single-parameter mechanism is DSIC. -/
def IsImplementable [Mul R] [Sub R] [Preorder R]
    (x : (I → R) → I → R) : Prop :=
  ∃ p : (I → R) → I → R,
    ( { allocationRule := x
        paymentRule := p } : SingleParameterMechanism I R).IsDSIC

end SingleParameterMechanism

/-- A multiple-parameter mechanism with transfers.

Here `A` is the type of feasible allocations and `V` is the codomain of
valuations. Agent `i`'s type/report space is `A → V`: a valuation function
assigning a value to every possible allocation. The mechanism then maps a
profile of reported valuations to an allocation and a payment for each agent. -/
structure MultipleParameterMechanism
    (I : Type*) (A : Type*) (V : Type*) (P : Type*)
    extends MechanismWithTransfers I (fun _ => A → V) A P

namespace MultipleParameterMechanism

variable {I A V : Type*}

/-- The valuation/type space of an agent in a multiple-parameter mechanism. -/
abbrev Valuation (A : Type*) (V : Type*) := A → V

/-- The value extractor used by the generic quasi-linear transfer definitions:
agent `i` evaluates allocation `a` by applying their valuation function to `a`. -/
def valueOfAllocation
    (a : A) (types : ∀ _ : I, Valuation A V) (i : I) : V :=
  types i a

end MultipleParameterMechanism
