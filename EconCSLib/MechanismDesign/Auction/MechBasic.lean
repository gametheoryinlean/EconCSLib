/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.StrategicGame.NashEquilibrium

/-!
# EconCSLib.MechanismDesign.Auction.MechBasic

General mechanism design framework, following the Bourbaki principle:
define the most general structure first, then specialize.

## Abstraction hierarchy

```
Mechanism I T O                                  -- general direct mechanism
  └─ MechanismWithTransfers I T A P              -- allocation + payment rules
       ├─ SingleItemAuction I V P                -- one-item auctions
       ├─ SingleParameterMechanism I R           -- scalar reports and allocations
       └─ BayesianMechanismWithTransfers ...     -- incomplete-information layer

MultipleParameterMechanism I A V P               -- valuation reports `A → V`
  ├─ VCGMechanism                                -- welfare-maximizing VCG rule
  └─ CombinatorialAuction I k V P                -- bundle allocations over `Fin k`
```

## Typeclass design

- `Mechanism` itself needs no algebraic structure on `O`.
- `toStrategicGame` needs `U` with `Preorder` (for dominance/Nash).
- `IsDSIC` reuses `IsWeaklyDominant` from `StrategicGame.Dominance`.
- `MechanismWithTransfers` lives in `Transfer.lean`; it keeps utility construction external
  rather than baking quasi-linearity into the structure.

## Main definitions

* `Mechanism` — a (direct revelation) mechanism: agents report, mechanism decides
* `Mechanism.toStrategicGame` — the induced strategic game where each agent's
  strategy space is their type space
* `Mechanism.IsDSIC` — dominant-strategy incentive compatibility:
  truthful reporting is weakly dominant for every agent under every valuation

## References

* [Nisan, Roughgarden, Tardos, Vazirani, *Algorithmic Game Theory*]
* [Maschler, Solan, Zamir, *Game Theory*, Ch. 11–12]
-/

/-- A (direct revelation) mechanism.

  - `I` — the set of agents (indices)
  - `T` — the type space of each agent
  - `O` — the outcome space

  A mechanism maps a profile of reported types to an outcome.
  In a *direct* mechanism, the message/preference space equals the type space,
  so agent `i` reports elements of `T i`.

  This is the most general definition. Specializations (auctions, voting rules,
  matching mechanisms) arise by choosing appropriate `T`, `O`, and utility functions. -/
structure Mechanism (I : Type*) (T : I → Type*) (O : Type*) where
  /-- The outcome function: given all agents' reports, choose an outcome. -/
  outcome : (∀ i, T i) → O

namespace Mechanism

variable {I : Type*} [DecidableEq I] {T : I → Type*} {O U : Type*}
variable (M : Mechanism I T O) (u : O → (∀ i, T i) → I → U)

/-- The strategic game induced by a mechanism and a utility function.

  Each agent's strategy space is their type space `T i` (they choose what to report).
  Agent `i`'s payoff from report profile `r` under true type `tᵢ` is
  `utility (M.outcome r) tᵢ i`.

  The utility function `u : O → (∀ i, T i) → I → U` takes:
  - the outcome chosen by the mechanism
  - the true type profile (for computing each agent's value)
  - the agent index

  This captures the standard setup: agents have private types, the mechanism
  chooses an outcome based on reports, and each agent evaluates the outcome
  according to their true type. -/
def toStrategicGame (v : ∀ i, T i) : StrategicGame I U where
  strategy := T
  payoff r i := u (M.outcome r) v i

/-- Dominant-strategy incentive compatibility (DSIC).

  A mechanism is DSIC with respect to a utility function if for every true type
  profile `v`, truthful reporting `v i` is a weakly dominant strategy for every agent `i`
  in the induced strategic game.

  This reuses `IsWeaklyDominant` from `StrategicGame.Dominance` — no redundant definition. -/
def IsDSIC [Preorder U] : Prop :=
  ∀ v : (∀ i, T i), ∀ i : I, IsWeaklyDominant (M.toStrategicGame u v) i (v i)

/-- A mechanism is (Ex-Post) Individually Rational if every agent gets nonneg utility
  from truthful reporting, regardless of others' reports. -/
def IsExPostIR [Preorder U] [Zero U] : Prop :=
  ∀ v : (∀ i, T i), ∀ i : I, ∀ r : (∀ i, T i),
    0 ≤ u (M.outcome (Function.update r i (v i))) v i

/-- If a mechanism is DSIC, then truthful reporting is a Nash equilibrium. -/
theorem IsDSIC.truthful_isNash [Preorder U]
    (hdsic : M.IsDSIC u) (v : ∀ i, T i) :
    IsNashEquilibrium (M.toStrategicGame u v) v :=
  IsNashEquilibrium.of_dominant (fun i => hdsic v i)

end Mechanism
