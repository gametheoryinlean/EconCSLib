/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.MechanismDesign.Auction.Transfer
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# EconCSLib.MechanismDesign.Auction.MechBayesian

Mechanism-design primitives for incomplete-information settings.

This file adds a lightweight Bayesian layer on top of the existing
`Mechanism` / `MechanismWithTransfers` hierarchy:

* agents have true types drawn from a common prior probability measure
* agents choose messages as functions of their types
* the mechanism maps message profiles to outcomes, or to allocations and payments

The goal here is only to model the objects cleanly. Equilibrium notions,
interim / ex-ante utilities, and Bayesian incentive properties can be added
on top of this interface in later files.

## Structure hierarchy

```
BayesianMechanism I T M O                        -- prior + message-to-outcome rule
  └─ BayesianMechanismWithTransfers I T M A P    -- allocation + payment rules
       └─ DirectBayesianMechanismWithTransfers I T A P
                                                   -- direct revelation: M = T

MechanismWithTransfers I M A P                   -- complete-information projection
  ↑
BayesianMechanismWithTransfers.toMechanismWithTransfers
```

## Main results

* `BayesianMechanismWithTransfers.exAnte_revelation_principle` — ex-ante revelation principle

## References

* Vijay Krishna, *Auction Theory*, 2nd ed., 2010, Chapter 5
* Roger Myerson, *Incentive Compatibility and the Bargaining Problem*, 1979
-/

/-- A mechanism in an incomplete-information environment.

`T i` is agent `i`'s true type space, `M i` is agent `i`'s message space,
and `prior` is the common prior over type profiles.

This keeps the Harsanyi-style uncertainty separate from the mechanism map
itself: the mechanism acts on reported messages, while the prior lives as
extra Bayesian structure. -/
structure BayesianMechanism
    (I : Type*) (T : I → Type*) [∀ i, MeasurableSpace (T i)]
    (M : I → Type*) (O : Type*) where
  /-- Common prior probability measure over true type profiles. -/
  prior : MeasureTheory.Measure (∀ i, T i)
  /-- The prior is a probability measure. -/
  prob_prior : MeasureTheory.IsProbabilityMeasure prior
  /-- Outcome rule as a function of reported messages. -/
  outcome : (∀ i, M i) → O

-- Intentionally global so measure-theoretic lemmas can infer the probability
-- structure from a mechanism term without repeated local `haveI := B.prob_prior`.
attribute [instance] BayesianMechanism.prob_prior

namespace BayesianMechanism

variable {I : Type*} {T : I → Type*} [∀ i, MeasurableSpace (T i)]
variable {M : I → Type*} {O : Type*}

/-- A pure reporting strategy in an incomplete-information mechanism:
an agent maps each possible true type to a report/message. -/
abbrev Strategy (Tᵢ : Type*) (Mᵢ : Type*) := Tᵢ → Mᵢ

/-- A strategy profile for all agents in an incomplete-information mechanism. -/
abbrev StrategyProfile (T : I → Type*) (M : I → Type*) := ∀ i, Strategy (T i) (M i)

/-- A measurable strategy profile for all agents in an incomplete-information mechanism. -/
def IsMeasurableStrategyProfile
    [∀ i, MeasurableSpace (M i)]
    (σ : StrategyProfile T M) : Prop :=
  ∀ i, Measurable (σ i)

/-- The message profile induced by a true type profile and a strategy profile. -/
def inducedMessages (σ : StrategyProfile T M) (t : ∀ i, T i) : ∀ i, M i :=
  fun i => σ i (t i)

/-- Forget the prior and view a Bayesian mechanism simply as a mechanism on
reported messages. -/
def toMechanism (B : BayesianMechanism I T M O) : Mechanism I M O where
  outcome := B.outcome

end BayesianMechanism

/-- A direct-revelation Bayesian mechanism: agents report in their own type spaces. -/
abbrev DirectBayesianMechanism
    (I : Type*) (T : I → Type*) [∀ i, MeasurableSpace (T i)] (O : Type*) :=
  BayesianMechanism I T T O

namespace DirectBayesianMechanism

variable {I : Type*} {T : I → Type*} [∀ i, MeasurableSpace (T i)] {O : Type*}

/-- Truthful reporting in a direct Bayesian mechanism.

This is kept as a namespace-local definition, rather than always reusing the
transfer-mechanism version, so the direct non-transfer interface remains
self-contained. -/
def truthfulStrategy : BayesianMechanism.StrategyProfile T T :=
  fun _ => id

end DirectBayesianMechanism

/-- A transfer mechanism in an incomplete-information environment.

As in `MechanismWithTransfers`, the allocation and payment rules are stored
separately, while the common prior records the incomplete-information
structure. Utility is intentionally left external. -/
structure BayesianMechanismWithTransfers
    (I : Type*) (T : I → Type*) [∀ i, MeasurableSpace (T i)]
    (M : I → Type*) (A : Type*) (P : Type*) where
  /-- Common prior probability measure over true type profiles. -/
  prior : MeasureTheory.Measure (∀ i, T i)
  /-- The prior is a probability measure. -/
  prob_prior : MeasureTheory.IsProbabilityMeasure prior
  /-- Allocation rule from reported messages. -/
  allocationRule : (∀ i, M i) → A
  /-- Payment rule from reported messages. -/
  paymentRule : (∀ i, M i) → I → P

-- Intentionally global so transfer-mechanism terms expose their probability
-- structure directly to measure-theoretic typeclass search.
attribute [instance] BayesianMechanismWithTransfers.prob_prior

namespace BayesianMechanismWithTransfers

open MeasureTheory

variable {I : Type*} {T : I → Type*} [∀ i, MeasurableSpace (T i)]
variable {M : I → Type*} {A P : Type*}

/-- A pure reporting strategy profile for a Bayesian transfer mechanism. -/
abbrev StrategyProfile (T : I → Type*) (M : I → Type*) :=
  BayesianMechanism.StrategyProfile T M

/-- The allocation induced by a strategy profile and a realized type profile. -/
def inducedAllocation
    (B : BayesianMechanismWithTransfers I T M A P)
    (σ : StrategyProfile T M) (t : ∀ i, T i) : A :=
  B.allocationRule (BayesianMechanism.inducedMessages σ t)

/-- The payment vector induced by a strategy profile and a realized type profile. -/
def inducedPayments
    (B : BayesianMechanismWithTransfers I T M A P)
    (σ : StrategyProfile T M) (t : ∀ i, T i) : I → P :=
  B.paymentRule (BayesianMechanism.inducedMessages σ t)

/-- Deviating from a strategy profile at one agent. -/
def deviate
    [DecidableEq I]
    (σ : StrategyProfile T M) (i : I) (τ : T i → M i) :
    StrategyProfile T M :=
  Function.update σ i τ

/-- Forget the Bayesian prior and recover the underlying transfer mechanism on
reported messages. -/
def toMechanismWithTransfers
    (B : BayesianMechanismWithTransfers I T M A P) :
    MechanismWithTransfers I M A P where
  allocationRule := B.allocationRule
  paymentRule := B.paymentRule

/-- Forget the transfer decomposition and recover the corresponding Bayesian
mechanism with outcome space `A × (I → P)`. -/
def toBayesianMechanism
    (B : BayesianMechanismWithTransfers I T M A P) :
    BayesianMechanism I T M (A × (I → P)) where
  prior := B.prior
  prob_prior := B.prob_prior
  outcome r := (B.allocationRule r, B.paymentRule r)

/-- Ex-ante expected utility of agent `i` under a strategy profile.

The utility rule is supplied externally, as in `MechanismWithTransfers`:
it depends on the induced allocation, the induced payments, the realized
true type profile, and the agent index. -/
noncomputable def exAnteExpectedUtility
    (B : BayesianMechanismWithTransfers I T M A P)
    (u : A → (I → P) → (∀ i, T i) → I → ℝ)
    (σ : StrategyProfile T M) (i : I) : ℝ :=
  ∫ t, u (B.inducedAllocation σ t) (B.inducedPayments σ t) t i ∂B.prior

/-- Integrability of ex-ante utilities for agent `i` under a strategy profile. -/
def IntegrableExAnteUtility
    (B : BayesianMechanismWithTransfers I T M A P)
    (u : A → (I → P) → (∀ i, T i) → I → ℝ)
    (σ : StrategyProfile T M) (i : I) : Prop :=
  Integrable (fun t => u (B.inducedAllocation σ t) (B.inducedPayments σ t) t i) B.prior

/-- An ex-ante Bayesian Nash equilibrium of a transfer mechanism.

No agent can improve their ex-ante expected utility by replacing their
reporting rule with any other measurable pure type-contingent reporting rule.

This is the ex-ante notion: expectations are taken under the full prior, not
conditional on agent `i`'s realized type. The standard interim BNE notion from
mechanism design is a natural future extension. -/
def IsExAnteBayesianNashEquilibrium
    [DecidableEq I]
    [∀ i, MeasurableSpace (M i)]
    (B : BayesianMechanismWithTransfers I T M A P)
    (u : A → (I → P) → (∀ i, T i) → I → ℝ)
    (σ : StrategyProfile T M) : Prop :=
  BayesianMechanism.IsMeasurableStrategyProfile σ ∧
    ∀ (i : I) (τ : T i → M i), Measurable τ →
      B.exAnteExpectedUtility u (deviate σ i τ) i ≤
        B.exAnteExpectedUtility u σ i

end BayesianMechanismWithTransfers

/-- A direct-revelation Bayesian transfer mechanism. -/
abbrev DirectBayesianMechanismWithTransfers
    (I : Type*) (T : I → Type*) [∀ i, MeasurableSpace (T i)] (A : Type*) (P : Type*) :=
  BayesianMechanismWithTransfers I T T A P

namespace DirectBayesianMechanismWithTransfers

variable {I : Type*} {T : I → Type*} [∀ i, MeasurableSpace (T i)] {A P : Type*}

/-- Truthful reporting in a direct Bayesian mechanism with transfers. -/
def truthfulStrategy :
    BayesianMechanismWithTransfers.StrategyProfile T T :=
  fun _ => id

end DirectBayesianMechanismWithTransfers

section exAnte_revelation_principle

namespace BayesianMechanismWithTransfers

variable {I : Type*} {T : I → Type*} [∀ i, MeasurableSpace (T i)]
variable {M : I → Type*} {A P : Type*}

/-- The direct-revelation mechanism induced by an indirect mechanism and a
strategy profile.

An agent reports their type directly; the mechanism then feeds these reports
through the original equilibrium reporting strategies and applies the original
allocation and payment rules. This is the standard object behind the revelation
principle. -/
def directRevelation
    (B : BayesianMechanismWithTransfers I T M A P)
    (σ : StrategyProfile T M) :
    DirectBayesianMechanismWithTransfers I T A P where
  prior := B.prior
  prob_prior := B.prob_prior
  allocationRule t := B.inducedAllocation σ t
  paymentRule t := B.inducedPayments σ t

/-- Under truthful reporting in the induced direct mechanism, the realized
allocation agrees definitionally with the original mechanism played under `σ`. -/
@[simp] lemma directRevelation_allocation_truthful
    (B : BayesianMechanismWithTransfers I T M A P)
    (σ : StrategyProfile T M) (t : ∀ i, T i) :
    (B.directRevelation σ).allocationRule t = B.inducedAllocation σ t :=
  rfl

/-- Under truthful reporting in the induced direct mechanism, the realized
payment vector agrees definitionally with the original mechanism played under `σ`. -/
@[simp] lemma directRevelation_payments_truthful
    (B : BayesianMechanismWithTransfers I T M A P)
    (σ : StrategyProfile T M) (t : ∀ i, T i) :
    (B.directRevelation σ).paymentRule t = B.inducedPayments σ t :=
  rfl

/-- The revelation-principle target property attached to a strategy profile.

This packages the statement we will eventually want to prove: if `σ` is an
equilibrium of the indirect mechanism, then truthful reporting is a Bayesian
equilibrium of the induced direct mechanism. -/
def ExAnteRevelationPrincipleConclusion
    [DecidableEq I]
    [∀ i, MeasurableSpace (T i)]
    [∀ i, MeasurableSpace (M i)]
    (B : BayesianMechanismWithTransfers I T M A P)
    (u : A → (I → P) → (∀ i, T i) → I → ℝ)
    (σ : StrategyProfile T M) : Prop :=
  (B.directRevelation σ).IsExAnteBayesianNashEquilibrium u
    DirectBayesianMechanismWithTransfers.truthfulStrategy

-- Omit the variable-scope `MeasurableSpace (T i)` so that the type and message
-- measurability instances appear together in the explicit binder list below.
omit [∀ i, MeasurableSpace (T i)] in
/-- Revelation principle, ex-ante form:
if `σ` is a Bayesian Nash equilibrium of the indirect mechanism, then truthful
reporting is a Bayesian Nash equilibrium of the induced direct mechanism.

This is the ex-ante version because `IsExAnteBayesianNashEquilibrium` above is defined
via ex-ante expected utility rather than interim conditional utility.

References:
* [Myerson 1979, "Incentive Compatibility and the Bargaining Problem"]
* [Krishna 2010, Ch. 5] -/
theorem exAnte_revelation_principle
    [DecidableEq I]
    [∀ i, MeasurableSpace (T i)]
    [∀ i, MeasurableSpace (M i)]
    (B : BayesianMechanismWithTransfers I T M A P)
    (u : A → (I → P) → (∀ i, T i) → I → ℝ)
    (σ : StrategyProfile T M)
    (hσ : B.IsExAnteBayesianNashEquilibrium u σ) :
    B.ExAnteRevelationPrincipleConclusion u σ := by
  rcases hσ with ⟨hσ_meas, hσ_eq⟩
  constructor
  · intro i
    rw [DirectBayesianMechanismWithTransfers.truthfulStrategy]
    apply measurable_id
  · intro i report hreport
    specialize hσ_eq i (fun t => σ i (report t)) ((hσ_meas i).comp hreport)
    rw [(by
        unfold BayesianMechanismWithTransfers.exAnteExpectedUtility
        apply MeasureTheory.integral_congr_ae
        filter_upwards with t
        simp only [BayesianMechanismWithTransfers.inducedAllocation,
          BayesianMechanismWithTransfers.inducedPayments]
        apply congrArg₂ (fun a p => u (B.allocationRule a) (B.paymentRule p) t i)
        all_goals
          ext j
          by_cases h : j = i
          · subst h
            simp [BayesianMechanism.inducedMessages, BayesianMechanismWithTransfers.deviate]
          · simp [BayesianMechanism.inducedMessages, BayesianMechanismWithTransfers.deviate,
              DirectBayesianMechanismWithTransfers.truthfulStrategy, h] :
        (B.directRevelation σ).exAnteExpectedUtility u
            (deviate DirectBayesianMechanismWithTransfers.truthfulStrategy i report) i =
          B.exAnteExpectedUtility u (deviate σ i (fun t => σ i (report t))) i),
      (by
        unfold BayesianMechanismWithTransfers.exAnteExpectedUtility
        apply MeasureTheory.integral_congr_ae
        filter_upwards with t
        rfl :
        (B.directRevelation σ).exAnteExpectedUtility u
            DirectBayesianMechanismWithTransfers.truthfulStrategy i =
          B.exAnteExpectedUtility u σ i)]
    assumption

end BayesianMechanismWithTransfers

end exAnte_revelation_principle
