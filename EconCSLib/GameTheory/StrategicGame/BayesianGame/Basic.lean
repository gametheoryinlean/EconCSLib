/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.StrategicGame.MixedStrategy
import EconCSLib.GameTheory.StrategicGame.Nash
import EconCSLib.Math.Simplex

/-!
# Finite Bayesian game foundations

This module formalizes the finite part of [MFoGT, Section 7.4] and compares its
equilibrium terminology with [MSZ, Section 9.4].

## Model

`PrimitiveBayesianGame` has a finite state space, a common prior,
player-specific signals, state-dependent payoffs, and finite action sets.
`PrimitiveBayesianGame.toReduced` pushes the prior to signal profiles and
conditions payoffs on each signal-profile fiber, producing `BayesianGame`.
Conditional payoffs on null fibers are defined to be zero.

In `BayesianGame`, each player's action type is independent of that player's
signal, as in MFoGT. MSZ permits type-dependent action sets `A_i(t_i)`, so this
is the constant-action-family specialization of its Harsanyi model.

## Equilibrium terminology

MFoGT calls the no-whole-strategy-deviation predicate Bayesian equilibrium and
derives optimality conditional on each positive-probability own signal, calling
the latter comparison "ex-post." This module uses the standard term "interim"
for that conditional comparison.

MSZ calls the whole-strategy predicate Nash equilibrium
[MSZ, Definition 9.46] and the typewise predicate Bayesian equilibrium
[MSZ, Definition 9.49]. Their equivalence is [MSZ, Theorem 9.53], under MSZ's
assumption that every type has positive marginal probability. Accordingly:

* `IsBayesianEquilibrium` is the MFoGT whole-strategy predicate;
* `IsExAnteNashEquilibrium` is an explicit synonym using MSZ terminology;
* `IsInterimBayesianEquilibrium` requires a best response at every
  positive-probability type.

The strategic-form game below has the original players choose complete
contingent plans. It is distinct from the agent-form game of
[MSZ, Definition 9.50], whose players are the individual types.

## Scope

All state, type, and action spaces in this module are finite. The
measure-theoretic strategy representations and nonatomic-agent model are in
`BayesianGame.Continuous`; the continuous war-of-attrition example is in
`BayesianGame.WarOfAttrition`.

## Main results

* `PrimitiveBayesianGame.toReduced` and
  `PrimitiveBayesianGame.toReduced_behavioralExpectedPayoff` - reduction to
  type profiles and preservation of ex-ante payoffs;
* `BayesianGame.isBayesianEquilibrium_iff_conditionalInterimBestResponses` -
  the MFoGT ex-ante/interim characterization;
* `BayesianGame.isExAnteNashEquilibrium_iff_isInterimBayesianEquilibrium_of_fullTypeSupport`
  - the constant-action-family form of [MSZ, Theorem 9.53];
* `BayesianGame.isConditionalInterimBestResponse_iff_pureAction` - equivalence
  between mixed deviations and the pure deviations in [MSZ, Definition 9.49];
* `BayesianGame.isExAnteNashEquilibrium_iff_allConditionalInterimPureActionBestResponses_of_fullTypeSupport`
  - the all-type, pure-action, constant-action-family specialization of
  [MSZ, Theorem 9.53];
* `BayesianGame.exists_allConditionalInterimPureActionBestResponses_of_fullTypeSupport`
  - the corresponding constant-action-family specialization of
  [MSZ, Theorem 9.52];
* `BayesianGame.isMixedBayesianEquilibrium_iff_behavioral` and
  `BayesianGame.exists_isBayesianEquilibrium` - mixed/behavioral equivalence
  and finite existence;
* `BayesianGame.distributionalStrategyToBehavior_isInduced` - the finite
  distributional/behavioral correspondence, including null types.

## References

* [MFoGT] Chapter 7, Section 7.4
* [MSZ] Chapter 9, especially Section 9.4
-/

open Finset BigOperators

namespace StrategicGame

universe uN uT uA

/-- A finite reduced Bayesian game with a common prior on type profiles and
payoffs depending on the realized type and action profiles.

Type profiles outside the support of `prior` may carry arbitrary payoff values;
they make no contribution to ex-ante or positive-type interim payoffs. -/
structure BayesianGame (N : Type uN) [Fintype N] [DecidableEq N] where
  /-- The type space of each player. -/
  Ty : N → Type uT
  /-- The action space of each player. -/
  Act : N → Type uA
  /-- Each type space is finite. -/
  [tyFintype : ∀ i : N, Fintype (Ty i)]
  /-- Each action space is finite. -/
  [actFintype : ∀ i : N, Fintype (Act i)]
  /-- Each type space is nonempty. -/
  [tyNonempty : ∀ i : N, Nonempty (Ty i)]
  /-- Each action space is nonempty. -/
  [actNonempty : ∀ i : N, Nonempty (Act i)]
  /-- Type spaces have decidable equality. -/
  [tyDecidableEq : ∀ i : N, DecidableEq (Ty i)]
  /-- Action spaces have decidable equality. -/
  [actDecidableEq : ∀ i : N, DecidableEq (Act i)]
  /-- The common prior on type profiles. -/
  prior : stdSimplex ℝ (∀ i : N, Ty i)
  /-- Payoffs as functions of the type profile, action profile, and player. -/
  payoff : (∀ i : N, Ty i) → (∀ i : N, Act i) → N → ℝ

attribute [instance] BayesianGame.tyFintype
attribute [instance] BayesianGame.actFintype
attribute [instance] BayesianGame.tyNonempty
attribute [instance] BayesianGame.actNonempty
attribute [instance] BayesianGame.tyDecidableEq
attribute [instance] BayesianGame.actDecidableEq

/-- Finite primitive Bayesian game from MFoGT Section 7.4.1: Nature chooses a
state, each player observes a finite signal (their type), and payoffs depend on
the state and the realized action profile. -/
structure PrimitiveBayesianGame (N : Type uN) [Fintype N] [DecidableEq N]
    (Ω : Type*) [Fintype Ω] where
  /-- The signal/type space of each player. -/
  Ty : N → Type uT
  /-- The action space of each player. -/
  Act : N → Type uA
  /-- Each type space is finite. -/
  [tyFintype : ∀ i : N, Fintype (Ty i)]
  /-- Each action space is finite. -/
  [actFintype : ∀ i : N, Fintype (Act i)]
  /-- Each type space is nonempty. -/
  [tyNonempty : ∀ i : N, Nonempty (Ty i)]
  /-- Each action space is nonempty. -/
  [actNonempty : ∀ i : N, Nonempty (Act i)]
  /-- Type spaces have decidable equality. -/
  [tyDecidableEq : ∀ i : N, DecidableEq (Ty i)]
  /-- Action spaces have decidable equality. -/
  [actDecidableEq : ∀ i : N, DecidableEq (Act i)]
  /-- The common prior on states. -/
  prior : stdSimplex ℝ Ω
  /-- The signal observed by player `i` at state `ω`. -/
  signal : (i : N) → Ω → Ty i
  /-- State-dependent payoff functions. -/
  payoff : Ω → (∀ i : N, Act i) → N → ℝ

attribute [instance] PrimitiveBayesianGame.tyFintype
attribute [instance] PrimitiveBayesianGame.actFintype
attribute [instance] PrimitiveBayesianGame.tyNonempty
attribute [instance] PrimitiveBayesianGame.actNonempty
attribute [instance] PrimitiveBayesianGame.tyDecidableEq
attribute [instance] PrimitiveBayesianGame.actDecidableEq

namespace PrimitiveBayesianGame

variable {N : Type uN} [Fintype N] [DecidableEq N]
variable {Ω : Type*} [Fintype Ω]

/-- The type profile induced by the signals at state `ω`. -/
def typeProfileAt (P : PrimitiveBayesianGame N Ω) (ω : Ω) : ∀ i : N, P.Ty i :=
  fun i => P.signal i ω

/-- A behavioral strategy in the primitive model maps each signal to a mixed
action. -/
abbrev BehaviorStrategy (P : PrimitiveBayesianGame N Ω) (i : N) :=
  P.Ty i → stdSimplex ℝ (P.Act i)

/-- A behavioral-strategy profile in the primitive model. -/
abbrev BehaviorStrategyProfile (P : PrimitiveBayesianGame N Ω) :=
  ∀ i : N, P.BehaviorStrategy i

/-- Conditional probability of an action profile at state `ω` under
independent behavioral randomization. -/
noncomputable def behavioralActionProbability (P : PrimitiveBayesianGame N Ω)
    (β : P.BehaviorStrategyProfile) (ω : Ω) (a : ∀ i : N, P.Act i) : ℝ :=
  ∏ i : N, (β i (P.signal i ω)).val (a i)

/-- Ex-ante expected payoff in the primitive state-and-signal model. -/
noncomputable def behavioralExpectedPayoff (P : PrimitiveBayesianGame N Ω)
    (β : P.BehaviorStrategyProfile) (i : N) : ℝ :=
  ∑ ω : Ω, P.prior.val ω *
    ∑ a : ∀ j : N, P.Act j,
      P.behavioralActionProbability β ω a * P.payoff ω a i

/-- Replace player `i`'s primitive-model behavioral strategy by `βi`. -/
def deviateBehavior (P : PrimitiveBayesianGame N Ω)
    (β : P.BehaviorStrategyProfile) (i : N) (βi : P.BehaviorStrategy i) :
    P.BehaviorStrategyProfile :=
  Function.update β i βi

/-- Bayesian equilibrium in the primitive state-and-signal model. -/
def IsBayesianEquilibrium (P : PrimitiveBayesianGame N Ω)
    (β : P.BehaviorStrategyProfile) : Prop :=
  ∀ i : N, ∀ βi' : P.BehaviorStrategy i,
    P.behavioralExpectedPayoff (P.deviateBehavior β i βi') i ≤
      P.behavioralExpectedPayoff β i

/-- The probability of a type profile under the state prior. -/
noncomputable def typeProfileProbability (P : PrimitiveBayesianGame N Ω)
    (θ : ∀ i : N, P.Ty i) : ℝ :=
  ∑ ω : Ω, if P.typeProfileAt ω = θ then P.prior.val ω else 0

/-- The probability of every type profile is nonnegative. -/
theorem typeProfileProbability_nonneg (P : PrimitiveBayesianGame N Ω)
    (θ : ∀ i : N, P.Ty i) : 0 ≤ P.typeProfileProbability θ := by
  unfold typeProfileProbability
  exact Finset.sum_nonneg fun ω _ => by
    split
    · exact P.prior.property.1 ω
    · exact le_rfl

/-- Summing the induced type-profile probabilities recovers total state mass. -/
theorem sum_typeProfileProbability (P : PrimitiveBayesianGame N Ω) :
    ∑ θ : ∀ i : N, P.Ty i, P.typeProfileProbability θ = 1 := by
  unfold typeProfileProbability
  rw [Finset.sum_comm]
  calc
    ∑ ω : Ω, ∑ θ : ∀ i : N, P.Ty i,
        (if P.typeProfileAt ω = θ then P.prior.val ω else 0)
        = ∑ ω : Ω, P.prior.val ω := by
          apply Finset.sum_congr rfl
          intro ω _
          simp
    _ = 1 := P.prior.property.2

/-- Conditional expected payoff on a type-profile fiber. It is set to zero on
a null fiber, whose value is irrelevant to every ex-ante payoff. -/
noncomputable def conditionalPayoff (P : PrimitiveBayesianGame N Ω)
    (θ : ∀ i : N, P.Ty i) (a : ∀ i : N, P.Act i) (i : N) : ℝ :=
  if P.typeProfileProbability θ = 0 then
    0
  else
    (P.typeProfileProbability θ)⁻¹ *
      ∑ ω : Ω,
        if P.typeProfileAt ω = θ then P.prior.val ω * P.payoff ω a i else 0

/-- On a null type-profile fiber, every prior-weighted state payoff on that
fiber is zero. -/
private theorem weightedPayoff_fiber_eq_zero_of_probability_eq_zero
    (P : PrimitiveBayesianGame N Ω) (θ : ∀ i : N, P.Ty i)
    (hθ : P.typeProfileProbability θ = 0)
    (a : ∀ i : N, P.Act i) (i : N) :
    ∑ ω : Ω,
      (if P.typeProfileAt ω = θ then P.prior.val ω * P.payoff ω a i else 0) = 0 := by
  have hsum : ∑ ω : Ω,
      (if P.typeProfileAt ω = θ then P.prior.val ω else 0) = 0 := hθ
  have hzero : ∀ ω : Ω, P.typeProfileAt ω = θ → P.prior.val ω = 0 := by
    intro ω hω
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg
      (fun ω' (_ : ω' ∈ (Finset.univ : Finset Ω)) => by
        split
        · exact P.prior.property.1 ω'
        · exact le_rfl)).mp hsum ω (Finset.mem_univ ω)
    simpa [hω] using hterm
  apply Finset.sum_eq_zero
  intro ω _
  by_cases hω : P.typeProfileAt ω = θ
  · simp [hω, hzero ω hω]
  · simp [hω]

/-- Multiplying the conditional payoff by its type-profile probability recovers
the corresponding unnormalized state-fiber payoff. -/
theorem typeProfileProbability_mul_conditionalPayoff
    (P : PrimitiveBayesianGame N Ω) (θ : ∀ i : N, P.Ty i)
    (a : ∀ i : N, P.Act i) (i : N) :
    P.typeProfileProbability θ * P.conditionalPayoff θ a i =
      ∑ ω : Ω,
        if P.typeProfileAt ω = θ then P.prior.val ω * P.payoff ω a i else 0 := by
  unfold conditionalPayoff
  by_cases hθ : P.typeProfileProbability θ = 0
  · rw [if_pos hθ, mul_zero]
    exact P.weightedPayoff_fiber_eq_zero_of_probability_eq_zero θ hθ a i |>.symm
  · rw [if_neg hθ]
    field_simp

/-- Reduction of the primitive state-and-signal model to the finite
type-profile formulation used in the rest of this module. -/
noncomputable def toReduced (P : PrimitiveBayesianGame N Ω) : BayesianGame N where
  Ty := P.Ty
  Act := P.Act
  prior :=
    ⟨P.typeProfileProbability, P.typeProfileProbability_nonneg,
      P.sum_typeProfileProbability⟩
  payoff := P.conditionalPayoff

end PrimitiveBayesianGame

namespace BayesianGame

variable {N : Type uN} [Fintype N] [DecidableEq N]

/-! ### Basic strategy spaces -/

/-- A type profile in a Bayesian game. -/
abbrev TypeProfile (B : BayesianGame N) :=
  ∀ i : N, B.Ty i

/-- An action profile in a Bayesian game. -/
abbrev ActionProfile (B : BayesianGame N) :=
  ∀ i : N, B.Act i

/-- A pure strategy maps each type of a player to an action. -/
abbrev PureStrategy (B : BayesianGame N) (i : N) :=
  B.Ty i → B.Act i

/-- A pure-strategy profile. -/
abbrev PureStrategyProfile (B : BayesianGame N) :=
  ∀ i : N, B.PureStrategy i

/-- A behavioral strategy maps each type of a player to a mixed action. -/
abbrev BehaviorStrategy (B : BayesianGame N) (i : N) :=
  B.Ty i → stdSimplex ℝ (B.Act i)

/-- A behavioral-strategy profile. -/
abbrev BehaviorStrategyProfile (B : BayesianGame N) :=
  ∀ i : N, B.BehaviorStrategy i

/-- A mixed strategy in the strategic-form representation: a distribution over
type-contingent pure strategies. -/
abbrev MixedBayesianStrategy (B : BayesianGame N) (i : N) [Fintype (B.PureStrategy i)] :=
  stdSimplex ℝ (B.PureStrategy i)

/-- A profile of mixed strategies over type-contingent pure plans. -/
abbrev MixedBayesianStrategyProfile (B : BayesianGame N)
    [∀ i, Fintype (B.PureStrategy i)] :=
  ∀ i, B.MixedBayesianStrategy i

/-- The behavioral strategy obtained from the typewise action marginals of a
mixed strategy over pure contingent plans. -/
noncomputable def mixedBayesianStrategyToBehavior (B : BayesianGame N) (i : N)
    (μ : B.MixedBayesianStrategy i) : B.BehaviorStrategy i :=
  fun t => stdSimplex.coordinateMarginal μ t

/-- Typewise marginalization of a mixed contingent-plan profile. -/
noncomputable def mixedBayesianStrategyProfileToBehavior
    (B : BayesianGame N) (μ : B.MixedBayesianStrategyProfile) :
    B.BehaviorStrategyProfile :=
  fun i => B.mixedBayesianStrategyToBehavior i (μ i)

/-- Product coupling of a behavioral strategy across the player's finite type
set, viewed as a mixed strategy over pure contingent plans. -/
noncomputable def behaviorStrategyToMixedBayesian (B : BayesianGame N) (i : N)
    (β : B.BehaviorStrategy i) : B.MixedBayesianStrategy i :=
  stdSimplex.piProduct β

/-- Independently couple each player's behavioral choices across that
player's counterfactual types. -/
noncomputable def behaviorProfileToMixedBayesian
    (B : BayesianGame N) (β : B.BehaviorStrategyProfile) :
    B.MixedBayesianStrategyProfile :=
  fun i => B.behaviorStrategyToMixedBayesian i (β i)

/-- The product coupling of a behavioral strategy has the original behavioral
strategy as its typewise action marginals. Thus the two finite strategy
representations in MFoGT Section 7.4.2 are outcome-equivalent at every type. -/
theorem mixedBayesianStrategyToBehavior_behaviorStrategyToMixedBayesian
    (B : BayesianGame N) (i : N) (β : B.BehaviorStrategy i) :
    B.mixedBayesianStrategyToBehavior i (B.behaviorStrategyToMixedBayesian i β) = β := by
  funext t
  exact stdSimplex.coordinateMarginal_piProduct β t

/-- Independently coupling a behavioral profile and then taking its
typewise marginals recovers the original profile. -/
theorem mixedBayesianStrategyProfileToBehavior_behaviorProfileToMixedBayesian
    (B : BayesianGame N) (β : B.BehaviorStrategyProfile) :
    B.mixedBayesianStrategyProfileToBehavior
      (B.behaviorProfileToMixedBayesian β) = β := by
  funext i
  exact B.mixedBayesianStrategyToBehavior_behaviorStrategyToMixedBayesian i (β i)

/-- Embed a pure strategy as a behavioral strategy. -/
noncomputable def pureToBehaviorStrategy (B : BayesianGame N) (i : N)
    (σi : B.PureStrategy i) : B.BehaviorStrategy i :=
  fun t => stdSimplex.pure (σi t)

/-- Embed a pure-strategy profile as a behavioral-strategy profile. -/
noncomputable def pureToBehaviorProfile (B : BayesianGame N)
    (σ : B.PureStrategyProfile) : B.BehaviorStrategyProfile :=
  fun i => B.pureToBehaviorStrategy i (σ i)

/-- The action profile induced by a pure-strategy profile and a type profile. -/
def realizedActionProfile (B : BayesianGame N)
    (σ : B.PureStrategyProfile) (θ : B.TypeProfile) : B.ActionProfile :=
  fun i => σ i (θ i)

/-! ### Payoff and equilibrium -/

/-- The probability of an action profile induced by a behavioral-strategy profile
at a fixed type profile. -/
noncomputable def behavioralActionProbability (B : BayesianGame N)
    (β : B.BehaviorStrategyProfile) (θ : B.TypeProfile) (a : B.ActionProfile) : ℝ :=
  ∏ i : N, (β i (θ i)).val (a i)

/-- Ex-ante expected payoff of a behavioral-strategy profile, matching the
finite reduced sum after MFoGT conditions the primitive state-dependent game
on the type-profile fibers. -/
noncomputable def behavioralExpectedPayoff (B : BayesianGame N)
    (β : B.BehaviorStrategyProfile) (i : N) : ℝ :=
  ∑ θ : B.TypeProfile,
    B.prior.val θ *
      ∑ a : B.ActionProfile,
        B.behavioralActionProbability β θ a * B.payoff θ a i

end BayesianGame

namespace PrimitiveBayesianGame

variable {N : Type uN} [Fintype N] [DecidableEq N]
variable {Ω : Type*} [Fintype Ω]

/-- The finite reduction preserves the ex-ante payoff of every behavioral
strategy profile, which is the equality displayed in MFoGT Section 7.4.1. -/
theorem toReduced_behavioralExpectedPayoff
    (P : PrimitiveBayesianGame N Ω) (β : P.BehaviorStrategyProfile) (i : N) :
    P.toReduced.behavioralExpectedPayoff β i = P.behavioralExpectedPayoff β i := by
  classical
  unfold BayesianGame.behavioralExpectedPayoff behavioralExpectedPayoff
  simp only [toReduced, BayesianGame.behavioralActionProbability,
    PrimitiveBayesianGame.behavioralActionProbability]
  calc
    ∑ θ : ∀ i : N, P.Ty i,
        P.typeProfileProbability θ *
          ∑ a : ∀ i : N, P.Act i,
            (∏ j : N, (β j (θ j)).val (a j)) * P.conditionalPayoff θ a i
        = ∑ θ : ∀ i : N, P.Ty i,
            ∑ a : ∀ i : N, P.Act i,
              (∏ j : N, (β j (θ j)).val (a j)) *
                (P.typeProfileProbability θ * P.conditionalPayoff θ a i) := by
            apply Finset.sum_congr rfl
            intro θ _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro a _
            ring
    _ = ∑ θ : ∀ i : N, P.Ty i,
          ∑ a : ∀ i : N, P.Act i,
            (∏ j : N, (β j (θ j)).val (a j)) *
              ∑ ω : Ω,
                (if P.typeProfileAt ω = θ then P.prior.val ω * P.payoff ω a i else 0) := by
          apply Finset.sum_congr rfl
          intro θ _
          apply Finset.sum_congr rfl
          intro a _
          rw [P.typeProfileProbability_mul_conditionalPayoff]
    _ = ∑ a : ∀ i : N, P.Act i,
          ∑ ω : Ω,
            (∏ j : N, (β j (P.signal j ω)).val (a j)) *
              (P.prior.val ω * P.payoff ω a i) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro a _
          simp_rw [Finset.mul_sum]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro ω _
          simp [typeProfileAt]
    _ = ∑ ω : Ω, P.prior.val ω *
          ∑ a : ∀ i : N, P.Act i,
            (∏ j : N, (β j (P.signal j ω)).val (a j)) * P.payoff ω a i := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro ω _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro a _
          ring

end PrimitiveBayesianGame

namespace BayesianGame

variable {N : Type uN} [Fintype N] [DecidableEq N]

/-- Replace the behavioral strategy of player `i` by `βi`. -/
def deviateBehavior (B : BayesianGame N)
    (β : B.BehaviorStrategyProfile) (i : N) (βi : B.BehaviorStrategy i) :
    B.BehaviorStrategyProfile :=
  Function.update β i βi

/-- Replace only the mixed action used by type `t` of player `i`. -/
def deviateBehaviorAtType (B : BayesianGame N)
    (β : B.BehaviorStrategyProfile) (i : N) (t : B.Ty i)
    (x : stdSimplex ℝ (B.Act i)) : B.BehaviorStrategyProfile :=
  Function.update β i (Function.update (β i) t x)

/-- A behavioral-strategy profile is a Bayesian equilibrium if no player can
improve his ex-ante payoff by changing his whole type-contingent behavioral
strategy. -/
def IsBayesianEquilibrium (B : BayesianGame N) (β : B.BehaviorStrategyProfile) : Prop :=
  ∀ i : N, ∀ βi' : B.BehaviorStrategy i,
    B.behavioralExpectedPayoff (B.deviateBehavior β i βi') i ≤
      B.behavioralExpectedPayoff β i

/-- Ex-ante Nash equilibrium in the terminology of [MSZ, Definition 9.46].
MFoGT Section 7.4 calls the same no-whole-plan-deviation predicate Bayesian
equilibrium. -/
abbrev IsExAnteNashEquilibrium
    (B : BayesianGame N) (β : B.BehaviorStrategyProfile) : Prop :=
  B.IsBayesianEquilibrium β

end BayesianGame

namespace PrimitiveBayesianGame

variable {N : Type uN} [Fintype N] [DecidableEq N]
variable {Ω : Type*} [Fintype Ω]

/-- The finite state-to-type reduction preserves Bayesian equilibrium. -/
theorem toReduced_isBayesianEquilibrium
    (P : PrimitiveBayesianGame N Ω) (β : P.BehaviorStrategyProfile) :
    P.toReduced.IsBayesianEquilibrium β ↔ P.IsBayesianEquilibrium β := by
  unfold BayesianGame.IsBayesianEquilibrium IsBayesianEquilibrium
  constructor <;> intro h i βi'
  · simpa only [P.toReduced_behavioralExpectedPayoff] using h i βi'
  · simpa only [P.toReduced_behavioralExpectedPayoff] using h i βi'

end PrimitiveBayesianGame

namespace BayesianGame

variable {N : Type uN} [Fintype N] [DecidableEq N]

/-! ### Strategic-form representation for pure strategies -/

/-- The strategic-form game whose pure strategies are type-contingent action
rules and whose payoffs are ex-ante expected payoffs. -/
noncomputable def strategicForm (B : BayesianGame N) : StrategicGame N ℝ where
  strategy i := B.PureStrategy i
  payoff σ i :=
    ∑ θ : B.TypeProfile,
      B.prior.val θ * B.payoff θ (B.realizedActionProfile σ θ) i

/-- The pure contingent-plan spaces of the strategic form are finite. -/
noncomputable instance strategicFormStrategyFintype
    (B : BayesianGame N) (i : N) :
    Fintype (B.strategicForm.strategy i) := by
  change Fintype (B.PureStrategy i)
  infer_instance

/-- Equality of pure contingent plans in the strategic form is decidable. -/
noncomputable instance strategicFormStrategyDecidableEq
    (B : BayesianGame N) (i : N) :
    DecidableEq (B.strategicForm.strategy i) := by
  change DecidableEq (B.PureStrategy i)
  infer_instance

/-- Every pure contingent-plan space of the strategic form is inhabited. -/
noncomputable instance strategicFormStrategyInhabited
    (B : BayesianGame N) (i : N) :
    Inhabited (B.strategicForm.strategy i) := by
  change Inhabited (B.PureStrategy i)
  exact Classical.inhabited_of_nonempty inferInstance

/-- Distribution of the realized action profile at type profile `θ` when each
player independently draws a pure contingent plan from `μ`. -/
noncomputable def mixedPlanActionDistribution
    (B : BayesianGame N) (μ : B.MixedBayesianStrategyProfile)
    (θ : B.TypeProfile) : stdSimplex ℝ B.ActionProfile :=
  stdSimplex.map (fun σ => B.realizedActionProfile σ θ)
    (stdSimplex.piProduct μ)

/-- Drawing mixed contingent plans and evaluating them at `θ` gives the
independent product of their typewise behavioral marginals. This is the
finite realization-equivalence identity behind MFoGT Section 7.4.2. -/
theorem mixedPlanActionDistribution_eq_piProduct_behavior
    (B : BayesianGame N) (μ : B.MixedBayesianStrategyProfile)
    (θ : B.TypeProfile) :
    B.mixedPlanActionDistribution μ θ =
      stdSimplex.piProduct
        (fun i => B.mixedBayesianStrategyToBehavior i (μ i) (θ i)) := by
  classical
  simpa [mixedPlanActionDistribution, realizedActionProfile,
    mixedBayesianStrategyToBehavior] using
    (stdSimplex.map_piProduct
      (f := fun i (σi : B.PureStrategy i) => σi (θ i)) μ)

/-- Pointwise form of mixed-plan/behavioral realization equivalence. -/
theorem mixedPlanActionDistribution_apply
    (B : BayesianGame N) (μ : B.MixedBayesianStrategyProfile)
    (θ : B.TypeProfile) (a : B.ActionProfile) :
    (B.mixedPlanActionDistribution μ θ).val a =
      B.behavioralActionProbability
        (B.mixedBayesianStrategyProfileToBehavior μ) θ a := by
  rw [B.mixedPlanActionDistribution_eq_piProduct_behavior μ θ]
  rfl

/-- The strategic-form mixed payoff of a profile of distributions over pure
contingent plans equals the ex-ante payoff of its behavioral marginals. This
proves payoff equivalence, not merely equality of each player's typewise
marginals. -/
theorem mixedPlanExpectedPayoff_eq_behavioralExpectedPayoff
    (B : BayesianGame N) (μ : B.MixedBayesianStrategyProfile) (i : N) :
    evaluate_at_mixed B.strategicForm i μ =
      B.behavioralExpectedPayoff
        (B.mixedBayesianStrategyProfileToBehavior μ) i := by
  classical
  unfold evaluate_at_mixed strategicForm behavioralExpectedPayoff
  simp only
  calc
    ∑ σ : B.PureStrategyProfile,
        (∏ j : N, (μ j).val (σ j)) *
          ∑ θ : B.TypeProfile,
            B.prior.val θ * B.payoff θ (B.realizedActionProfile σ θ) i
        =
      ∑ θ : B.TypeProfile,
        B.prior.val θ *
          ∑ σ : B.PureStrategyProfile,
            (∏ j : N, (μ j).val (σ j)) *
              B.payoff θ (B.realizedActionProfile σ θ) i := by
          simp_rw [Finset.mul_sum]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro θ _
          apply Finset.sum_congr rfl
          intro σ _
          ring
    _ =
      ∑ θ : B.TypeProfile,
        B.prior.val θ *
          ∑ a : B.ActionProfile,
            B.behavioralActionProbability
                (B.mixedBayesianStrategyProfileToBehavior μ) θ a *
              B.payoff θ a i := by
          apply Finset.sum_congr rfl
          intro θ _
          congr 1
          have h := stdSimplex.wsum_map
            (fun σ : B.PureStrategyProfile => B.realizedActionProfile σ θ)
            (stdSimplex.piProduct μ)
            (fun a : B.ActionProfile => B.payoff θ a i)
          change wsum (B.mixedPlanActionDistribution μ θ)
              (fun a : B.ActionProfile => B.payoff θ a i) =
            wsum (stdSimplex.piProduct μ)
              ((fun a : B.ActionProfile => B.payoff θ a i) ∘
                fun σ : B.PureStrategyProfile => B.realizedActionProfile σ θ) at h
          rw [B.mixedPlanActionDistribution_eq_piProduct_behavior μ θ] at h
          simpa [wsum, behavioralActionProbability,
            mixedBayesianStrategyProfileToBehavior] using h.symm

/-- Mixed Bayesian equilibrium in the Harsanyi strategic form: each player
chooses a probability distribution over pure type-contingent plans. -/
def IsMixedBayesianEquilibrium
    (B : BayesianGame N) (μ : B.MixedBayesianStrategyProfile) : Prop :=
  mixedNashEquilibrium B.strategicForm μ

/-- Typewise marginalization commutes with replacing one player's mixed
contingent-plan strategy. -/
theorem mixedBayesianStrategyProfileToBehavior_update
    (B : BayesianGame N) (μ : B.MixedBayesianStrategyProfile)
    (i : N) (ν : B.MixedBayesianStrategy i) :
    B.mixedBayesianStrategyProfileToBehavior (Function.update μ i ν) =
      B.deviateBehavior (B.mixedBayesianStrategyProfileToBehavior μ) i
        (B.mixedBayesianStrategyToBehavior i ν) := by
  funext j
  by_cases hji : j = i
  · subst j
    simp [mixedBayesianStrategyProfileToBehavior, deviateBehavior]
  · simp [mixedBayesianStrategyProfileToBehavior, deviateBehavior,
      Function.update_of_ne hji]

/-- Mixed contingent-plan equilibrium and behavioral Bayesian equilibrium are
equivalent under typewise marginalization. The reverse implication uses the
independent product coupling only to realize an arbitrary behavioral
deviation as a mixed contingent-plan deviation. -/
theorem isMixedBayesianEquilibrium_iff_behavioral
    (B : BayesianGame N) (μ : B.MixedBayesianStrategyProfile) :
    B.IsMixedBayesianEquilibrium μ ↔
      B.IsBayesianEquilibrium
        (B.mixedBayesianStrategyProfileToBehavior μ) := by
  constructor
  · intro hMixed
    unfold IsBayesianEquilibrium
    intro i βi'
    have hdev := hMixed i (B.behaviorStrategyToMixedBayesian i βi')
    rw [B.mixedPlanExpectedPayoff_eq_behavioralExpectedPayoff,
      B.mixedPlanExpectedPayoff_eq_behavioralExpectedPayoff] at hdev
    have hbehaviorUpdate :
        B.mixedBayesianStrategyProfileToBehavior
            (Function.update μ i (B.behaviorStrategyToMixedBayesian i βi')) =
          B.deviateBehavior (B.mixedBayesianStrategyProfileToBehavior μ) i βi' := by
      rw [B.mixedBayesianStrategyProfileToBehavior_update,
        B.mixedBayesianStrategyToBehavior_behaviorStrategyToMixedBayesian]
    calc
      B.behavioralExpectedPayoff
          (B.deviateBehavior (B.mixedBayesianStrategyProfileToBehavior μ) i βi') i =
        B.behavioralExpectedPayoff
          (B.mixedBayesianStrategyProfileToBehavior
            (Function.update μ i (B.behaviorStrategyToMixedBayesian i βi'))) i :=
        congrArg (fun β => B.behavioralExpectedPayoff β i) hbehaviorUpdate.symm
      _ ≤ B.behavioralExpectedPayoff
          (B.mixedBayesianStrategyProfileToBehavior μ) i := hdev
  · intro hBehavior i ν
    have hdev := hBehavior i (B.mixedBayesianStrategyToBehavior i ν)
    have hupd := B.mixedBayesianStrategyProfileToBehavior_update μ i ν
    calc
      evaluate_at_mixed B.strategicForm i (Function.update μ i ν) =
          B.behavioralExpectedPayoff
            (B.mixedBayesianStrategyProfileToBehavior (Function.update μ i ν)) i :=
        B.mixedPlanExpectedPayoff_eq_behavioralExpectedPayoff
          (Function.update μ i ν) i
      _ = B.behavioralExpectedPayoff
          (B.deviateBehavior (B.mixedBayesianStrategyProfileToBehavior μ) i
            (B.mixedBayesianStrategyToBehavior i ν)) i :=
        congrArg (fun β => B.behavioralExpectedPayoff β i) hupd
      _ ≤ B.behavioralExpectedPayoff
          (B.mixedBayesianStrategyProfileToBehavior μ) i := hdev
      _ = evaluate_at_mixed B.strategicForm i μ :=
        (B.mixedPlanExpectedPayoff_eq_behavioralExpectedPayoff μ i).symm

/-- Every finite Bayesian game has an equilibrium in mixed
type-contingent plans. The empty-player case is included and is vacuous. -/
theorem exists_isMixedBayesianEquilibrium (B : BayesianGame N) :
    ∃ μ : B.MixedBayesianStrategyProfile, B.IsMixedBayesianEquilibrium μ := by
  classical
  cases isEmpty_or_nonempty N with
  | inl hEmpty =>
      letI : IsEmpty N := hEmpty
      exact ⟨fun i => isEmptyElim i, fun i => isEmptyElim i⟩
  | inr hNonempty =>
      letI : Nonempty N := hNonempty
      letI : Inhabited N := Classical.inhabited_of_nonempty hNonempty
      exact exists_mixed_nash_equilibrium_finite B.strategicForm

/-- Every finite Bayesian game has a behavioral Bayesian equilibrium. This is
the finite existence theorem obtained from Nash existence in the Harsanyi
strategic form and mixed-plan/behavioral realization equivalence. -/
theorem exists_isBayesianEquilibrium (B : BayesianGame N) :
    ∃ β : B.BehaviorStrategyProfile, B.IsBayesianEquilibrium β := by
  obtain ⟨μ, hμ⟩ := B.exists_isMixedBayesianEquilibrium
  exact ⟨B.mixedBayesianStrategyProfileToBehavior μ,
    (B.isMixedBayesianEquilibrium_iff_behavioral μ).mp hμ⟩

/-- A pure Bayesian equilibrium is a Nash equilibrium of the induced
strategic-form game. This is the pure-strategy special case of the behavioral
definition above. -/
def IsPureBayesianEquilibrium (B : BayesianGame N) (σ : B.PureStrategyProfile) : Prop :=
  IsNashEquilibrium B.strategicForm σ

/-! ### Interim payoff formulation -/

/-- The prior probability of player `i` having type `t`. -/
noncomputable def typeMarginal (B : BayesianGame N) (i : N) (t : B.Ty i) : ℝ :=
  ∑ θ : B.TypeProfile, if θ i = t then B.prior.val θ else 0

/-- Every type has positive marginal probability. MSZ assumes this in its
Harsanyi model; this module keeps it as a separate predicate because
`BayesianGame` also permits null types. -/
def HasFullTypeSupport (B : BayesianGame N) : Prop :=
  ∀ i : N, ∀ t : B.Ty i, 0 < B.typeMarginal i t

/-- The type marginal is nonnegative. -/
theorem typeMarginal_nonneg (B : BayesianGame N) (i : N) (t : B.Ty i) :
    0 ≤ B.typeMarginal i t := by
  unfold typeMarginal
  exact Finset.sum_nonneg fun θ _ => by
    split
    · exact B.prior.property.1 θ
    · exact le_refl 0

/-- Fiberwise decomposition of a sum over type profiles by player `i`'s realized
type: summing the fiber sums over every type of `i` recovers the sum over all
type profiles. -/
theorem sum_typeProfile_ite_eq (B : BayesianGame N) (i : N) (g : B.TypeProfile → ℝ) :
    ∑ t : B.Ty i, ∑ θ : B.TypeProfile, (if θ i = t then g θ else 0)
      = ∑ θ : B.TypeProfile, g θ := by
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun θ _ => Fintype.sum_ite_eq (θ i) (fun _ => g θ)

/-- The type marginals of player `i` sum to one. -/
theorem sum_typeMarginal (B : BayesianGame N) (i : N) :
    ∑ t : B.Ty i, B.typeMarginal i t = 1 := by
  unfold typeMarginal
  rw [B.sum_typeProfile_ite_eq i B.prior.val, B.prior.property.2]

/-- The unnormalized interim expected payoff of type `t` of player `i` from
using mixed action `x`, holding the opponents' behavioral-strategy profile
fixed. Dividing by `typeMarginal B i t` gives the usual conditional payoff when
the marginal is positive. -/
noncomputable def interimBehaviorPayoffOfMixedAction (B : BayesianGame N)
    (β : B.BehaviorStrategyProfile) (i : N) (t : B.Ty i)
    (x : stdSimplex ℝ (B.Act i)) : ℝ :=
  ∑ θ : B.TypeProfile,
    if θ i = t then
      B.prior.val θ *
        ∑ a : B.ActionProfile,
          B.behavioralActionProbability (B.deviateBehaviorAtType β i t x) θ a *
            B.payoff θ a i
    else
      0

/-- The normalized interim payoff conditional on player `i` having type `t`.
This is the finite `Bⁱ(t)` payoff displayed in MFoGT Section 7.4.1. The value is
set to zero when the conditioning type has zero marginal probability. -/
noncomputable def conditionalInterimBehaviorPayoffOfMixedAction (B : BayesianGame N)
    (β : B.BehaviorStrategyProfile) (i : N) (t : B.Ty i)
    (x : stdSimplex ℝ (B.Act i)) : ℝ :=
  if 0 < B.typeMarginal i t then
    (B.typeMarginal i t)⁻¹ * B.interimBehaviorPayoffOfMixedAction β i t x
  else
    0

/-- A zero type marginal forces every type profile in that fiber to have zero
prior probability. -/
theorem prior_eq_zero_on_typeFiber_of_typeMarginal_eq_zero
    (B : BayesianGame N) (i : N) (t : B.Ty i)
    (ht : B.typeMarginal i t = 0)
    (θ : B.TypeProfile) (hθ : θ i = t) :
    B.prior.val θ = 0 := by
  have hsum : ∑ θ' : B.TypeProfile,
      (if θ' i = t then B.prior.val θ' else 0) = 0 := by
    simpa [typeMarginal] using ht
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg
    (fun θ' (_ : θ' ∈ (Finset.univ : Finset B.TypeProfile)) => by
      split
      · exact B.prior.property.1 θ'
      · exact le_rfl)).mp hsum θ (Finset.mem_univ θ)
  simpa [hθ] using hterm

/-- Every unnormalized interim payoff at a null type is zero, independently of
the contemplated mixed action. -/
theorem interimBehaviorPayoffOfMixedAction_eq_zero_of_typeMarginal_eq_zero
    (B : BayesianGame N) (β : B.BehaviorStrategyProfile)
    (i : N) (t : B.Ty i) (ht : B.typeMarginal i t = 0)
    (x : stdSimplex ℝ (B.Act i)) :
    B.interimBehaviorPayoffOfMixedAction β i t x = 0 := by
  unfold interimBehaviorPayoffOfMixedAction
  apply Finset.sum_eq_zero
  intro θ _
  by_cases hθ : θ i = t
  · rw [if_pos hθ, B.prior_eq_zero_on_typeFiber_of_typeMarginal_eq_zero i t ht θ hθ,
      zero_mul]
  · rw [if_neg hθ]

/-- Multiplying the normalized conditional interim payoff by the type
marginal recovers the unnormalized interim payoff, including at null types. -/
theorem typeMarginal_mul_conditionalInterimBehaviorPayoffOfMixedAction
    (B : BayesianGame N) (β : B.BehaviorStrategyProfile)
    (i : N) (t : B.Ty i) (x : stdSimplex ℝ (B.Act i)) :
    B.typeMarginal i t *
        B.conditionalInterimBehaviorPayoffOfMixedAction β i t x =
      B.interimBehaviorPayoffOfMixedAction β i t x := by
  by_cases ht : 0 < B.typeMarginal i t
  · rw [conditionalInterimBehaviorPayoffOfMixedAction, if_pos ht, ← mul_assoc,
      mul_inv_cancel₀ (ne_of_gt ht), one_mul]
  · have ht0 : B.typeMarginal i t = 0 :=
      le_antisymm (not_lt.mp ht) (B.typeMarginal_nonneg i t)
    rw [conditionalInterimBehaviorPayoffOfMixedAction, if_neg ht, ht0, zero_mul,
      B.interimBehaviorPayoffOfMixedAction_eq_zero_of_typeMarginal_eq_zero β i t ht0 x]

/-- Type `t` of player `i` is an interim behavioral best response to the
opponents' strategies. -/
def IsInterimBestResponse (B : BayesianGame N)
    (β : B.BehaviorStrategyProfile) (i : N) (t : B.Ty i) : Prop :=
  ∀ x : stdSimplex ℝ (B.Act i),
    B.interimBehaviorPayoffOfMixedAction β i t x ≤
      B.interimBehaviorPayoffOfMixedAction β i t (β i t)

/-- Interim best-response predicate using the normalized conditional payoff
`Bⁱ(t)` from MFoGT Section 7.4.1. -/
def IsConditionalInterimBestResponse (B : BayesianGame N)
    (β : B.BehaviorStrategyProfile) (i : N) (t : B.Ty i) : Prop :=
  ∀ x : stdSimplex ℝ (B.Act i),
    B.conditionalInterimBehaviorPayoffOfMixedAction β i t x ≤
      B.conditionalInterimBehaviorPayoffOfMixedAction β i t (β i t)

/-- Pure-action version of the interim best-response condition in
[MSZ, Definition 9.49], specialized to the fixed action type `B.Act i`. It is equivalent to
`IsConditionalInterimBestResponse` because conditional expected payoff is
linear in the acting type's mixed action. -/
def IsConditionalInterimPureActionBestResponse (B : BayesianGame N)
    (β : B.BehaviorStrategyProfile) (i : N) (t : B.Ty i) : Prop :=
  ∀ a : B.Act i,
    B.conditionalInterimBehaviorPayoffOfMixedAction β i t (stdSimplex.pure a) ≤
      B.conditionalInterimBehaviorPayoffOfMixedAction β i t (β i t)

/-- Interim Bayesian equilibrium: every positive-probability type is a best
response conditional on that type. The equivalent pure-action formulation
below is the literal form of [MSZ, Definition 9.49]. -/
def IsInterimBayesianEquilibrium
    (B : BayesianGame N) (β : B.BehaviorStrategyProfile) : Prop :=
  ∀ i : N, ∀ t : B.Ty i,
    0 < B.typeMarginal i t → B.IsConditionalInterimBestResponse β i t

/-- At a positive-probability type, normalized and unnormalized interim
best-response inequalities are equivalent. -/
theorem isInterimBestResponse_iff_isConditionalInterimBestResponse
    (B : BayesianGame N) (β : B.BehaviorStrategyProfile) (i : N) (t : B.Ty i)
    (ht : 0 < B.typeMarginal i t) :
    B.IsInterimBestResponse β i t ↔ B.IsConditionalInterimBestResponse β i t := by
  unfold IsInterimBestResponse IsConditionalInterimBestResponse
  simp only [conditionalInterimBehaviorPayoffOfMixedAction, if_pos ht]
  exact forall_congr' fun _ => (mul_le_mul_iff_of_pos_left (inv_pos.mpr ht)).symm

/-- At a type profile realizing `t`, the action law under a mixed deviation is
the mixture of the laws under its pure-action components. -/
private theorem behavioralActionProbability_deviateAtType_eq_sum_pure
    (B : BayesianGame N) (β : B.BehaviorStrategyProfile)
    (i : N) (t : B.Ty i) (x : stdSimplex ℝ (B.Act i))
    (θ : B.TypeProfile) (hθ : θ i = t) (a : B.ActionProfile) :
    B.behavioralActionProbability (B.deviateBehaviorAtType β i t x) θ a =
      ∑ ai : B.Act i, x.val ai *
        B.behavioralActionProbability
          (B.deviateBehaviorAtType β i t (stdSimplex.pure ai)) θ a := by
  classical
  unfold behavioralActionProbability deviateBehaviorAtType
  let P : ℝ := ∏ j ∈ Finset.univ.erase i, (β j (θ j)).val (a j)
  have hxprod :
      ∏ j : N,
          ((Function.update β i (Function.update (β i) t x)) j (θ j)).val (a j) =
        x.val (a i) * P := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
    congr 1
    · simp [hθ]
    · apply Finset.prod_congr rfl
      intro j hj
      simp [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  have hpureprod : ∀ ai : B.Act i,
      ∏ j : N,
          ((Function.update β i
              (Function.update (β i) t (stdSimplex.pure ai))) j (θ j)).val (a j) =
        (if a i = ai then 1 else 0) * P := by
    intro ai
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
    congr 1
    · simp [hθ, stdSimplex.pure_apply]
    · apply Finset.prod_congr rfl
      intro j hj
      simp [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  rw [hxprod]
  simp_rw [hpureprod]
  simp [Finset.sum_ite_eq, Finset.mem_univ]

/-- The interim payoff of a mixed action is the corresponding convex
combination of pure-action interim payoffs. -/
theorem interimBehaviorPayoffOfMixedAction_eq_sum_pure
    (B : BayesianGame N) (β : B.BehaviorStrategyProfile)
    (i : N) (t : B.Ty i) (x : stdSimplex ℝ (B.Act i)) :
    B.interimBehaviorPayoffOfMixedAction β i t x =
      ∑ ai : B.Act i, x.val ai *
        B.interimBehaviorPayoffOfMixedAction β i t (stdSimplex.pure ai) := by
  classical
  unfold interimBehaviorPayoffOfMixedAction
  calc
    ∑ θ : B.TypeProfile,
        (if θ i = t then
          B.prior.val θ *
            ∑ a : B.ActionProfile,
              B.behavioralActionProbability (B.deviateBehaviorAtType β i t x) θ a *
                B.payoff θ a i
        else 0) =
      ∑ θ : B.TypeProfile,
        (if θ i = t then
          B.prior.val θ *
            ∑ a : B.ActionProfile,
              (∑ ai : B.Act i, x.val ai *
                B.behavioralActionProbability
                  (B.deviateBehaviorAtType β i t (stdSimplex.pure ai)) θ a) *
                B.payoff θ a i
        else 0) := by
          apply Finset.sum_congr rfl
          intro θ _
          by_cases hθ : θ i = t
          · simp only [hθ, if_true]
            congr 1
            apply Finset.sum_congr rfl
            intro a _
            rw [B.behavioralActionProbability_deviateAtType_eq_sum_pure
              β i t x θ hθ a]
          · simp [hθ]
    _ = ∑ ai : B.Act i, x.val ai *
        ∑ θ : B.TypeProfile,
          (if θ i = t then
            B.prior.val θ *
              ∑ a : B.ActionProfile,
                B.behavioralActionProbability
                    (B.deviateBehaviorAtType β i t (stdSimplex.pure ai)) θ a *
                  B.payoff θ a i
          else 0) := by
            simp_rw [Finset.sum_mul, Finset.mul_sum]
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro θ _
            by_cases hθ : θ i = t
            · simp only [hθ, if_true]
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl
              intro ai _
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro a _
              ring
            · simp [hθ]

/-- For a finite action set, testing every mixed interim deviation is
equivalent to testing the pure-action deviations appearing literally in
[MSZ, Definition 9.49]. -/
theorem isConditionalInterimBestResponse_iff_pureAction
    (B : BayesianGame N) (β : B.BehaviorStrategyProfile)
    (i : N) (t : B.Ty i) :
    B.IsConditionalInterimBestResponse β i t ↔
      B.IsConditionalInterimPureActionBestResponse β i t := by
  constructor
  · intro h a
    exact h (stdSimplex.pure a)
  · intro h x
    by_cases ht : 0 < B.typeMarginal i t
    · simp only [conditionalInterimBehaviorPayoffOfMixedAction, if_pos ht]
      rw [B.interimBehaviorPayoffOfMixedAction_eq_sum_pure β i t x]
      calc
        (B.typeMarginal i t)⁻¹ *
            ∑ ai : B.Act i, x.val ai *
              B.interimBehaviorPayoffOfMixedAction β i t (stdSimplex.pure ai) =
          ∑ ai : B.Act i, x.val ai *
            B.conditionalInterimBehaviorPayoffOfMixedAction β i t
              (stdSimplex.pure ai) := by
              simp only [conditionalInterimBehaviorPayoffOfMixedAction, if_pos ht]
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro ai _
              ring
        _ ≤ ∑ ai : B.Act i, x.val ai *
            B.conditionalInterimBehaviorPayoffOfMixedAction β i t (β i t) :=
          Finset.sum_le_sum fun ai _ =>
            mul_le_mul_of_nonneg_left (h ai) (x.property.1 ai)
        _ = (B.typeMarginal i t)⁻¹ *
            B.interimBehaviorPayoffOfMixedAction β i t (β i t) := by
          rw [← Finset.sum_mul, x.property.2, one_mul,
            conditionalInterimBehaviorPayoffOfMixedAction, if_pos ht]
    · simp [conditionalInterimBehaviorPayoffOfMixedAction, ht]

/-- Pure-action, constant-action-family form of interim Bayesian equilibrium. -/
theorem isInterimBayesianEquilibrium_iff_pureAction
    (B : BayesianGame N) (β : B.BehaviorStrategyProfile) :
    B.IsInterimBayesianEquilibrium β ↔
      ∀ i : N, ∀ t : B.Ty i, 0 < B.typeMarginal i t →
        B.IsConditionalInterimPureActionBestResponse β i t := by
  unfold IsInterimBayesianEquilibrium
  exact forall_congr' fun i => forall_congr' fun t => forall_congr' fun _ =>
    B.isConditionalInterimBestResponse_iff_pureAction β i t

/-- At a type profile `θ` realizing `i`'s type as `t`, replacing `i`'s whole
behavioral strategy by `βi'` yields the same realized mixed-action probability
as replacing only the mixed action used at `t`. -/
private theorem deviateBehavior_apply_eq_deviateBehaviorAtType_apply
    (B : BayesianGame N) (β : B.BehaviorStrategyProfile) (i : N) (t : B.Ty i)
    (βi' : B.BehaviorStrategy i) {θ : B.TypeProfile} (hθ : θ i = t) (j : N) :
    (B.deviateBehavior β i βi') j (θ j) = (B.deviateBehaviorAtType β i t (βi' t)) j (θ j) := by
  unfold deviateBehavior deviateBehaviorAtType
  by_cases hj : j = i
  · subst hj
    simp [hθ]
  · simp [Function.update_of_ne hj]

private theorem behavioralActionProbability_deviate_eq_deviateAtType
    (B : BayesianGame N) (β : B.BehaviorStrategyProfile) (i : N) (t : B.Ty i)
    (βi' : B.BehaviorStrategy i) {θ : B.TypeProfile} (hθ : θ i = t) (a : B.ActionProfile) :
    B.behavioralActionProbability (B.deviateBehavior β i βi') θ a
      = B.behavioralActionProbability (B.deviateBehaviorAtType β i t (βi' t)) θ a := by
  unfold behavioralActionProbability
  exact Finset.prod_congr rfl fun j _ =>
    congrArg (fun x => x.val (a j))
      (B.deviateBehavior_apply_eq_deviateBehaviorAtType_apply β i t βi' hθ j)

/-- Deviating player `i`'s whole behavioral strategy to `βi'` gives an ex-ante
payoff that decomposes as the sum, over `i`'s types, of the interim payoffs
from playing `βi' t` at each type `t`. -/
theorem behavioralExpectedPayoff_deviate_eq_sum_interim
    (B : BayesianGame N) (β : B.BehaviorStrategyProfile) (i : N) (βi' : B.BehaviorStrategy i) :
    B.behavioralExpectedPayoff (B.deviateBehavior β i βi') i
      = ∑ t : B.Ty i, B.interimBehaviorPayoffOfMixedAction β i t (βi' t) := by
  unfold behavioralExpectedPayoff interimBehaviorPayoffOfMixedAction
  rw [← B.sum_typeProfile_ite_eq i
    (fun θ => B.prior.val θ *
      ∑ a : B.ActionProfile,
        B.behavioralActionProbability (B.deviateBehavior β i βi') θ a * B.payoff θ a i)]
  refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun θ _ => ?_
  by_cases hθ : θ i = t
  · have hsum_eq : (∑ a : B.ActionProfile,
          B.behavioralActionProbability (B.deviateBehavior β i βi') θ a * B.payoff θ a i)
        = ∑ a : B.ActionProfile,
          B.behavioralActionProbability (B.deviateBehaviorAtType β i t (βi' t)) θ a *
            B.payoff θ a i :=
      Finset.sum_congr rfl fun a _ => by
        rw [B.behavioralActionProbability_deviate_eq_deviateAtType β i t βi' hθ a]
    simp only [hθ, if_true, hsum_eq]
  · simp [hθ]

/-- The undeviated ex-ante payoff decomposes as the sum, over `i`'s types, of
the interim payoffs realized by `β`'s own prescription. -/
theorem behavioralExpectedPayoff_eq_sum_interim
    (B : BayesianGame N) (β : B.BehaviorStrategyProfile) (i : N) :
    B.behavioralExpectedPayoff β i
      = ∑ t : B.Ty i, B.interimBehaviorPayoffOfMixedAction β i t (β i t) := by
  have h := B.behavioralExpectedPayoff_deviate_eq_sum_interim β i (β i)
  rwa [show B.deviateBehavior β i (β i) = β from by
    unfold deviateBehavior; exact Function.update_eq_self i β] at h

/-- Finite form of the MFoGT identity
`γⁱ(σ) = ∑ₜ Πⁱ(t) Bⁱ(t)`: ex-ante payoff is the type-marginal weighted sum of
normalized own-type conditional payoffs. -/
theorem behavioralExpectedPayoff_eq_sum_typeMarginal_mul_conditionalInterim
    (B : BayesianGame N) (β : B.BehaviorStrategyProfile) (i : N) :
    B.behavioralExpectedPayoff β i =
      ∑ t : B.Ty i,
        B.typeMarginal i t *
          B.conditionalInterimBehaviorPayoffOfMixedAction β i t (β i t) := by
  rw [B.behavioralExpectedPayoff_eq_sum_interim β i]
  exact Finset.sum_congr rfl fun t _ =>
    (B.typeMarginal_mul_conditionalInterimBehaviorPayoffOfMixedAction β i t (β i t)).symm

/-- [MFoGT, Section 7.4.1] A behavioral-strategy profile is a Bayesian equilibrium
iff each positive-probability type plays an interim best response.

MFoGT calls this own-type-conditioned maximization "ex-post" in this passage;
this module uses the standard Bayesian-game term "interim." The payoff in
`IsInterimBestResponse` is unnormalized, which is equivalent to MFoGT's
conditional payoff after division by the positive type marginal. -/
theorem isBayesianEquilibrium_iff_interimBestResponses
    (B : BayesianGame N) (β : B.BehaviorStrategyProfile) :
    B.IsBayesianEquilibrium β ↔
      ∀ i : N, ∀ t : B.Ty i,
        0 < B.typeMarginal i t → B.IsInterimBestResponse β i t := by
  unfold IsBayesianEquilibrium IsInterimBestResponse
  constructor
  · intro hEq i t ht x
    classical
    have hle := hEq i (Function.update (β i) t x)
    rw [B.behavioralExpectedPayoff_deviate_eq_sum_interim β i (Function.update (β i) t x),
      B.behavioralExpectedPayoff_eq_sum_interim β i] at hle
    have hpt : ∀ t' : B.Ty i, t' ≠ t →
        B.interimBehaviorPayoffOfMixedAction β i t' (Function.update (β i) t x t')
          = B.interimBehaviorPayoffOfMixedAction β i t' (β i t') := by
      intro t' ht'
      rw [Function.update_of_ne ht']
    have hsum_eq : ∑ t' : B.Ty i, B.interimBehaviorPayoffOfMixedAction β i t'
          (Function.update (β i) t x t')
        = B.interimBehaviorPayoffOfMixedAction β i t x
          + ∑ t' ∈ Finset.univ.erase t,
              B.interimBehaviorPayoffOfMixedAction β i t' (β i t') := by
      rw [← Finset.add_sum_erase Finset.univ
        (fun t' => B.interimBehaviorPayoffOfMixedAction β i t' (Function.update (β i) t x t'))
        (Finset.mem_univ t)]
      congr 1
      · simp [Function.update_self]
      · exact Finset.sum_congr rfl fun t' ht' =>
          hpt t' (Finset.ne_of_mem_erase ht')
    have hsum_eq' : ∑ t' : B.Ty i, B.interimBehaviorPayoffOfMixedAction β i t' (β i t')
        = B.interimBehaviorPayoffOfMixedAction β i t (β i t)
          + ∑ t' ∈ Finset.univ.erase t,
              B.interimBehaviorPayoffOfMixedAction β i t' (β i t') :=
      (Finset.add_sum_erase Finset.univ
        (fun t' => B.interimBehaviorPayoffOfMixedAction β i t' (β i t')) (Finset.mem_univ t)).symm
    rw [hsum_eq, hsum_eq'] at hle
    linarith
  · intro hInterim i βi'
    rw [B.behavioralExpectedPayoff_deviate_eq_sum_interim β i βi',
      B.behavioralExpectedPayoff_eq_sum_interim β i]
    apply Finset.sum_le_sum
    intro t _
    rcases eq_or_lt_of_le (B.typeMarginal_nonneg i t) with ht0 | htpos
    · rw [B.interimBehaviorPayoffOfMixedAction_eq_zero_of_typeMarginal_eq_zero
          β i t ht0.symm (βi' t),
        B.interimBehaviorPayoffOfMixedAction_eq_zero_of_typeMarginal_eq_zero
          β i t ht0.symm (β i t)]
    · exact hInterim i t htpos (βi' t)

/-- Normalized conditional-payoff form of the ex-ante/interim
characterization in MFoGT Section 7.4.1. -/
theorem isBayesianEquilibrium_iff_conditionalInterimBestResponses
    (B : BayesianGame N) (β : B.BehaviorStrategyProfile) :
    B.IsBayesianEquilibrium β ↔
      ∀ i : N, ∀ t : B.Ty i,
        0 < B.typeMarginal i t → B.IsConditionalInterimBestResponse β i t := by
  rw [B.isBayesianEquilibrium_iff_interimBestResponses β]
  exact forall_congr' fun i => forall_congr' fun t => forall_congr' fun ht =>
    B.isInterimBestResponse_iff_isConditionalInterimBestResponse β i t ht

/-- The ex-ante predicate is equivalent to interim optimality at every
positive-probability type, even when null types are present. -/
theorem isExAnteNashEquilibrium_iff_isInterimBayesianEquilibrium
    (B : BayesianGame N) (β : B.BehaviorStrategyProfile) :
    B.IsExAnteNashEquilibrium β ↔ B.IsInterimBayesianEquilibrium β := by
  exact B.isBayesianEquilibrium_iff_conditionalInterimBestResponses β

/-- Every finite Bayesian game has an interim Bayesian equilibrium at all
positive-probability types. Under MSZ's full-type-support convention, this is
the existence conclusion of [MSZ, Theorem 9.52]. -/
theorem exists_isInterimBayesianEquilibrium (B : BayesianGame N) :
    ∃ β : B.BehaviorStrategyProfile, B.IsInterimBayesianEquilibrium β := by
  obtain ⟨β, hβ⟩ := B.exists_isBayesianEquilibrium
  exact ⟨β,
    (B.isExAnteNashEquilibrium_iff_isInterimBayesianEquilibrium β).mp hβ⟩

/-- Constant-action-family specialization of [MSZ, Theorem 9.53]. Under full
type support, ex-ante Nash equilibrium is equivalent to interim Bayesian
equilibrium at every type. -/
theorem isExAnteNashEquilibrium_iff_isInterimBayesianEquilibrium_of_fullTypeSupport
    (B : BayesianGame N) (β : B.BehaviorStrategyProfile)
    (hfull : B.HasFullTypeSupport) :
    B.IsExAnteNashEquilibrium β ↔
      ∀ i : N, ∀ t : B.Ty i, B.IsConditionalInterimBestResponse β i t := by
  rw [B.isExAnteNashEquilibrium_iff_isInterimBayesianEquilibrium β]
  unfold IsInterimBayesianEquilibrium
  constructor
  · exact fun h i t => h i t (hfull i t)
  · exact fun h i t _ => h i t

/-- Source-facing constant-action-family specialization of [MSZ, Theorem 9.53].
Under full type support, ex-ante Nash equilibrium is equivalent to all of the
pure-action interim inequalities from [MSZ, Definition 9.49]. -/
theorem isExAnteNashEquilibrium_iff_allConditionalInterimPureActionBestResponses_of_fullTypeSupport
    (B : BayesianGame N) (β : B.BehaviorStrategyProfile)
    (hfull : B.HasFullTypeSupport) :
    B.IsExAnteNashEquilibrium β ↔
      ∀ i : N, ∀ t : B.Ty i,
        B.IsConditionalInterimPureActionBestResponse β i t := by
  rw [B.isExAnteNashEquilibrium_iff_isInterimBayesianEquilibrium_of_fullTypeSupport
    β hfull]
  exact forall_congr' fun i => forall_congr' fun t =>
    B.isConditionalInterimBestResponse_iff_pureAction β i t

/-- Constant-action-family specialization of [MSZ, Theorem 9.52]: under the
full-type-support assumption built into MSZ's Harsanyi model, there is a
behavioral profile satisfying every pure-action interim incentive constraint.
MSZ additionally permits the available action set to depend on the type. -/
theorem exists_allConditionalInterimPureActionBestResponses_of_fullTypeSupport
    (B : BayesianGame N) (hfull : B.HasFullTypeSupport) :
    ∃ β : B.BehaviorStrategyProfile,
      ∀ i : N, ∀ t : B.Ty i,
        B.IsConditionalInterimPureActionBestResponse β i t := by
  obtain ⟨β, hβ⟩ := B.exists_isInterimBayesianEquilibrium
  refine ⟨β, ?_⟩
  have hpure := (B.isInterimBayesianEquilibrium_iff_pureAction β).mp hβ
  exact fun i t => hpure i t (hfull i t)

/-- Under the explicit zero convention for undefined conditional payoffs, a
null type is automatically a conditional interim best response. -/
theorem isConditionalInterimBestResponse_of_typeMarginal_eq_zero
    (B : BayesianGame N) (β : B.BehaviorStrategyProfile)
    (i : N) (t : B.Ty i) (ht : B.typeMarginal i t = 0) :
    B.IsConditionalInterimBestResponse β i t := by
  intro x
  simp [conditionalInterimBehaviorPayoffOfMixedAction, ht]

/-- Convention-totalized form of the ex-ante/interim equivalence. It includes
null types only because their conditional payoffs are explicitly defined to be
zero; it is not the source-facing all-type statement unless full type support
is assumed. -/
theorem isBayesianEquilibrium_iff_allConditionalInterimBestResponses_totalized
    (B : BayesianGame N) (β : B.BehaviorStrategyProfile) :
    B.IsBayesianEquilibrium β ↔
      ∀ i : N, ∀ t : B.Ty i, B.IsConditionalInterimBestResponse β i t := by
  rw [B.isBayesianEquilibrium_iff_conditionalInterimBestResponses β]
  constructor
  · intro h i t
    rcases eq_or_lt_of_le (B.typeMarginal_nonneg i t) with ht0 | htpos
    · exact B.isConditionalInterimBestResponse_of_typeMarginal_eq_zero β i t ht0.symm
    · exact h i t htpos
  · exact fun h i t _ => h i t

/-! ### Pure-strategy special case -/

/-- Replace player `i`'s realized action by `a` in an action profile induced by a
pure-strategy profile. -/
def actionProfileWithAction (B : BayesianGame N)
    (σ : B.PureStrategyProfile) (θ : B.TypeProfile)
    (i : N) (a : B.Act i) : B.ActionProfile :=
  Function.update (B.realizedActionProfile σ θ) i a

/-- The unnormalized interim expected payoff of type `t` of player `i` from
choosing pure action `a`, holding the opponents' pure-strategy profile fixed. -/
noncomputable def interimPayoffOfAction (B : BayesianGame N)
    (σ : B.PureStrategyProfile) (i : N) (t : B.Ty i) (a : B.Act i) : ℝ :=
  ∑ θ : B.TypeProfile,
    if θ i = t then
      B.prior.val θ * B.payoff θ (B.actionProfileWithAction σ θ i a) i
    else
      0

/-- Every pure-action interim payoff at a null type is zero. -/
theorem interimPayoffOfAction_eq_zero_of_typeMarginal_eq_zero
    (B : BayesianGame N) (σ : B.PureStrategyProfile)
    (i : N) (t : B.Ty i) (ht : B.typeMarginal i t = 0) (a : B.Act i) :
    B.interimPayoffOfAction σ i t a = 0 := by
  unfold interimPayoffOfAction
  apply Finset.sum_eq_zero
  intro θ _
  by_cases hθ : θ i = t
  · rw [if_pos hθ, B.prior_eq_zero_on_typeFiber_of_typeMarginal_eq_zero i t ht θ hθ,
      zero_mul]
  · rw [if_neg hθ]

/-- Type `t` of player `i` is a pure interim best response. -/
def IsPureInterimBestResponse (B : BayesianGame N)
    (σ : B.PureStrategyProfile) (i : N) (t : B.Ty i) : Prop :=
  ∀ a : B.Act i,
    B.interimPayoffOfAction σ i t a ≤
      B.interimPayoffOfAction σ i t (σ i t)

/-- At a type profile `θ` realizing `i`'s type as `t`, replacing `i`'s whole
pure strategy by `σi'` yields the same realized action profile as replacing
only the action used at `t`. -/
private theorem deviate_realizedActionProfile_apply_eq_actionProfileWithAction
    (B : BayesianGame N) (σ : B.PureStrategyProfile) (i : N) (t : B.Ty i)
    (σi' : B.PureStrategy i) {θ : B.TypeProfile} (hθ : θ i = t) (j : N) :
    B.realizedActionProfile (Function.update σ i σi') θ j
      = B.actionProfileWithAction σ θ i (σi' t) j := by
  by_cases hj : j = i
  · subst hj
    simp [realizedActionProfile, actionProfileWithAction, hθ]
  · simp [realizedActionProfile, actionProfileWithAction, Function.update_of_ne hj]

/-- Updating `i`'s realized action to `i`'s own action at `θ` is a no-op. -/
private theorem actionProfileWithAction_self
    (B : BayesianGame N) (σ : B.PureStrategyProfile) (θ : B.TypeProfile) (i : N) (t : B.Ty i)
    (hθ : θ i = t) :
    B.actionProfileWithAction σ θ i (σ i t) = B.realizedActionProfile σ θ := by
  funext j
  by_cases hj : j = i
  · subst hj
    simp [actionProfileWithAction, realizedActionProfile, hθ]
  · simp [actionProfileWithAction, realizedActionProfile, Function.update_of_ne hj]

private theorem realizedActionProfile_deviate_eq_actionProfileWithAction
    (B : BayesianGame N) (σ : B.PureStrategyProfile) (i : N) (t : B.Ty i)
    (σi' : B.PureStrategy i) {θ : B.TypeProfile} (hθ : θ i = t) :
    B.realizedActionProfile (Function.update σ i σi') θ
      = B.actionProfileWithAction σ θ i (σi' t) :=
  funext fun j => B.deviate_realizedActionProfile_apply_eq_actionProfileWithAction σ i t σi' hθ j

/-- Deviating player `i`'s whole pure strategy to `σi'` gives an ex-ante
strategic-form payoff that decomposes as the sum, over `i`'s types, of the
interim payoffs from playing `σi' t` at each type `t`. -/
theorem strategicForm_payoff_deviate_eq_sum_interim
    (B : BayesianGame N) (σ : B.PureStrategyProfile) (i : N) (σi' : B.PureStrategy i) :
    B.strategicForm.payoff (Function.update σ i σi') i
      = ∑ t : B.Ty i, B.interimPayoffOfAction σ i t (σi' t) := by
  unfold strategicForm interimPayoffOfAction
  simp only
  rw [← B.sum_typeProfile_ite_eq i
    (fun θ => B.prior.val θ *
      B.payoff θ (B.realizedActionProfile (Function.update σ i σi') θ) i)]
  refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun θ _ => ?_
  by_cases hθ : θ i = t
  · rw [B.realizedActionProfile_deviate_eq_actionProfileWithAction σ i t σi' hθ]
  · simp [hθ]

/-- The undeviated ex-ante strategic-form payoff decomposes as the sum, over
`i`'s types, of the interim payoffs realized by `σ`'s own prescription. -/
theorem strategicForm_payoff_eq_sum_interim
    (B : BayesianGame N) (σ : B.PureStrategyProfile) (i : N) :
    B.strategicForm.payoff σ i
      = ∑ t : B.Ty i, B.interimPayoffOfAction σ i t (σ i t) := by
  unfold strategicForm interimPayoffOfAction
  simp only
  rw [← B.sum_typeProfile_ite_eq i
    (fun θ => B.prior.val θ * B.payoff θ (B.realizedActionProfile σ θ) i)]
  refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun θ _ => ?_
  by_cases hθ : θ i = t
  · rw [← B.actionProfileWithAction_self σ θ i t hθ]
  · simp [hθ]

/-- Pure-strategy special case of the ex-ante/interim characterization. As
above, MFoGT uses "ex-post" for the own-type-conditioned condition. -/
theorem isPureBayesianEquilibrium_iff_pureInterimBestResponses
    (B : BayesianGame N) (σ : B.PureStrategyProfile) :
    B.IsPureBayesianEquilibrium σ ↔
      ∀ i : N, ∀ t : B.Ty i,
        0 < B.typeMarginal i t → B.IsPureInterimBestResponse σ i t := by
  unfold IsPureBayesianEquilibrium IsNashEquilibrium IsBestResponse IsPureInterimBestResponse
  constructor
  · intro hEq i t ht a
    classical
    have hle := hEq i (Function.update (σ i) t a)
    rw [B.strategicForm_payoff_deviate_eq_sum_interim σ i (Function.update (σ i) t a),
      B.strategicForm_payoff_eq_sum_interim σ i] at hle
    have hpt : ∀ t' : B.Ty i, t' ≠ t →
        B.interimPayoffOfAction σ i t' (Function.update (σ i) t a t')
          = B.interimPayoffOfAction σ i t' (σ i t') := by
      intro t' ht'
      rw [Function.update_of_ne ht']
    have hsum_eq : ∑ t' : B.Ty i, B.interimPayoffOfAction σ i t'
          (Function.update (σ i) t a t')
        = B.interimPayoffOfAction σ i t a
          + ∑ t' ∈ Finset.univ.erase t, B.interimPayoffOfAction σ i t' (σ i t') := by
      rw [← Finset.add_sum_erase Finset.univ
        (fun t' => B.interimPayoffOfAction σ i t' (Function.update (σ i) t a t'))
        (Finset.mem_univ t)]
      congr 1
      · simp [Function.update_self]
      · exact Finset.sum_congr rfl fun t' ht' => hpt t' (Finset.ne_of_mem_erase ht')
    have hsum_eq' : ∑ t' : B.Ty i, B.interimPayoffOfAction σ i t' (σ i t')
        = B.interimPayoffOfAction σ i t (σ i t)
          + ∑ t' ∈ Finset.univ.erase t, B.interimPayoffOfAction σ i t' (σ i t') :=
      (Finset.add_sum_erase Finset.univ
        (fun t' => B.interimPayoffOfAction σ i t' (σ i t')) (Finset.mem_univ t)).symm
    rw [hsum_eq, hsum_eq'] at hle
    linarith
  · intro hInterim i σi'
    rw [B.strategicForm_payoff_deviate_eq_sum_interim σ i σi',
      B.strategicForm_payoff_eq_sum_interim σ i]
    apply Finset.sum_le_sum
    intro t _
    rcases eq_or_lt_of_le (B.typeMarginal_nonneg i t) with ht0 | htpos
    · rw [B.interimPayoffOfAction_eq_zero_of_typeMarginal_eq_zero
          σ i t ht0.symm (σi' t),
        B.interimPayoffOfAction_eq_zero_of_typeMarginal_eq_zero
          σ i t ht0.symm (σ i t)]
    · exact hInterim i t htpos (σi' t)

/-! ### Distributional strategies -/

/-- [MFoGT Section 7.4.2] A distributional strategy for player `i`: a joint
distribution over the player's type and action whose type marginal agrees with
the common prior. -/
structure DistributionalStrategy (B : BayesianGame N) (i : N) where
  /-- Joint distribution over types and actions of player `i`. -/
  dist : stdSimplex ℝ (B.Ty i × B.Act i)
  /-- Compatibility with the common prior's marginal on player `i`'s type. -/
  compatible :
    ∀ t : B.Ty i, ∑ a : B.Act i, dist.val (t, a) = B.typeMarginal i t

/-- A distributional strategy is induced by a behavioral strategy when its joint
probability of `(type, action)` is the type marginal times the behavioral
probability of that action at that type. -/
def IsInducedByBehaviorStrategy (B : BayesianGame N) (i : N)
    (β : B.BehaviorStrategy i) (d : B.DistributionalStrategy i) : Prop :=
  ∀ t : B.Ty i, ∀ a : B.Act i,
    d.dist.val (t, a) = B.typeMarginal i t * (β t).val a

/-- The distributional strategy induced by a behavioral strategy: multiply
the conditional action law at each type by the prior marginal of that type. -/
noncomputable def behaviorStrategyToDistributional
    (B : BayesianGame N) (i : N) (β : B.BehaviorStrategy i) :
    B.DistributionalStrategy i := by
  refine ⟨⟨fun p => B.typeMarginal i p.1 * (β p.1).val p.2, ?_, ?_⟩, ?_⟩
  · rintro ⟨t, a⟩
    exact mul_nonneg (B.typeMarginal_nonneg i t) ((β t).property.1 a)
  · rw [Fintype.sum_prod_type]
    have hstep : ∀ t : B.Ty i,
        (∑ a : B.Act i, B.typeMarginal i t * (β t).val a) = B.typeMarginal i t :=
      fun t => by rw [← Finset.mul_sum, (β t).property.2, mul_one]
    simp_rw [hstep]
    exact B.sum_typeMarginal i
  · intro t
    show (∑ a : B.Act i, B.typeMarginal i t * (β t).val a) = B.typeMarginal i t
    rw [← Finset.mul_sum, (β t).property.2, mul_one]

/-- The canonical distributional strategy constructed from `β` is induced by
`β` in the exact joint-law sense. -/
theorem behaviorStrategyToDistributional_isInduced
    (B : BayesianGame N) (i : N) (β : B.BehaviorStrategy i) :
    B.IsInducedByBehaviorStrategy i β (B.behaviorStrategyToDistributional i β) :=
  fun _ _ => rfl

/-- A behavioral strategy induces a distributional strategy when weighted by
the type marginal. -/
theorem exists_distributionalStrategy_inducedBy_behavior
    (B : BayesianGame N) (i : N) (β : B.BehaviorStrategy i) :
    ∃ d : B.DistributionalStrategy i, B.IsInducedByBehaviorStrategy i β d :=
  ⟨B.behaviorStrategyToDistributional i β,
    B.behaviorStrategyToDistributional_isInduced i β⟩

/-- If a distributional strategy has zero type marginal at `t`, every joint
mass `(t,a)` is zero. This is the finite nonnegative-measure fact that makes
the behavioral/distributional correspondence exact even on null types,
although the conditional behavior there is not uniquely determined. -/
theorem DistributionalStrategy.eq_zero_of_typeMarginal_eq_zero
    (B : BayesianGame N) (i : N) (d : B.DistributionalStrategy i)
    (t : B.Ty i) (ht : B.typeMarginal i t = 0) (a : B.Act i) :
    d.dist.val (t, a) = 0 := by
  have hsum : ∑ a' : B.Act i, d.dist.val (t, a') = 0 := by
    rw [d.compatible t, ht]
  exact (Finset.sum_eq_zero_iff_of_nonneg
    (fun a' (_ : a' ∈ (Finset.univ : Finset (B.Act i))) =>
      d.dist.property.1 (t, a'))).mp hsum a (Finset.mem_univ a)

/-- A behavioral representative of a finite distributional strategy.
At a positive-probability type this is the normalized conditional action law;
at a null type an arbitrary point mass is chosen. -/
noncomputable def distributionalStrategyToBehavior
    (B : BayesianGame N) (i : N) (d : B.DistributionalStrategy i) :
    B.BehaviorStrategy i := by
  classical
  exact fun t =>
    if h : 0 < B.typeMarginal i t then
      ⟨fun a => d.dist.val (t, a) / B.typeMarginal i t,
        fun a => div_nonneg (d.dist.property.1 (t, a)) h.le,
        by
          show (∑ a : B.Act i, d.dist.val (t, a) / B.typeMarginal i t) = 1
          simp only [div_eq_mul_inv, ← Finset.sum_mul, d.compatible t]
          exact mul_inv_cancel₀ (ne_of_gt h)⟩
    else stdSimplex.pure (Classical.arbitrary (B.Act i))

/-- Every finite distributional strategy is induced by its canonical
behavioral representative. At null types both sides of the joint-law identity
are zero; only the conditional representative itself is non-unique. -/
theorem distributionalStrategyToBehavior_isInduced
    (B : BayesianGame N) (i : N) (d : B.DistributionalStrategy i) :
    B.IsInducedByBehaviorStrategy i (B.distributionalStrategyToBehavior i d) d := by
  classical
  intro t a
  by_cases ht : 0 < B.typeMarginal i t
  · simp only [distributionalStrategyToBehavior, dif_pos ht]
    exact (mul_div_cancel₀ (d.dist.val (t, a)) (ne_of_gt ht)).symm
  · have ht0 : B.typeMarginal i t = 0 :=
      le_antisymm (not_lt.mp ht) (B.typeMarginal_nonneg i t)
    rw [d.eq_zero_of_typeMarginal_eq_zero B i t ht0 a, ht0, zero_mul]

/-- In the finite model, distributional and behavioral strategies represent
exactly the same joint type-action laws. -/
theorem distributionalStrategy_corresponds_to_behaviorStrategy
    (B : BayesianGame N) (i : N) (d : B.DistributionalStrategy i) :
    ∃ β : B.BehaviorStrategy i, B.IsInducedByBehaviorStrategy i β d :=
  ⟨B.distributionalStrategyToBehavior i d,
    B.distributionalStrategyToBehavior_isInduced i d⟩

end BayesianGame

end StrategicGame
