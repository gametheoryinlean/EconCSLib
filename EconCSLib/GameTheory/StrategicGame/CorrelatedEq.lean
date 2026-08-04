/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.StrategicGame.MixedStrategy
import EconCSLib.GameTheory.StrategicGame.Nash
import EconCSLib.Math.Convex.FinitePolyhedron
import EconCSLib.Math.Simplex

/-!
# EconCSLib.GameTheory.StrategicGame.CorrelatedEq

Finite correlated equilibria, formulated both through mixed complete
contingent plans and through signal-contingent mixed actions.

The source-faithful API models MFoGT Section 7.2 literally: a pure strategy in
the information extension is a complete signal-to-action plan, and a mixed
strategy is a distribution over such plans. A second API uses behavioral
strategies, assigning a mixed action directly to every signal. In the finite
model these presentations are proved equivalent in expected payoffs, Nash
equilibria, and induced correlated-equilibrium distributions. The bridge uses
finite product distributions and their coordinate marginals.

## Main definitions

* `InformationStructure` - a finite common-prior information structure
* `PureContingentPlan` - a complete signal-to-action plan
* `contingentPlanExtension` - the pure extension in MFoGT Definition 7.2.2
* `MixedContingentPlan` - a mixed strategy over complete contingent plans
* `ExtendedStrategy` - a signal-contingent mixed action
* `extendBy` - the behavioral information extension `[G, I]`
* `IsMixedPlanCorrelatedEquilibrium` - the source's mixed Nash predicate
* `IsCorrelatedEquilibrium` - its equivalent finite behavioral realization
* `MixedContingentPlanCorrelatedEquilibriumDistributions` - the literal
  mixed-plan union in MFoGT Definition 7.2.4
* `CorrelatedEquilibriumDistributions` - the behavioral union, proved equal to
  the source's mixed-plan union
* `NashCorrelatedEquilibriumDistributions` - an explicit synonym for that union
* `IsSignalwiseCorrelatedEquilibrium` - the finite conditional-best-response form
* `SignalwiseCorrelatedEquilibriumDistributions` - distributions induced by
  signalwise-best-response profiles; proved equal to the Nash-based set
* `CanonicalCorrelatedEquilibriumDistributions` - the Nash-based canonical set
  from MFoGT Definition 7.2.5
* `MixedPlanCanonicalCorrelatedEquilibriumDistributions` - the same canonical
  set stated literally with the identity contingent-plan profile
* `SignalwiseCanonicalCorrelatedEquilibriumDistributions` - its equivalent ex-post form
* `IsCorrelatedEq` - the finite global obedience characterization

## Main results

* `nash_iff_degenerate_ce` - unfolding lemma for the profile-level degenerate shorthand
* `expectedPayoff_contingentPlanExtension_eq_extendBy` - mixed-plan and
  behavioral expected payoffs agree
* `isMixedContingentPlanNashEquilibrium_iff_behavioral` - mixed-plan and
  behavioral Nash equilibria agree under marginalization
* `mixedContingentPlanCorrelatedEquilibriumDistributions_eq_behavioral` - the
  two definitions induce the same `CED(G)`
* `isExtendedNashEquilibrium_iff_signalwise` - finite ex-ante/ex-post equivalence
* `isExtendedNashEquilibrium_trivial_iff_isMixedNashEq` - trivial information
  recovers ordinary mixed Nash equilibrium
* `piProduct_mem_correlatedEquilibriumDistributions_of_isMixedNashEq` - [MSZ
  Theorem 8.7]: the product distribution of a mixed Nash equilibrium is a
  correlated equilibrium
* `piProduct_mem_correlatedEquilibriumDistributions_of_mixedNashEquilibrium` -
  the same theorem for the all-mixed-deviations predicate returned by the
  library's Nash existence theorem
* `vertex_mem_correlatedEquilibriumDistributions_iff_isNashEquilibrium` - a
  point-mass distribution is correlated exactly at a pure Nash equilibrium
* `inducedDistribution_canonical_truthful` - canonical truthful play induces its prior
* `behaviorProfileToMixedContingentPlan_canonical_truthful` - the behavioral
  truthful profile couples to the point mass on the identity contingent plan
* `canonicalCorrelatedEquilibriumDistributions_eq_correlatedEquilibriumDistributions`
  - MFoGT Theorem 7.2.6
* `mixedPlanCanonicalCorrelatedEquilibriumDistributions_eq_mixedPlanCED` - the
  source-literal identity-plan form of MFoGT Theorem 7.2.6
* `mem_correlatedEquilibriumDistributions_iff_obedience` - MFoGT Theorem 7.2.7
* `correlatedEquilibriumDistributions_eq_finiteLinearInequalitySet` - the exact
  finite linear-inequality description used in MFoGT Corollary 7.2.8
* `correlatedEquilibriumDistributions_image_convex` - convexity of `CED(G)`
* `correlatedEquilibriumDistributions_eq_convexHull_finset` - MFoGT
  Corollary 7.2.8: `CED(G)` is the convex hull of finitely many points
* `correlatedEquilibriumDistributions_image_isCompact` - compactness of the
  finite real `CED(G)`

The source's mixed-plan, behavioral Nash, conditional-best-response,
actionwise-obedience, and canonical presentations are connected by proved
equivalences. The finite H-description, convexity, and finite convex-hull
representation in MFoGT Corollary 7.2.8 are all proved. The final geometric
theorem is stated for real payoffs, matching the source's finite-dimensional
real probability model.

## References

* [MSZ] Chapter 8, especially Section 8.2
* [MFoGT] Chapter 7, Section 7.2
-/

open Finset BigOperators

namespace StrategicGame

universe uOmega uSignal u_N u_U u_S

variable {N : Type u_N} {U : Type u_U}

section Degenerate

variable [DecidableEq N] [Preorder U]

/-- Profile-level shorthand: a pure profile is degenerately correlated exactly
when it is a pure Nash equilibrium. -/
def IsDegenerateCorrelatedEq (G : StrategicGame N U) (sigma : G.Profile) : Prop :=
  IsNashEquilibrium G sigma

/-- Unfolding lemma for the profile-level degenerate shorthand. -/
theorem nash_iff_degenerate_ce (G : StrategicGame N U) (sigma : G.Profile) :
    IsNashEquilibrium G sigma ↔ IsDegenerateCorrelatedEq G sigma := by
  exact Iff.rfl

end Degenerate

section FiniteCorrelatedEquilibrium

variable [Fintype N] [DecidableEq N]
variable [Field U] [LinearOrder U] [IsStrictOrderedRing U]

set_option linter.unusedSectionVars false

/-! ### MFoGT 7.2.2: information structures and finite extensions -/

/-- Finite specialization of [MFoGT Definition 7.2.1].

The measurable spaces in the source become finite discrete spaces. The prior
uses the same ordered field as payoffs; taking `U = ℝ` gives the source's
real probability model. -/
structure InformationStructure (G : StrategicGame N U)
    (Omega : Type uOmega) [Fintype Omega] where
  /-- Player `i`'s finite signal space. -/
  Signal : N -> Type uSignal
  /-- Every signal space is finite. -/
  [signalFintype : ∀ i : N, Fintype (Signal i)]
  /-- Equality of finite signals is decidable. -/
  [signalDecidableEq : ∀ i : N, DecidableEq (Signal i)]
  /-- The common prior on the event space. -/
  prior : stdSimplex U Omega
  /-- The signal observed by player `i` at an event. -/
  signal : (i : N) -> Omega -> Signal i

attribute [instance] InformationStructure.signalFintype
attribute [instance] InformationStructure.signalDecidableEq

variable {G : StrategicGame.{u_N, u_U, u_S} N U}
variable [∀ i : N, Fintype (G.strategy i)]
variable [∀ i : N, DecidableEq (G.strategy i)]

/-! #### The source's contingent-plan extension -/

/-- A pure contingent plan maps every signal of player `i` to a pure action.
This is the pure strategy space in MFoGT Definition 7.2.2. -/
abbrev PureContingentPlan {Omega : Type uOmega} [Fintype Omega]
    (I : InformationStructure G Omega) (i : N) :=
  I.Signal i → G.strategy i

/-- A profile of pure signal-contingent plans. -/
abbrev PureContingentPlanProfile {Omega : Type uOmega} [Fintype Omega]
    (I : InformationStructure G Omega) :=
  ∀ i : N, PureContingentPlan I i

/-- The base-game action profile realized by a contingent-plan profile at
event `omega`. -/
def realizedContingentPlanProfile {Omega : Type uOmega} [Fintype Omega]
    (I : InformationStructure G Omega) (plan : PureContingentPlanProfile I)
    (omega : Omega) : G.Profile :=
  fun i => plan i (I.signal i omega)

/-- The pure contingent-plan extension `[G, I]` from MFoGT Definition 7.2.2.
Its pure strategies are signal-to-action maps and its payoff is the prior
expectation of the realized base-game payoff. -/
noncomputable def contingentPlanExtension (G : StrategicGame N U)
    [∀ i : N, Fintype (G.strategy i)]
    {Omega : Type uOmega} [Fintype Omega]
    (I : InformationStructure G Omega) : StrategicGame N U where
  strategy i := PureContingentPlan I i
  payoff plan i :=
    ∑ omega : Omega, I.prior.val omega *
      G.payoff (realizedContingentPlanProfile I plan omega) i

instance contingentPlanExtension_strategyFintype
    {Omega : Type uOmega} [Fintype Omega]
    (I : InformationStructure G Omega) (i : N) :
    Fintype ((contingentPlanExtension G I).strategy i) := by
  change Fintype (I.Signal i → G.strategy i)
  infer_instance

instance contingentPlanExtension_strategyDecidableEq
    {Omega : Type uOmega} [Fintype Omega]
    (I : InformationStructure G Omega) (i : N) :
    DecidableEq ((contingentPlanExtension G I).strategy i) := by
  change DecidableEq (I.Signal i → G.strategy i)
  infer_instance

/-- A mixed strategy over the source's pure contingent plans. -/
abbrev MixedContingentPlan {Omega : Type uOmega} [Fintype Omega]
    (I : InformationStructure G Omega) (i : N) :=
  MixedStrategy (contingentPlanExtension G I) i

/-- A mixed-strategy profile of the source's contingent-plan extension. -/
abbrev MixedContingentPlanProfile {Omega : Type uOmega} [Fintype Omega]
    (I : InformationStructure G Omega) :=
  MixedProfile (contingentPlanExtension G I)

/-- A strategy in the finite behavioral extension `[G, I]` assigns a mixed
action to each signal, as in the finite formula following MFoGT Definition
7.2.3. A deterministic signal-to-action rule is the special case obtained with
point masses. -/
abbrev ExtendedStrategy {Omega : Type uOmega} [Fintype Omega]
    (I : InformationStructure G Omega) (i : N) :=
  I.Signal i -> MixedStrategy G i

/-- A profile of signal-contingent mixed actions in `[G, I]`. -/
abbrev ExtendedProfile {Omega : Type uOmega} [Fintype Omega]
    (I : InformationStructure G Omega) :=
  ∀ i : N, ExtendedStrategy I i

/-- Marginalize a mixed contingent plan at each signal to obtain its
behavioral realization. -/
noncomputable def mixedContingentPlanToBehavior
    {Omega : Type uOmega} [Fintype Omega]
    (I : InformationStructure G Omega) (i : N)
    (mu : MixedContingentPlan I i) : ExtendedStrategy I i :=
  fun a => stdSimplex.coordinateMarginal mu a

/-- Marginalize every player's mixed contingent plan to a behavioral profile. -/
noncomputable def mixedContingentPlanProfileToBehavior
    {Omega : Type uOmega} [Fintype Omega]
    (I : InformationStructure G Omega) (mu : MixedContingentPlanProfile I) :
    ExtendedProfile I :=
  fun i => mixedContingentPlanToBehavior I i (mu i)

/-- Independently couple a player's signalwise mixed actions into a
distribution over complete contingent plans. -/
noncomputable def behaviorToMixedContingentPlan
    {Omega : Type uOmega} [Fintype Omega]
    (I : InformationStructure G Omega) (i : N)
    (sigma : ExtendedStrategy I i) : MixedContingentPlan I i :=
  stdSimplex.piProduct sigma

/-- Independently couple every player's behavioral strategy into a mixed
contingent-plan profile. -/
noncomputable def behaviorProfileToMixedContingentPlan
    {Omega : Type uOmega} [Fintype Omega]
    (I : InformationStructure G Omega) (sigma : ExtendedProfile I) :
    MixedContingentPlanProfile I :=
  fun i => behaviorToMixedContingentPlan I i (sigma i)

/-- Product coupling followed by signalwise marginalization recovers the
original behavioral strategy. -/
theorem mixedContingentPlanToBehavior_behaviorToMixedContingentPlan
    {Omega : Type uOmega} [Fintype Omega]
    (I : InformationStructure G Omega) (i : N) (sigma : ExtendedStrategy I i) :
    mixedContingentPlanToBehavior I i
        (behaviorToMixedContingentPlan I i sigma) = sigma := by
  funext a
  exact stdSimplex.coordinateMarginal_piProduct sigma a

/-- Product coupling followed by marginalization recovers the original
behavioral profile. -/
theorem mixedContingentPlanProfileToBehavior_behaviorProfileToMixedContingentPlan
    {Omega : Type uOmega} [Fintype Omega]
    (I : InformationStructure G Omega) (sigma : ExtendedProfile I) :
    mixedContingentPlanProfileToBehavior I
        (behaviorProfileToMixedContingentPlan I sigma) = sigma := by
  funext i
  exact mixedContingentPlanToBehavior_behaviorToMixedContingentPlan I i (sigma i)

/-- Signalwise marginalization commutes with replacing one player's mixed
contingent plan. -/
theorem mixedContingentPlanProfileToBehavior_update
    {Omega : Type uOmega} [Fintype Omega]
    (I : InformationStructure G Omega) (mu : MixedContingentPlanProfile I)
    (i : N) (nu : MixedContingentPlan I i) :
    mixedContingentPlanProfileToBehavior I (Function.update mu i nu) =
      Function.update (mixedContingentPlanProfileToBehavior I mu) i
        (mixedContingentPlanToBehavior I i nu) := by
  funext j
  by_cases hji : j = i
  · subst j
    simp [mixedContingentPlanProfileToBehavior]
  · simp [mixedContingentPlanProfileToBehavior, hji]

/-- The mixed-action profile selected by an extended profile at event `omega`. -/
def extendedMixedProfile {Omega : Type uOmega} [Fintype Omega]
    (I : InformationStructure G Omega) (sigma : ExtendedProfile I) (omega : Omega) :
    MixedProfile G :=
  fun i => sigma i (I.signal i omega)

/-- Conditional probability of pure action profile `s` at event `omega`.

This is the product probability `q(omega, sigma)` displayed after MFoGT
Definition 7.2.3. Conditional independence here represents independent private
randomization by the players after observing their signals. -/
noncomputable def extendedActionProbability {Omega : Type uOmega} [Fintype Omega]
    (I : InformationStructure G Omega) (sigma : ExtendedProfile I)
    (omega : Omega) (s : G.Profile) : U :=
  ∏ i : N, (extendedMixedProfile I sigma omega i).val (s i)

/-- Finite behavioral extension `[G, I]` corresponding to MFoGT Definition
7.2.2. Its strategy space consists of signal-contingent mixed actions, and its
payoff averages the base-game payoff over the common prior and the players'
independent private randomization. -/
noncomputable def extendBy (G : StrategicGame N U)
    [∀ i : N, Fintype (G.strategy i)]
    {Omega : Type uOmega} [Fintype Omega]
    (I : InformationStructure G Omega) : StrategicGame N U where
  strategy i := ExtendedStrategy I i
  payoff sigma i :=
    ∑ omega : Omega, I.prior.val omega *
      ∑ s : G.Profile,
        extendedActionProbability I sigma omega s * G.payoff s i

/-- The ex-ante payoff in `[G, I]`, unfolded as the state expectation of the
conditional product-distribution payoff. -/
theorem extendBy_payoff {Omega : Type uOmega} [Fintype Omega]
    (I : InformationStructure G Omega) (sigma : (extendBy G I).Profile) (i : N) :
    (extendBy G I).payoff sigma i =
      ∑ omega : Omega, I.prior.val omega *
        ∑ s : G.Profile,
          extendedActionProbability I sigma omega s * G.payoff s i :=
  rfl

/-- At every event, independently mixed contingent plans induce exactly the
product distribution of their signalwise behavioral marginals. -/
theorem map_piProduct_mixedContingentPlanProfile
    {Omega : Type uOmega} [Fintype Omega]
    (I : InformationStructure G Omega) (mu : MixedContingentPlanProfile I)
    (omega : Omega) :
    stdSimplex.map (fun plan => realizedContingentPlanProfile I plan omega)
        (stdSimplex.piProduct mu) =
      stdSimplex.piProduct
        (extendedMixedProfile I
          (mixedContingentPlanProfileToBehavior I mu) omega) := by
  simpa [realizedContingentPlanProfile, extendedMixedProfile,
    mixedContingentPlanProfileToBehavior, mixedContingentPlanToBehavior] using
    (stdSimplex.map_piProduct (𝕜 := U)
      (fun i (plan : PureContingentPlan I i) => plan (I.signal i omega)) mu)

/-- At a fixed event, the expected base-game payoff under mixed complete plans
equals the expected payoff under their behavioral marginals. -/
theorem mixedContingentPlanProfile_statePayoff_eq_behavior
    {Omega : Type uOmega} [Fintype Omega]
    (I : InformationStructure G Omega) (mu : MixedContingentPlanProfile I)
    (omega : Omega) (who : N) :
    (∑ plan : PureContingentPlanProfile I,
        (∏ i : N, (mu i).val (plan i)) *
          G.payoff (realizedContingentPlanProfile I plan omega) who) =
      ∑ s : G.Profile,
        extendedActionProbability I
            (mixedContingentPlanProfileToBehavior I mu) omega s *
          G.payoff s who := by
  have hmap := map_piProduct_mixedContingentPlanProfile I mu omega
  have hchange := stdSimplex.wsum_map (𝕜 := U)
    (fun plan => realizedContingentPlanProfile I plan omega)
    (stdSimplex.piProduct mu) (fun s => G.payoff s who)
  rw [hmap] at hchange
  simpa [wsum, dotProduct, extendedActionProbability,
    stdSimplex.piProduct_apply, Function.comp_def] using hchange.symm

/-- **Finite mixed-plan/behavioral payoff equivalence.** The mixed expected
payoff of the source's contingent-plan extension is exactly the pure payoff of
the behavioral extension at the signalwise marginals. -/
theorem expectedPayoff_contingentPlanExtension_eq_extendBy
    {Omega : Type uOmega} [Fintype Omega]
    (I : InformationStructure G Omega) (mu : MixedContingentPlanProfile I)
    (who : N) :
    expectedPayoff (contingentPlanExtension G I) mu who =
      (extendBy G I).payoff
        (mixedContingentPlanProfileToBehavior I mu) who := by
  classical
  unfold expectedPayoff contingentPlanExtension
  rw [extendBy_payoff]
  calc
    (∑ plan : PureContingentPlanProfile I,
        (∏ i : N, (mu i).val (plan i)) *
          ∑ omega : Omega, I.prior.val omega *
            G.payoff (realizedContingentPlanProfile I plan omega) who) =
        ∑ omega : Omega, I.prior.val omega *
          ∑ plan : PureContingentPlanProfile I,
            (∏ i : N, (mu i).val (plan i)) *
              G.payoff (realizedContingentPlanProfile I plan omega) who := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro omega _
      apply Finset.sum_congr rfl
      intro plan _
      ring
    _ = ∑ omega : Omega, I.prior.val omega *
          ∑ s : G.Profile,
            extendedActionProbability I
                (mixedContingentPlanProfileToBehavior I mu) omega s *
              G.payoff s who := by
      apply Finset.sum_congr rfl
      intro omega _
      rw [mixedContingentPlanProfile_statePayoff_eq_behavior]

/-- Nash equilibrium of the finite behavioral extension `[G, I]`. Its exact
equivalence with the source's mixed contingent-plan equilibrium is proved by
`isMixedContingentPlanNashEquilibrium_iff_behavioral`. -/
def IsExtendedNashEquilibrium {Omega : Type uOmega} [Fintype Omega]
    (I : InformationStructure G Omega) (sigma : (extendBy G I).Profile) : Prop :=
  IsNashEquilibrium (extendBy G I) sigma

/-- Mixed Nash equilibrium of the source's contingent-plan extension from
MFoGT Definition 7.2.3. -/
def IsMixedContingentPlanNashEquilibrium
    {Omega : Type uOmega} [Fintype Omega]
    (I : InformationStructure G Omega) (mu : MixedContingentPlanProfile I) : Prop :=
  IsMixedNashEq (contingentPlanExtension G I) mu

/-- Source-faithful correlated-equilibrium predicate: a mixed Nash equilibrium
over complete contingent plans. -/
abbrev IsMixedPlanCorrelatedEquilibrium
    {Omega : Type uOmega} [Fintype Omega]
    (I : InformationStructure G Omega) (mu : MixedContingentPlanProfile I) : Prop :=
  IsMixedContingentPlanNashEquilibrium I mu

/-- Behavioral realization of MFoGT Definition 7.2.3: a correlated equilibrium
of `G` relative to `I` is a Nash equilibrium of the behavioral extension. The
mixed-plan predicate matching the source literally is
`IsMixedPlanCorrelatedEquilibrium`. -/
abbrev IsCorrelatedEquilibrium {Omega : Type uOmega} [Fintype Omega]
    (I : InformationStructure G Omega) (sigma : (extendBy G I).Profile) : Prop :=
  IsExtendedNashEquilibrium I sigma

/-! #### Conditional best responses and the ex-ante/ex-post bridge -/

private noncomputable def redirectMixed (i : N) (p : MixedStrategy G i)
    (s t : G.strategy i) : MixedStrategy G i := by
  classical
  by_cases hst : s = t
  · exact p
  · refine ⟨fun r => if r = s then 0 else if r = t then p.val t + p.val s else p.val r,
      ?_⟩
    have hts : t ≠ s := Ne.symm hst
    constructor
    · intro r
      change 0 ≤ if r = s then 0 else if r = t then p.val t + p.val s else p.val r
      by_cases hrs : r = s
      · simp [hrs]
      · by_cases hrt : r = t
        · subst r
          rw [if_neg hts, if_pos rfl]
          exact add_nonneg (p.property.1 t) (p.property.1 s)
        · simp [hrs, hrt, p.property.1]
    · rw [← p.property.2]
      let f : G.strategy i → U :=
        fun r => if r = s then 0 else if r = t then p.val t + p.val s else p.val r
      have hfs : f s = 0 := by simp [f]
      have ht : t ∈ Finset.univ.erase s := by simp [hts]
      have hrest :
          (∑ r ∈ (Finset.univ.erase s).erase t, f r) =
            ∑ r ∈ (Finset.univ.erase s).erase t, p.val r := by
        apply Finset.sum_congr rfl
        intro r hr
        have hrs : r ≠ s :=
          (Finset.mem_erase.mp (Finset.mem_of_mem_erase hr)).1
        have hrt : r ≠ t := (Finset.mem_erase.mp hr).1
        simp [f, hrs, hrt]
      change (∑ r, f r) = ∑ r, p.val r
      calc
        (∑ r, f r) = ∑ r ∈ Finset.univ.erase s, f r := by
          symm
          exact Finset.sum_erase Finset.univ hfs
        _ = (∑ r ∈ (Finset.univ.erase s).erase t, f r) + f t :=
          (Finset.sum_erase_add (Finset.univ.erase s) f ht).symm
        _ = (∑ r ∈ (Finset.univ.erase s).erase t, p.val r) +
            (p.val t + p.val s) := by rw [hrest]; simp [f, hts]
        _ = ∑ r, p.val r := by
          rw [← Finset.sum_erase_add Finset.univ p.val (Finset.mem_univ s)]
          rw [← Finset.sum_erase_add (Finset.univ.erase s) p.val ht]
          ring

private theorem redirectMixed_apply_self (i : N) (p : MixedStrategy G i)
    (s t : G.strategy i) :
    (redirectMixed i p s t).val s = if s = t then p.val s else 0 := by
  classical
  by_cases hst : s = t
  · simp [redirectMixed, hst]
  · simp [redirectMixed, hst]

private theorem redirectMixed_apply_target (i : N) (p : MixedStrategy G i)
    (s t : G.strategy i) :
    (redirectMixed i p s t).val t =
      if s = t then p.val t else p.val t + p.val s := by
  classical
  by_cases hst : s = t
  · simp [redirectMixed, hst]
  · have hts : t ≠ s := Ne.symm hst
    simp [redirectMixed, hst, hts]

private abbrev OpponentProfile (G : StrategicGame N U) (i : N) :=
  ∀ j : {j : N // j ≠ i}, G.strategy j

private def profileFrom (G : StrategicGame N U) [DecidableEq N] (i : N)
    (s : G.strategy i) (r : OpponentProfile G i) : G.Profile :=
  (Equiv.piSplitAt i G.strategy).symm (s, r)

private noncomputable def opponentProbability (p : MixedProfile G) (i : N)
    (r : OpponentProfile G i) : U :=
  ∏ j : {j : N // j ≠ i}, (p j).val (r j)

private noncomputable def pureActionPayoffAgainst (p : MixedProfile G) (i : N)
    (s : G.strategy i) : U :=
  ∑ r : OpponentProfile G i,
    opponentProbability p i r * G.payoff (profileFrom G i s r) i

private theorem expectedPayoff_eq_sum_own_action (p : MixedProfile G) (i : N) :
    expectedPayoff G p i =
      ∑ s : G.strategy i, (p i).val s * pureActionPayoffAgainst p i s := by
  classical
  unfold expectedPayoff
  let e := Equiv.piSplitAt i G.strategy
  rw [← e.symm.sum_comp]
  rw [Fintype.sum_prod_type]
  unfold pureActionPayoffAgainst
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  change
    (∏ j : N, (p j).val ((profileFrom G i s r) j)) * G.payoff (profileFrom G i s r) i =
      (p i).val s * (opponentProbability p i r * G.payoff (profileFrom G i s r) i)
  rw [Fintype.prod_eq_mul_prod_subtype_ne]
  have hself : profileFrom G i s r i = s := by
    simp [profileFrom, Equiv.piSplitAt_symm_apply]
  rw [hself]
  have hopp :
      (∏ j : {j : N // j ≠ i}, (p j).val (profileFrom G i s r j)) =
        opponentProbability p i r := by
    unfold opponentProbability
    apply Fintype.prod_congr
    intro j
    simp [profileFrom, Equiv.piSplitAt_symm_apply, j.property]
  rw [hopp]
  ring

private theorem profileFrom_apply_self (i : N) (s : G.strategy i)
    (r : OpponentProfile G i) :
    profileFrom G i s r i = s := by
  simp [profileFrom, Equiv.piSplitAt_symm_apply]

private theorem deviate_profileFrom (i : N) (s t : G.strategy i)
    (r : OpponentProfile G i) :
    deviate (profileFrom G i s r) i t = profileFrom G i t r := by
  funext j
  by_cases hji : j = i
  · subst j
    simp [profileFrom_apply_self]
  · simp [deviate, profileFrom, Equiv.piSplitAt_symm_apply, hji]

private theorem actionObedienceSum_eq_weighted_pureActionPayoff
    (p : MixedProfile G) (i : N) (s t : G.strategy i) :
    (∑ rho : G.Profile,
      if rho i = s then
        (∏ j : N, (p j).val (rho j)) *
          (G.payoff rho i - G.payoff (deviate rho i t) i)
      else 0) =
      (p i).val s *
        (pureActionPayoffAgainst p i s - pureActionPayoffAgainst p i t) := by
  classical
  let e := Equiv.piSplitAt i G.strategy
  rw [← e.symm.sum_comp]
  rw [Fintype.sum_prod_type]
  change
    (∑ u : G.strategy i, ∑ r : OpponentProfile G i,
      if profileFrom G i u r i = s then
        (∏ j : N, (p j).val (profileFrom G i u r j)) *
          (G.payoff (profileFrom G i u r) i -
            G.payoff (deviate (profileFrom G i u r) i t) i)
      else 0) =
      (p i).val s *
        (pureActionPayoffAgainst p i s - pureActionPayoffAgainst p i t)
  rw [Finset.sum_eq_single s]
  · simp only [profileFrom_apply_self, if_true]
    unfold pureActionPayoffAgainst
    rw [mul_sub]
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro r _
    rw [Fintype.prod_eq_mul_prod_subtype_ne]
    rw [profileFrom_apply_self]
    have hopp :
        (∏ j : {j : N // j ≠ i},
          (p j).val (profileFrom G i s r j)) = opponentProbability p i r := by
      unfold opponentProbability
      apply Fintype.prod_congr
      intro j
      simp [profileFrom, Equiv.piSplitAt_symm_apply, j.property]
    rw [hopp, deviate_profileFrom]
    ring
  · intro u _ hus
    simp [profileFrom_apply_self, hus]
  · intro hs
    exact (hs (Finset.mem_univ s)).elim

private theorem opponentProbability_update_self (p : MixedProfile G) (i : N)
    (mu : MixedStrategy G i) (r : OpponentProfile G i) :
    opponentProbability (Function.update p i mu) i r = opponentProbability p i r := by
  classical
  unfold opponentProbability
  apply Fintype.prod_congr
  intro j
  simp [Function.update_of_ne j.property]

private theorem pureActionPayoffAgainst_update_self (p : MixedProfile G) (i : N)
    (mu : MixedStrategy G i) (s : G.strategy i) :
    pureActionPayoffAgainst (Function.update p i mu) i s =
      pureActionPayoffAgainst p i s := by
  classical
  unfold pureActionPayoffAgainst
  apply Finset.sum_congr rfl
  intro r _
  rw [opponentProbability_update_self]

private theorem expectedPayoff_update_pure (p : MixedProfile G) (i : N)
    (s : G.strategy i) :
    expectedPayoff G (Function.update p i (pureToMixed s)) i =
      pureActionPayoffAgainst p i s := by
  classical
  rw [expectedPayoff_eq_sum_own_action]
  simp_rw [pureActionPayoffAgainst_update_self]
  simp [Function.update_self, pureToMixed]

private theorem expectedPayoff_update_eq_sum_pureActionPayoff
    (p : MixedProfile G) (i : N) (mu : MixedStrategy G i) :
    expectedPayoff G (Function.update p i mu) i =
      ∑ s : G.strategy i, mu.val s * pureActionPayoffAgainst p i s := by
  classical
  rw [expectedPayoff_eq_sum_own_action]
  simp_rw [pureActionPayoffAgainst_update_self]
  simp [Function.update_self]

private theorem expectedPayoff_update_le_of_isMixedNashEq
    (p : MixedProfile G) (h : IsMixedNashEq G p) (i : N)
    (mu : MixedStrategy G i) :
    expectedPayoff G (Function.update p i mu) i ≤ expectedPayoff G p i := by
  rw [expectedPayoff_update_eq_sum_pureActionPayoff]
  calc
    (∑ s : G.strategy i, mu.val s * pureActionPayoffAgainst p i s) =
        ∑ s : G.strategy i, mu.val s *
          expectedPayoff G (deviateMixed G p i s) i := by
      apply Finset.sum_congr rfl
      intro s _
      rw [deviateMixed, expectedPayoff_update_pure]
    _ ≤ ∑ s : G.strategy i, mu.val s * expectedPayoff G p i := by
      apply Finset.sum_le_sum
      intro s _
      exact mul_le_mul_of_nonneg_left (h i s) (mu.property.1 s)
    _ = expectedPayoff G p i := by
      rw [← Finset.sum_mul, mu.property.2, one_mul]

/-- **Finite mixed-plan/behavioral Nash equivalence.** A mixed profile over the
source's complete contingent plans is Nash exactly when its signalwise action
marginals form a Nash equilibrium of the behavioral extension. -/
theorem isMixedContingentPlanNashEquilibrium_iff_behavioral
    {Omega : Type uOmega} [Fintype Omega]
    (I : InformationStructure G Omega) (mu : MixedContingentPlanProfile I) :
    IsMixedContingentPlanNashEquilibrium I mu ↔
      IsExtendedNashEquilibrium I
        (mixedContingentPlanProfileToBehavior I mu) := by
  constructor
  · intro hplan i tau
    let nu : MixedContingentPlan I i :=
      behaviorToMixedContingentPlan I i tau
    have hdev := expectedPayoff_update_le_of_isMixedNashEq mu hplan i nu
    rw [expectedPayoff_contingentPlanExtension_eq_extendBy I
          (Function.update mu i nu) i,
        expectedPayoff_contingentPlanExtension_eq_extendBy I mu i,
        mixedContingentPlanProfileToBehavior_update,
        mixedContingentPlanToBehavior_behaviorToMixedContingentPlan] at hdev
    exact hdev
  · intro hbehavior i plan
    let nu : MixedContingentPlan I i := pureToMixed plan
    have hdev := hbehavior i (mixedContingentPlanToBehavior I i nu)
    change expectedPayoff (contingentPlanExtension G I)
        (deviateMixed (contingentPlanExtension G I) mu i plan) i ≤
      expectedPayoff (contingentPlanExtension G I) mu i
    rw [deviateMixed]
    rw [expectedPayoff_contingentPlanExtension_eq_extendBy I
          (Function.update mu i nu) i,
        expectedPayoff_contingentPlanExtension_eq_extendBy I mu i,
        mixedContingentPlanProfileToBehavior_update]
    exact hdev

/-- Every behavioral profile has a canonical independent mixed-plan
realization, and equilibrium is preserved and reflected by that realization. -/
theorem isMixedContingentPlanNashEquilibrium_behaviorProfile_iff
    {Omega : Type uOmega} [Fintype Omega]
    (I : InformationStructure G Omega) (sigma : ExtendedProfile I) :
    IsMixedContingentPlanNashEquilibrium I
        (behaviorProfileToMixedContingentPlan I sigma) ↔
      IsExtendedNashEquilibrium I sigma := by
  rw [isMixedContingentPlanNashEquilibrium_iff_behavioral,
    mixedContingentPlanProfileToBehavior_behaviorProfileToMixedContingentPlan]

/-- The unnormalized expected payoff on the event where player `i` observes
signal `a`, when that player uses mixed action `mu` and all opponents keep the
behavior prescribed by `sigma`.

Using an unnormalized event payoff avoids division by the probability of `a`.
For a positive-probability signal, comparing these values is exactly the
conditional best-response comparison in the paragraph following MFoGT
Definition 7.2.2; for a null signal every value is zero. -/
noncomputable def signalExpectedPayoff
    {Omega : Type uOmega} [Fintype Omega]
    (I : InformationStructure G Omega) (sigma : ExtendedProfile I)
    (i : N) (a : I.Signal i) (mu : MixedStrategy G i) : U :=
  ∑ omega : Omega,
    if I.signal i omega = a then
      I.prior.val omega *
        expectedPayoff G (Function.update (extendedMixedProfile I sigma omega) i mu) i
    else 0

/-- Unnormalized payoff on signal `a` from the pure action `s`. -/
noncomputable def signalPureActionPayoff
    {Omega : Type uOmega} [Fintype Omega]
    (I : InformationStructure G Omega) (sigma : ExtendedProfile I)
    (i : N) (a : I.Signal i) (s : G.strategy i) : U :=
  signalExpectedPayoff I sigma i a (pureToMixed s)

private theorem signalExpectedPayoff_eq_sum_pure
    {Omega : Type uOmega} [Fintype Omega]
    (I : InformationStructure G Omega) (sigma : ExtendedProfile I)
    (i : N) (a : I.Signal i) (mu : MixedStrategy G i) :
    signalExpectedPayoff I sigma i a mu =
      ∑ s : G.strategy i,
        mu.val s * signalPureActionPayoff I sigma i a s := by
  classical
  unfold signalExpectedPayoff signalPureActionPayoff
  simp_rw [signalExpectedPayoff]
  simp_rw [expectedPayoff_update_pure]
  simp_rw [expectedPayoff_update_eq_sum_pureActionPayoff]
  calc
    (∑ omega : Omega,
      if I.signal i omega = a then
        I.prior.val omega *
          ∑ s : G.strategy i,
            mu.val s * pureActionPayoffAgainst (extendedMixedProfile I sigma omega) i s
      else 0) =
        ∑ omega : Omega, ∑ s : G.strategy i,
          mu.val s *
            (if I.signal i omega = a then
              I.prior.val omega *
                pureActionPayoffAgainst (extendedMixedProfile I sigma omega) i s
            else 0) := by
      apply Finset.sum_congr rfl
      intro omega _
      by_cases hsig : I.signal i omega = a
      · simp only [hsig, if_true, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro s _
        ring
      · simp [hsig]
    _ = ∑ s : G.strategy i, ∑ omega : Omega,
          mu.val s *
            (if I.signal i omega = a then
              I.prior.val omega *
                pureActionPayoffAgainst (extendedMixedProfile I sigma omega) i s
            else 0) := by rw [Finset.sum_comm]
    _ = ∑ s : G.strategy i, mu.val s *
        ∑ omega : Omega,
          if I.signal i omega = a then
            I.prior.val omega *
              pureActionPayoffAgainst (extendedMixedProfile I sigma omega) i s
          else 0 := by
      apply Finset.sum_congr rfl
      intro s _
      rw [Finset.mul_sum]

/-- Contribution of signal `a` and realized own action `s` to the payoff loss
from replacing `s` by `t`.

The expression is deliberately unnormalized. A zero-probability signal or a
zero-probability action in the mixed action contributes zero, while every
positive-probability signal/action pair imposes its usual conditional
best-response inequality. -/
noncomputable def signalObedienceDifference
    {Omega : Type uOmega} [Fintype Omega]
    (I : InformationStructure G Omega) (sigma : ExtendedProfile I)
    (i : N) (a : I.Signal i) (s t : G.strategy i) : U :=
  ∑ rho : G.Profile,
    if rho i = s then
      ∑ omega : Omega,
        if I.signal i omega = a then
          I.prior.val omega * extendedActionProbability I sigma omega rho *
            (G.payoff rho i - G.payoff (deviate rho i t) i)
        else 0
    else 0

/-- The actionwise obedience contribution is the probability of action `s`
times its conditional payoff advantage over `t`. -/
theorem signalObedienceDifference_eq_weighted_purePayoff
    {Omega : Type uOmega} [Fintype Omega]
    (I : InformationStructure G Omega) (sigma : ExtendedProfile I)
    (i : N) (a : I.Signal i) (s t : G.strategy i) :
    signalObedienceDifference I sigma i a s t =
      (sigma i a).val s *
        (signalPureActionPayoff I sigma i a s -
          signalPureActionPayoff I sigma i a t) := by
  classical
  unfold signalObedienceDifference
  have hpush :
      (∑ rho : G.Profile,
        if rho i = s then
          ∑ omega : Omega,
            if I.signal i omega = a then
              I.prior.val omega * extendedActionProbability I sigma omega rho *
                (G.payoff rho i - G.payoff (deviate rho i t) i)
            else 0
        else 0) =
        ∑ rho : G.Profile,
          ∑ omega : Omega,
            if rho i = s then
              (if I.signal i omega = a then
                I.prior.val omega * extendedActionProbability I sigma omega rho *
                  (G.payoff rho i - G.payoff (deviate rho i t) i)
              else 0)
            else 0 := by
    apply Finset.sum_congr rfl
    intro rho _
    by_cases hrho : rho i = s <;> simp [hrho]
  rw [hpush]
  rw [Finset.sum_comm]
  have hrearrange :
      (∑ omega : Omega,
        ∑ rho : G.Profile,
          if rho i = s then
            (if I.signal i omega = a then
              I.prior.val omega * extendedActionProbability I sigma omega rho *
                (G.payoff rho i - G.payoff (deviate rho i t) i)
            else 0)
          else 0) =
        ∑ omega : Omega,
          if I.signal i omega = a then
            I.prior.val omega *
              ∑ rho : G.Profile,
                if rho i = s then
                  extendedActionProbability I sigma omega rho *
                    (G.payoff rho i - G.payoff (deviate rho i t) i)
                else 0
          else 0 := by
    apply Finset.sum_congr rfl
    intro omega _
    by_cases hsig : I.signal i omega = a
    · simp only [hsig, if_true, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro rho _
      by_cases hrho : rho i = s <;> simp [hrho]
      ring
    · simp [hsig]
  rw [hrearrange]
  simp_rw [extendedActionProbability]
  simp_rw [actionObedienceSum_eq_weighted_pureActionPayoff]
  unfold signalPureActionPayoff signalExpectedPayoff
  simp_rw [expectedPayoff_update_pure]
  rw [mul_sub, Finset.mul_sum]
  rw [Finset.mul_sum]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro omega _
  by_cases hsig : I.signal i omega = a
  · have hp : (extendedMixedProfile I sigma omega i).val s = (sigma i a).val s := by
      simp [extendedMixedProfile, hsig]
    simp only [hsig, if_true]
    rw [hp]
    ring
  · simp [hsig]

private theorem weightedSum_sub_redirectMixed
    (i : N) (p : MixedStrategy G i) (v : G.strategy i → U)
    (s t : G.strategy i) :
    (∑ r : G.strategy i, p.val r * v r) -
        ∑ r : G.strategy i, (redirectMixed i p s t).val r * v r =
      p.val s * (v s - v t) := by
  classical
  by_cases hst : s = t
  · subst t
    simp [redirectMixed]
  · have hts : t ≠ s := Ne.symm hst
    have ht : t ∈ Finset.univ.erase s := by simp [hts]
    let fp : G.strategy i → U := fun r => p.val r * v r
    let fq : G.strategy i → U := fun r => (redirectMixed i p s t).val r * v r
    have hp_s := Finset.sum_erase_add Finset.univ fp (Finset.mem_univ s)
    have hp_t := Finset.sum_erase_add (Finset.univ.erase s) fp ht
    have hq_s := Finset.sum_erase_add Finset.univ fq (Finset.mem_univ s)
    have hq_t := Finset.sum_erase_add (Finset.univ.erase s) fq ht
    have hrest :
        (∑ r ∈ (Finset.univ.erase s).erase t, fq r) =
          ∑ r ∈ (Finset.univ.erase s).erase t, fp r := by
      apply Finset.sum_congr rfl
      intro r hr
      have hrs : r ≠ s :=
        (Finset.mem_erase.mp (Finset.mem_of_mem_erase hr)).1
      have hrt : r ≠ t := (Finset.mem_erase.mp hr).1
      simp [fp, fq, redirectMixed, hst, hrs, hrt]
    change (∑ r, fp r) - ∑ r, fq r = p.val s * (v s - v t)
    rw [← hp_s, ← hp_t, ← hq_s, ← hq_t, hrest]
    simp [fp, fq, redirectMixed_apply_self, redirectMixed_apply_target, hst]
    ring

private theorem weightedSum_sub_eq_sum_pairwise
    (i : N) (p mu : MixedStrategy G i) (v : G.strategy i → U) :
    (∑ s : G.strategy i, p.val s * v s) -
        ∑ t : G.strategy i, mu.val t * v t =
      ∑ s : G.strategy i, ∑ t : G.strategy i,
        mu.val t * (p.val s * (v s - v t)) := by
  classical
  symm
  calc
    (∑ s : G.strategy i, ∑ t : G.strategy i,
        mu.val t * (p.val s * (v s - v t))) =
        ∑ s : G.strategy i,
          (p.val s * v s - p.val s * ∑ t : G.strategy i, mu.val t * v t) := by
      apply Finset.sum_congr rfl
      intro s _
      calc
        (∑ t : G.strategy i, mu.val t * (p.val s * (v s - v t))) =
            ∑ t : G.strategy i,
              (p.val s * v s * mu.val t - p.val s * (mu.val t * v t)) := by
          apply Finset.sum_congr rfl
          intro t _
          ring
        _ = p.val s * v s * (∑ t : G.strategy i, mu.val t) -
            p.val s * ∑ t : G.strategy i, mu.val t * v t := by
          rw [Finset.sum_sub_distrib]
          rw [← Finset.mul_sum, ← Finset.mul_sum]
        _ = p.val s * v s - p.val s * ∑ t : G.strategy i, mu.val t * v t := by
          rw [mu.property.2, mul_one]
    _ = (∑ s : G.strategy i, p.val s * v s) -
        (∑ s : G.strategy i, p.val s) *
          (∑ t : G.strategy i, mu.val t * v t) := by
      rw [Finset.sum_sub_distrib, Finset.sum_mul]
    _ = (∑ s : G.strategy i, p.val s * v s) -
        ∑ t : G.strategy i, mu.val t * v t := by
      rw [p.property.2, one_mul]

/-- Finite signalwise best-response condition described after MFoGT Definition
7.2.2. At every signal, the prescribed mixed action maximizes the unnormalized
conditional expected payoff against the opponents' conditional behavior. -/
def IsSignalwiseCorrelatedEquilibrium {Omega : Type uOmega} [Fintype Omega]
    (I : InformationStructure G Omega) (sigma : ExtendedProfile I) : Prop :=
  ∀ (i : N) (a : I.Signal i) (mu : MixedStrategy G i),
    signalExpectedPayoff I sigma i a mu ≤
      signalExpectedPayoff I sigma i a (sigma i a)

/-- Equivalent actionwise obedience form of the finite signalwise
best-response condition. -/
def IsSignalActionwiseObedient {Omega : Type uOmega} [Fintype Omega]
    (I : InformationStructure G Omega) (sigma : ExtendedProfile I) : Prop :=
  ∀ (i : N) (a : I.Signal i) (s t : G.strategy i),
    0 ≤ signalObedienceDifference I sigma i a s t

/-- Mixed best response after every signal is equivalent to all actionwise
obedience inequalities. -/
theorem isSignalwiseCorrelatedEquilibrium_iff_actionwise
    {Omega : Type uOmega} [Fintype Omega]
    (I : InformationStructure G Omega) (sigma : ExtendedProfile I) :
    IsSignalwiseCorrelatedEquilibrium I sigma ↔
      IsSignalActionwiseObedient I sigma := by
  classical
  constructor
  · intro h i a s t
    rw [signalObedienceDifference_eq_weighted_purePayoff]
    have hdev := h i a (redirectMixed i (sigma i a) s t)
    rw [signalExpectedPayoff_eq_sum_pure, signalExpectedPayoff_eq_sum_pure] at hdev
    have hdiff := weightedSum_sub_redirectMixed i (sigma i a)
      (signalPureActionPayoff I sigma i a) s t
    exact hdiff ▸ sub_nonneg.mpr hdev
  · intro h i a mu
    rw [signalExpectedPayoff_eq_sum_pure, signalExpectedPayoff_eq_sum_pure]
    apply sub_nonneg.mp
    rw [weightedSum_sub_eq_sum_pairwise i (sigma i a) mu
      (signalPureActionPayoff I sigma i a)]
    exact Finset.sum_nonneg fun s _ =>
      Finset.sum_nonneg fun t _ =>
        mul_nonneg (mu.property.1 t) <| by
          rw [← signalObedienceDifference_eq_weighted_purePayoff I sigma i a s t]
          exact h i a s t

private theorem extendedMixedProfile_deviate
    {Omega : Type uOmega} [Fintype Omega]
    (I : InformationStructure G Omega) (sigma : ExtendedProfile I)
    (i : N) (tau : ExtendedStrategy I i) (omega : Omega) :
    extendedMixedProfile I (deviate (G := extendBy G I) sigma i tau) omega =
      Function.update (extendedMixedProfile I sigma omega) i
        (tau (I.signal i omega)) := by
  classical
  funext j
  by_cases hji : j = i
  · subst j
    simp [extendedMixedProfile, deviate]
  · simp [extendedMixedProfile, deviate, hji]

/-- The extension payoff is the prior average of the base game's mixed payoff. -/
theorem extendBy_payoff_eq_sum_expectedPayoff
    {Omega : Type uOmega} [Fintype Omega]
    (I : InformationStructure G Omega) (sigma : ExtendedProfile I) (i : N) :
    (extendBy G I).payoff sigma i =
      ∑ omega : Omega,
        I.prior.val omega * expectedPayoff G (extendedMixedProfile I sigma omega) i := by
  rfl

/-- A unilateral extended-strategy deviation decomposes into the conditional
payoffs of its mixed action at each signal. -/
theorem extendBy_payoff_deviate_eq_sum_signalExpectedPayoff
    {Omega : Type uOmega} [Fintype Omega]
    (I : InformationStructure G Omega) (sigma : ExtendedProfile I)
    (i : N) (tau : ExtendedStrategy I i) :
    (extendBy G I).payoff (deviate (G := extendBy G I) sigma i tau) i =
      ∑ a : I.Signal i, signalExpectedPayoff I sigma i a (tau a) := by
  classical
  rw [extendBy_payoff_eq_sum_expectedPayoff]
  simp_rw [extendedMixedProfile_deviate]
  unfold signalExpectedPayoff
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro omega _
  simp

/-- The equilibrium payoff decomposes into its signal-event contributions. -/
theorem extendBy_payoff_eq_sum_signalExpectedPayoff
    {Omega : Type uOmega} [Fintype Omega]
    (I : InformationStructure G Omega) (sigma : ExtendedProfile I) (i : N) :
    (extendBy G I).payoff sigma i =
      ∑ a : I.Signal i, signalExpectedPayoff I sigma i a (sigma i a) := by
  have h := extendBy_payoff_deviate_eq_sum_signalExpectedPayoff
    I sigma i (sigma i)
  simpa using h

/-- Finite ex-ante/ex-post equivalence stated after MFoGT Definition 7.2.2:
Nash equilibrium of the behavioral extension is equivalent to mixed best
response after every signal. -/
theorem isExtendedNashEquilibrium_iff_signalwise
    {Omega : Type uOmega} [Fintype Omega]
    (I : InformationStructure G Omega) (sigma : ExtendedProfile I) :
    IsExtendedNashEquilibrium I sigma ↔
      IsSignalwiseCorrelatedEquilibrium I sigma := by
  classical
  constructor
  · intro h i a mu
    have hlocal := h i (Function.update (sigma i) a mu)
    rw [extendBy_payoff_deviate_eq_sum_signalExpectedPayoff] at hlocal
    rw [extendBy_payoff_eq_sum_signalExpectedPayoff] at hlocal
    let f : I.Signal i → U :=
      fun b => signalExpectedPayoff I sigma i b (sigma i b)
    let g : I.Signal i → U :=
      fun b => signalExpectedPayoff I sigma i b
        (Function.update (sigma i) a mu b)
    have hrest :
        (∑ b ∈ Finset.univ.erase a, g b) =
          ∑ b ∈ Finset.univ.erase a, f b := by
      apply Finset.sum_congr rfl
      intro b hb
      have hba : b ≠ a := (Finset.mem_erase.mp hb).1
      simp [f, g, Function.update_of_ne hba]
    have hg := Finset.sum_erase_add Finset.univ g (Finset.mem_univ a)
    have hf := Finset.sum_erase_add Finset.univ f (Finset.mem_univ a)
    change (∑ b, g b) ≤ ∑ b, f b at hlocal
    rw [← hg, ← hf, hrest] at hlocal
    have hga : g a = signalExpectedPayoff I sigma i a mu := by
      simp [g]
    have hfa : f a = signalExpectedPayoff I sigma i a (sigma i a) := by
      rfl
    rw [hga, hfa] at hlocal
    linarith
  · intro h i tau
    rw [extendBy_payoff_deviate_eq_sum_signalExpectedPayoff]
    rw [extendBy_payoff_eq_sum_signalExpectedPayoff]
    exact Finset.sum_le_sum fun a _ => h i a (tau a)

/-- The same ex-ante/ex-post equivalence for `IsCorrelatedEquilibrium`. -/
theorem isCorrelatedEquilibrium_iff_signalwise
    {Omega : Type uOmega} [Fintype Omega]
    (I : InformationStructure G Omega) (sigma : ExtendedProfile I) :
    IsCorrelatedEquilibrium I sigma ↔
    IsSignalwiseCorrelatedEquilibrium I sigma :=
  isExtendedNashEquilibrium_iff_signalwise I sigma

/-! #### Trivial information and ordinary mixed Nash equilibrium -/

/-- The one-event, one-signal information structure. -/
def trivialInformationStructure
    (G : StrategicGame.{u_N, u_U, u_S} N U)
    [∀ i : N, Fintype (G.strategy i)] :
    InformationStructure G PUnit where
  Signal _ := PUnit
  prior := stdSimplex.vertex PUnit.unit
  signal _ _ := PUnit.unit

/-- A mixed profile regarded as a constant behavioral profile on the trivial
information structure. -/
def trivialExtendedProfile
    (G : StrategicGame.{u_N, u_U, u_S} N U)
    [∀ i : N, Fintype (G.strategy i)]
    (p : MixedProfile G) : ExtendedProfile (trivialInformationStructure G) :=
  fun i _ => p i

private theorem extendedMixedProfile_trivial
    (G : StrategicGame.{u_N, u_U, u_S} N U)
    [∀ i : N, Fintype (G.strategy i)]
    (p : MixedProfile G) (omega : PUnit) :
    extendedMixedProfile (trivialInformationStructure G)
        (trivialExtendedProfile G p) omega = p := by
  funext i
  rfl

private theorem signalExpectedPayoff_trivial
    (G : StrategicGame.{u_N, u_U, u_S} N U)
    [∀ i : N, Fintype (G.strategy i)]
    [∀ i : N, DecidableEq (G.strategy i)]
    (p : MixedProfile G) (i : N) (a : PUnit) (mu : MixedStrategy G i) :
    signalExpectedPayoff (trivialInformationStructure G)
        (trivialExtendedProfile G p) i a mu =
      expectedPayoff G (Function.update p i mu) i := by
  classical
  cases a
  unfold signalExpectedPayoff
  rw [Fintype.sum_unique]
  rw [extendedMixedProfile_trivial]
  simp [trivialInformationStructure, Pi.single]

/-- With trivial information, Nash equilibrium of the extension is exactly
ordinary mixed Nash equilibrium of the base game, formalizing the observation
after MFoGT Definition 7.2.3. -/
theorem isExtendedNashEquilibrium_trivial_iff_isMixedNashEq
    (G : StrategicGame.{u_N, u_U, u_S} N U)
    [∀ i : N, Fintype (G.strategy i)]
    [∀ i : N, DecidableEq (G.strategy i)]
    (p : MixedProfile G) :
    IsExtendedNashEquilibrium (trivialInformationStructure G)
        (trivialExtendedProfile G p) ↔ IsMixedNashEq G p := by
  classical
  rw [isExtendedNashEquilibrium_iff_signalwise]
  constructor
  · intro h i s
    have hpure := h i PUnit.unit (pureToMixed s)
    change signalExpectedPayoff (trivialInformationStructure G)
        (trivialExtendedProfile G p) i PUnit.unit (pureToMixed s) ≤
      signalExpectedPayoff (trivialInformationStructure G)
        (trivialExtendedProfile G p) i PUnit.unit (p i) at hpure
    rw [signalExpectedPayoff_trivial, signalExpectedPayoff_trivial] at hpure
    simpa [deviateMixed] using hpure
  · intro h i a mu
    cases a
    change signalExpectedPayoff (trivialInformationStructure G)
        (trivialExtendedProfile G p) i PUnit.unit mu ≤
      signalExpectedPayoff (trivialInformationStructure G)
        (trivialExtendedProfile G p) i PUnit.unit (p i)
    rw [signalExpectedPayoff_trivial, signalExpectedPayoff_trivial]
    simp only [Function.update_eq_self]
    calc
      expectedPayoff G (Function.update p i mu) i =
          ∑ s : G.strategy i,
            mu.val s * pureActionPayoffAgainst p i s :=
        expectedPayoff_update_eq_sum_pureActionPayoff p i mu
      _ = ∑ s : G.strategy i,
          mu.val s * expectedPayoff G
            (Function.update p i (pureToMixed s)) i := by
        apply Finset.sum_congr rfl
        intro s _
        rw [expectedPayoff_update_pure]
      _ ≤ ∑ s : G.strategy i, mu.val s * expectedPayoff G p i := by
        apply Finset.sum_le_sum
        intro s _
        exact mul_le_mul_of_nonneg_left (by simpa [deviateMixed] using h i s)
          (mu.property.1 s)
      _ = expectedPayoff G p i := by
        rw [← Finset.sum_mul, mu.property.2, one_mul]

/-! ### MFoGT 7.2.3: induced correlated distributions -/

/-- A probability distribution over pure action profiles. -/
abbrev CorrelatedStrategy (G : StrategicGame.{u_N, u_U, u_S} N U)
    [∀ i : N, Fintype (G.strategy i)] :=
  stdSimplex U G.Profile

/-- User-facing synonym for a distribution over pure action profiles. -/
abbrev CorrelatedDistribution (G : StrategicGame.{u_N, u_U, u_S} N U)
    [∀ i : N, Fintype (G.strategy i)] :=
  CorrelatedStrategy G

/-- The correlated distribution `Q(sigma)` induced by a behavioral extended
profile, exactly as in the finite formula following MFoGT Definition 7.2.3:

`Q(s) = sum_omega P(omega) * product_i sigma_i(theta_i(omega))(s_i)`. -/
noncomputable def inducedDistribution {Omega : Type uOmega} [Fintype Omega]
    (I : InformationStructure G Omega) (sigma : ExtendedProfile I) :
    CorrelatedStrategy G := by
  classical
  refine
    { val := fun s =>
        ∑ omega : Omega,
          I.prior.val omega * extendedActionProbability I sigma omega s
      property := ?_ }
  constructor
  · intro s
    exact Finset.sum_nonneg fun omega _ =>
      mul_nonneg (I.prior.property.1 omega) <|
        Finset.prod_nonneg fun i _ => (sigma i (I.signal i omega)).property.1 (s i)
  · calc
      (∑ s : G.Profile,
          ∑ omega : Omega,
            I.prior.val omega * extendedActionProbability I sigma omega s)
          = ∑ omega : Omega,
              ∑ s : G.Profile,
                I.prior.val omega * extendedActionProbability I sigma omega s := by
              rw [Finset.sum_comm]
      _ = ∑ omega : Omega, I.prior.val omega := by
            apply Finset.sum_congr rfl
            intro omega _
            rw [← Finset.mul_sum]
            have hprob :
                (∑ s : G.Profile, extendedActionProbability I sigma omega s) = 1 := by
              unfold extendedActionProbability extendedMixedProfile
              rw [← Fintype.prod_sum]
              exact Finset.prod_eq_one fun i _ =>
                (sigma i (I.signal i omega)).property.2
            rw [hprob, mul_one]
      _ = 1 := I.prior.property.2

/-- Evaluation of the induced distribution at a pure profile. -/
theorem inducedDistribution_val {Omega : Type uOmega} [Fintype Omega]
    (I : InformationStructure G Omega) (sigma : ExtendedProfile I) (s : G.Profile) :
    (inducedDistribution I sigma).val s =
      ∑ omega : Omega,
        I.prior.val omega * extendedActionProbability I sigma omega s :=
  rfl

/-- Under trivial information, the distribution induced by a mixed profile is
its independent product distribution. This is Equation (8.10) in [MSZ,
Section 8.2]. -/
theorem inducedDistribution_trivial_eq_piProduct (p : MixedProfile G) :
    inducedDistribution
        (trivialInformationStructure.{u_N, u_U, u_S, 0, 0} G)
        (trivialExtendedProfile.{u_N, u_U, u_S, 0, 0} G p) =
      stdSimplex.piProduct p := by
  classical
  apply Subtype.ext
  funext s
  rw [inducedDistribution_val, stdSimplex.piProduct_apply]
  simp [trivialInformationStructure, trivialExtendedProfile,
    extendedActionProbability, extendedMixedProfile]

/-- The action probability generated at an event by mixed complete plans is the
fiber sum over all plan profiles realizing that action profile. -/
theorem extendedActionProbability_mixedContingentPlan_eq_fiberSum
    {Omega : Type uOmega} [Fintype Omega]
    (I : InformationStructure G Omega) (mu : MixedContingentPlanProfile I)
    (omega : Omega) (s : G.Profile) :
    extendedActionProbability I
        (mixedContingentPlanProfileToBehavior I mu) omega s =
      ∑ plan : PureContingentPlanProfile I,
        if realizedContingentPlanProfile I plan omega = s then
          ∏ i : N, (mu i).val (plan i)
        else 0 := by
  have h := congrArg (fun q : CorrelatedStrategy G => q.val s)
    (map_piProduct_mixedContingentPlanProfile I mu omega)
  change (stdSimplex.map
      (fun plan => realizedContingentPlanProfile I plan omega)
      (stdSimplex.piProduct mu)).val s =
    (stdSimplex.piProduct
      (extendedMixedProfile I
        (mixedContingentPlanProfileToBehavior I mu) omega)).val s at h
  rw [stdSimplex.map_apply_eq_sum_ite] at h
  simpa [extendedActionProbability, stdSimplex.piProduct_apply] using h.symm

/-- Distribution induced by a mixed profile over the source's complete
contingent plans. Its direct fiber-sum formula is proved below. -/
noncomputable def inducedMixedContingentPlanDistribution
    {Omega : Type uOmega} [Fintype Omega]
    (I : InformationStructure G Omega) (mu : MixedContingentPlanProfile I) :
    CorrelatedStrategy G :=
  inducedDistribution I (mixedContingentPlanProfileToBehavior I mu)

/-- Direct MFoGT formula for the distribution induced by independently mixed
complete contingent plans. -/
theorem inducedMixedContingentPlanDistribution_val
    {Omega : Type uOmega} [Fintype Omega]
    (I : InformationStructure G Omega) (mu : MixedContingentPlanProfile I)
    (s : G.Profile) :
    (inducedMixedContingentPlanDistribution I mu).val s =
      ∑ omega : Omega, I.prior.val omega *
        ∑ plan : PureContingentPlanProfile I,
          if realizedContingentPlanProfile I plan omega = s then
            ∏ i : N, (mu i).val (plan i)
          else 0 := by
  rw [inducedMixedContingentPlanDistribution, inducedDistribution_val]
  apply Finset.sum_congr rfl
  intro omega _
  rw [extendedActionProbability_mixedContingentPlan_eq_fiberSum]

/-- A distribution is induced by a correlated-equilibrium profile of the fixed
information extension `[G, I]`. -/
def IsInducedSignalwiseCorrelatedEquilibriumDistribution
    {Omega : Type uOmega} [Fintype Omega]
    (I : InformationStructure G Omega) (q : CorrelatedStrategy G) : Prop :=
  ∃ sigma : ExtendedProfile I,
    IsSignalwiseCorrelatedEquilibrium I sigma ∧ inducedDistribution I sigma = q

/-- A distribution induced by a Nash equilibrium of the behavioral extension
`[G, I]`. -/
def IsInducedExtendedNashDistribution
    {Omega : Type uOmega} [Fintype Omega]
    (I : InformationStructure G Omega) (q : CorrelatedStrategy G) : Prop :=
  ∃ sigma : ExtendedProfile I,
    IsExtendedNashEquilibrium I sigma ∧ inducedDistribution I sigma = q

/-- A distribution induced by a mixed Nash equilibrium of the source's
complete-contingent-plan extension. -/
def IsInducedMixedContingentPlanNashDistribution
    {Omega : Type uOmega} [Fintype Omega]
    (I : InformationStructure G Omega) (q : CorrelatedStrategy G) : Prop :=
  ∃ mu : MixedContingentPlanProfile I,
    IsMixedContingentPlanNashEquilibrium I mu ∧
      inducedMixedContingentPlanDistribution I mu = q

/-- For every fixed finite information structure, the source's mixed-plan
model and the behavioral model induce exactly the same equilibrium
distributions. -/
theorem isInducedMixedContingentPlanNashDistribution_iff_behavioral
    {Omega : Type uOmega} [Fintype Omega]
    (I : InformationStructure G Omega) (q : CorrelatedStrategy G) :
    IsInducedMixedContingentPlanNashDistribution I q ↔
      IsInducedExtendedNashDistribution I q := by
  constructor
  · rintro ⟨mu, hmu, rfl⟩
    exact ⟨mixedContingentPlanProfileToBehavior I mu,
      (isMixedContingentPlanNashEquilibrium_iff_behavioral I mu).mp hmu, rfl⟩
  · rintro ⟨sigma, hsigma, rfl⟩
    refine ⟨behaviorProfileToMixedContingentPlan I sigma,
      (isMixedContingentPlanNashEquilibrium_behaviorProfile_iff I sigma).mpr hsigma, ?_⟩
    unfold inducedMixedContingentPlanDistribution
    rw [mixedContingentPlanProfileToBehavior_behaviorProfileToMixedContingentPlan]

/-- A fixed finite extension induces the same distributions whether equilibrium
is stated ex ante as Nash equilibrium or ex post as signalwise best response. -/
theorem isInducedExtendedNashDistribution_iff_signalwise
    {Omega : Type uOmega} [Fintype Omega]
    (I : InformationStructure G Omega) (q : CorrelatedStrategy G) :
    IsInducedExtendedNashDistribution I q ↔
      IsInducedSignalwiseCorrelatedEquilibriumDistribution I q := by
  constructor
  · rintro ⟨sigma, hsigma, rfl⟩
    exact ⟨sigma, (isExtendedNashEquilibrium_iff_signalwise I sigma).mp hsigma, rfl⟩
  · rintro ⟨sigma, hsigma, rfl⟩
    exact ⟨sigma, (isExtendedNashEquilibrium_iff_signalwise I sigma).mpr hsigma, rfl⟩

/-- A distribution induced by a correlated equilibrium in the finite
behavioral formulation of MFoGT Definition 7.2.3. -/
abbrev IsInducedCorrelatedEquilibriumDistribution
    {Omega : Type uOmega} [Fintype Omega]
    (I : InformationStructure G Omega) (q : CorrelatedStrategy G) : Prop :=
  IsInducedExtendedNashDistribution I q

/-- The behavioral-extension union of equilibrium distributions. The theorem
below proves that it is exactly the source's mixed-contingent-plan union
`CED(G)` from MFoGT Definition 7.2.4. -/
def CorrelatedEquilibriumDistributions
    (G : StrategicGame.{u_N, u_U, u_S} N U)
    [∀ i : N, Fintype (G.strategy i)]
    [∀ i : N, DecidableEq (G.strategy i)] :
    Set (CorrelatedStrategy G) :=
  {q | ∃ (Omega : Type (max u_N u_S)) (hOmega : Fintype Omega),
      letI := hOmega
      ∃ I : InformationStructure.{max u_N u_S, u_S, u_N, u_U, u_S} G Omega,
        IsInducedExtendedNashDistribution I q}

/-- The source-faithful union `CED(G)` from MFoGT Definition 7.2.4, formed from
mixed Nash equilibria over complete contingent plans. -/
def MixedContingentPlanCorrelatedEquilibriumDistributions
    (G : StrategicGame.{u_N, u_U, u_S} N U)
    [∀ i : N, Fintype (G.strategy i)]
    [∀ i : N, DecidableEq (G.strategy i)] :
    Set (CorrelatedStrategy G) :=
  {q | ∃ (Omega : Type (max u_N u_S)) (hOmega : Fintype Omega),
      letI := hOmega
      ∃ I : InformationStructure.{max u_N u_S, u_S, u_N, u_U, u_S} G Omega,
        IsInducedMixedContingentPlanNashDistribution I q}

/-- **MFoGT Definitions 7.2.2--7.2.4, finite realization theorem.** The
source's mixed complete-contingent-plan definition and the signalwise
behavioral definition generate the same set of correlated-equilibrium
distributions. -/
theorem mixedContingentPlanCorrelatedEquilibriumDistributions_eq_behavioral
    (G : StrategicGame.{u_N, u_U, u_S} N U)
    [∀ i : N, Fintype (G.strategy i)]
    [∀ i : N, DecidableEq (G.strategy i)] :
    MixedContingentPlanCorrelatedEquilibriumDistributions G =
      CorrelatedEquilibriumDistributions G := by
  ext q
  constructor
  · rintro ⟨Omega, hOmega, I, hq⟩
    letI := hOmega
    exact ⟨Omega, hOmega, I,
      (isInducedMixedContingentPlanNashDistribution_iff_behavioral I q).mp hq⟩
  · rintro ⟨Omega, hOmega, I, hq⟩
    letI := hOmega
    exact ⟨Omega, hOmega, I,
      (isInducedMixedContingentPlanNashDistribution_iff_behavioral I q).mpr hq⟩

/-- Explicit synonym emphasizing the behavioral Nash presentation of
`CorrelatedEquilibriumDistributions`, rather than the signalwise set below. The
mixed-plan source presentation is proved equal above. -/
abbrev NashCorrelatedEquilibriumDistributions
    (G : StrategicGame.{u_N, u_U, u_S} N U)
    [∀ i : N, Fintype (G.strategy i)]
    [∀ i : N, DecidableEq (G.strategy i)] :
    Set (CorrelatedStrategy G) :=
  CorrelatedEquilibriumDistributions G

/-- Ex-post presentation of the finite outcome set in MFoGT Definition 7.2.4.

The existential universe contains the canonical finite model used below. The
following theorem identifies this set with
`CorrelatedEquilibriumDistributions`. -/
def SignalwiseCorrelatedEquilibriumDistributions
    (G : StrategicGame.{u_N, u_U, u_S} N U)
    [∀ i : N, Fintype (G.strategy i)]
    [∀ i : N, DecidableEq (G.strategy i)] :
    Set (CorrelatedStrategy G) :=
  {q | ∃ (Omega : Type (max u_N u_S)) (hOmega : Fintype Omega),
      letI := hOmega
      ∃ I : InformationStructure.{max u_N u_S, u_S, u_N, u_U, u_S} G Omega,
        IsInducedSignalwiseCorrelatedEquilibriumDistribution I q}

/-- Distribution-level ex-ante/ex-post equivalence for MFoGT Definition 7.2.4. -/
theorem correlatedEquilibriumDistributions_eq_signalwise
    (G : StrategicGame.{u_N, u_U, u_S} N U)
    [∀ i : N, Fintype (G.strategy i)]
    [∀ i : N, DecidableEq (G.strategy i)] :
    CorrelatedEquilibriumDistributions G =
      SignalwiseCorrelatedEquilibriumDistributions G := by
  ext q
  constructor
  · rintro ⟨Omega, hOmega, I, hq⟩
    letI := hOmega
    exact ⟨Omega, hOmega, I,
      (isInducedExtendedNashDistribution_iff_signalwise I q).mp hq⟩
  · rintro ⟨Omega, hOmega, I, hq⟩
    letI := hOmega
    exact ⟨Omega, hOmega, I,
      (isInducedExtendedNashDistribution_iff_signalwise I q).mpr hq⟩

/-! ### MFoGT 7.2.4: canonical correlation -/

/-- Canonical information structure associated with `q`: the state is a pure
action profile and player `i` observes its own component. -/
def canonicalInformationStructure
    (G : StrategicGame.{u_N, u_U, u_S} N U)
    [∀ i : N, Fintype (G.strategy i)]
    [∀ i : N, DecidableEq (G.strategy i)]
    (q : CorrelatedStrategy G) : InformationStructure G G.Profile where
  Signal i := G.strategy i
  prior := q
  signal i rho := rho i

/-- Truthful behavior in the canonical extension: play the recommended action
with probability one. -/
noncomputable def truthfulCanonicalStrategy
    (G : StrategicGame.{u_N, u_U, u_S} N U)
    [∀ i : N, Fintype (G.strategy i)]
    [∀ i : N, DecidableEq (G.strategy i)]
    (q : CorrelatedStrategy G) : ExtendedProfile (canonicalInformationStructure G q) :=
  fun _ s => pureToMixed s

/-- The source-literal truthful pure contingent-plan profile in the canonical
extension: every player plays the action that they are recommended. -/
def truthfulCanonicalContingentPlanProfile
    (G : StrategicGame.{u_N, u_U, u_S} N U)
    [∀ i : N, Fintype (G.strategy i)]
    [∀ i : N, DecidableEq (G.strategy i)]
    (q : CorrelatedStrategy G) :
    PureContingentPlanProfile (canonicalInformationStructure G q) :=
  fun _ s => s

/-- The point-mass mixed profile on the canonical identity contingent-plan
profile. This is the mixed-strategy encoding of the source's truthful pure
plan. -/
noncomputable def truthfulCanonicalMixedContingentPlanProfile
    (G : StrategicGame.{u_N, u_U, u_S} N U)
    [∀ i : N, Fintype (G.strategy i)]
    [∀ i : N, DecidableEq (G.strategy i)]
    (q : CorrelatedStrategy G) :
    MixedContingentPlanProfile (canonicalInformationStructure G q) :=
  pureProfileToMixed (truthfulCanonicalContingentPlanProfile G q)

/-- The canonical product coupling of truthful signalwise point masses is
exactly the point mass on the identity contingent-plan profile. This closes
the object-level bridge between the behavioral and source-literal versions of
MFoGT Definition 7.2.5. -/
theorem behaviorProfileToMixedContingentPlan_canonical_truthful
    (q : CorrelatedStrategy G) :
    behaviorProfileToMixedContingentPlan (canonicalInformationStructure G q)
        (truthfulCanonicalStrategy G q) =
      truthfulCanonicalMixedContingentPlanProfile G q := by
  classical
  funext i
  apply stdSimplex.ext
  funext plan
  change (∏ s : G.strategy i, if plan s = s then 1 else 0) =
    if plan = (fun s => s) then 1 else 0
  by_cases hplan : plan = fun s => s
  · subst plan
    simp
  · have hsignal : ∃ s : G.strategy i, plan s ≠ s := by
      by_contra h
      push Not at h
      exact hplan (funext h)
    obtain ⟨s, hs⟩ := hsignal
    rw [if_neg hplan]
    exact Finset.prod_eq_zero (Finset.mem_univ s) (by simp [hs])

/-- Conditional action probability under canonical truthful behavior is the
point mass at the state profile. -/
theorem extendedActionProbability_canonical_truthful
    (q : CorrelatedStrategy G) (omega rho : G.Profile) :
    extendedActionProbability (canonicalInformationStructure G q)
        (truthfulCanonicalStrategy G q) omega rho =
      if rho = omega then 1 else 0 := by
  classical
  by_cases h : rho = omega
  · subst rho
    simp [extendedActionProbability, extendedMixedProfile,
      truthfulCanonicalStrategy, canonicalInformationStructure, pureToMixed]
  · have hcoord : ∃ i : N, rho i ≠ omega i := by
      by_contra hall
      apply h
      funext i
      by_contra hi
      exact hall ⟨i, hi⟩
    obtain ⟨i, hi⟩ := hcoord
    rw [if_neg h]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    change (if rho i = omega i then 1 else 0) = 0
    simp [hi]

/-- Canonical truthful behavior induces exactly the canonical prior. -/
theorem inducedDistribution_canonical_truthful (q : CorrelatedStrategy G) :
    inducedDistribution (canonicalInformationStructure G q)
        (truthfulCanonicalStrategy G q) = q := by
  classical
  apply Subtype.ext
  funext rho
  rw [inducedDistribution_val]
  simp_rw [extendedActionProbability_canonical_truthful]
  rw [Finset.sum_eq_single_of_mem rho (Finset.mem_univ rho)]
  · simp [canonicalInformationStructure]
  · intro omega _ hne
    simp [Ne.symm hne]

/-- The source-literal point mass on the canonical identity contingent plan
also induces exactly the canonical prior. -/
theorem inducedMixedContingentPlanDistribution_canonical_truthful
    (q : CorrelatedStrategy G) :
    inducedMixedContingentPlanDistribution (canonicalInformationStructure G q)
        (truthfulCanonicalMixedContingentPlanProfile G q) = q := by
  rw [← behaviorProfileToMixedContingentPlan_canonical_truthful]
  unfold inducedMixedContingentPlanDistribution
  rw [mixedContingentPlanProfileToBehavior_behaviorProfileToMixedContingentPlan]
  exact inducedDistribution_canonical_truthful q

/-- Canonical correlated-equilibrium predicate from MFoGT Definition 7.2.5:
truthful play is a Nash equilibrium of the canonical behavioral extension. -/
def IsCanonicalCorrelatedEquilibriumDistribution
    (G : StrategicGame.{u_N, u_U, u_S} N U)
    [∀ i : N, Fintype (G.strategy i)]
    [∀ i : N, DecidableEq (G.strategy i)]
    (q : CorrelatedStrategy G) : Prop :=
  IsExtendedNashEquilibrium (canonicalInformationStructure G q)
    (truthfulCanonicalStrategy G q)

/-- `CCED(G)`, the Nash-based canonical set from MFoGT Definition 7.2.5. -/
def CanonicalCorrelatedEquilibriumDistributions
    (G : StrategicGame.{u_N, u_U, u_S} N U)
    [∀ i : N, Fintype (G.strategy i)]
    [∀ i : N, DecidableEq (G.strategy i)] :
    Set (CorrelatedStrategy G) :=
  {q | IsCanonicalCorrelatedEquilibriumDistribution G q}

/-- Source-literal canonical correlated-equilibrium predicate: the point mass
on the identity contingent-plan profile is a mixed Nash equilibrium of the
canonical contingent-plan extension. -/
def IsMixedPlanCanonicalCorrelatedEquilibriumDistribution
    (G : StrategicGame.{u_N, u_U, u_S} N U)
    [∀ i : N, Fintype (G.strategy i)]
    [∀ i : N, DecidableEq (G.strategy i)]
    (q : CorrelatedStrategy G) : Prop :=
  IsMixedContingentPlanNashEquilibrium (canonicalInformationStructure G q)
    (truthfulCanonicalMixedContingentPlanProfile G q)

/-- The source-literal mixed-plan version of `CCED(G)` from MFoGT Definition
7.2.5. -/
def MixedPlanCanonicalCorrelatedEquilibriumDistributions
    (G : StrategicGame.{u_N, u_U, u_S} N U)
    [∀ i : N, Fintype (G.strategy i)]
    [∀ i : N, DecidableEq (G.strategy i)] :
    Set (CorrelatedStrategy G) :=
  {q | IsMixedPlanCanonicalCorrelatedEquilibriumDistribution G q}

/-- The source-literal identity-plan canonical predicate is equivalent to the
behavioral truthful predicate. -/
theorem isMixedPlanCanonicalCorrelatedEquilibriumDistribution_iff_behavioral
    (G : StrategicGame.{u_N, u_U, u_S} N U)
    [∀ i : N, Fintype (G.strategy i)]
    [∀ i : N, DecidableEq (G.strategy i)]
    (q : CorrelatedStrategy G) :
    IsMixedPlanCanonicalCorrelatedEquilibriumDistribution G q ↔
      IsCanonicalCorrelatedEquilibriumDistribution G q := by
  rw [IsMixedPlanCanonicalCorrelatedEquilibriumDistribution,
    IsCanonicalCorrelatedEquilibriumDistribution,
    ← behaviorProfileToMixedContingentPlan_canonical_truthful]
  exact isMixedContingentPlanNashEquilibrium_behaviorProfile_iff
    (canonicalInformationStructure G q) (truthfulCanonicalStrategy G q)

/-- The source-literal mixed-plan and behavioral presentations of `CCED(G)`
are extensionally equal. -/
theorem mixedPlanCanonicalCorrelatedEquilibriumDistributions_eq_behavioral
    (G : StrategicGame.{u_N, u_U, u_S} N U)
    [∀ i : N, Fintype (G.strategy i)]
    [∀ i : N, DecidableEq (G.strategy i)] :
    MixedPlanCanonicalCorrelatedEquilibriumDistributions G =
      CanonicalCorrelatedEquilibriumDistributions G := by
  ext q
  exact isMixedPlanCanonicalCorrelatedEquilibriumDistribution_iff_behavioral G q

/-- Signalwise analogue of the canonical correlated-equilibrium predicate:
truthful point-mass behavior satisfies all signalwise obedience inequalities. -/
def IsSignalwiseCanonicalCorrelatedEquilibriumDistribution
    (G : StrategicGame.{u_N, u_U, u_S} N U)
    [∀ i : N, Fintype (G.strategy i)]
    [∀ i : N, DecidableEq (G.strategy i)]
    (q : CorrelatedStrategy G) : Prop :=
  IsSignalwiseCorrelatedEquilibrium (canonicalInformationStructure G q)
    (truthfulCanonicalStrategy G q)

/-- Canonical truthful play is Nash exactly when it is a best response after
every recommendation. -/
theorem isCanonicalCorrelatedEquilibriumDistribution_iff_signalwise
    (G : StrategicGame.{u_N, u_U, u_S} N U)
    [∀ i : N, Fintype (G.strategy i)]
    [∀ i : N, DecidableEq (G.strategy i)]
    (q : CorrelatedStrategy G) :
    IsCanonicalCorrelatedEquilibriumDistribution G q ↔
      IsSignalwiseCanonicalCorrelatedEquilibriumDistribution G q :=
  isExtendedNashEquilibrium_iff_signalwise
    (canonicalInformationStructure G q) (truthfulCanonicalStrategy G q)

/-- Ex-post presentation of the canonical correlated-equilibrium set. -/
def SignalwiseCanonicalCorrelatedEquilibriumDistributions
    (G : StrategicGame.{u_N, u_U, u_S} N U)
    [∀ i : N, Fintype (G.strategy i)]
    [∀ i : N, DecidableEq (G.strategy i)] :
    Set (CorrelatedStrategy G) :=
  {q | IsSignalwiseCanonicalCorrelatedEquilibriumDistribution G q}

/-- The Nash-based and ex-post presentations of `CCED(G)` agree. -/
theorem canonicalCorrelatedEquilibriumDistributions_eq_signalwise
    (G : StrategicGame.{u_N, u_U, u_S} N U)
    [∀ i : N, Fintype (G.strategy i)]
    [∀ i : N, DecidableEq (G.strategy i)] :
    CanonicalCorrelatedEquilibriumDistributions G =
      SignalwiseCanonicalCorrelatedEquilibriumDistributions G := by
  ext q
  exact isCanonicalCorrelatedEquilibriumDistribution_iff_signalwise G q

/-! ### MFoGT 7.2.5: finite obedience characterization -/

/-- The expected payoff loss from replacing recommendation `s` by `t` in a
correlated distribution. -/
noncomputable def obedienceDifference
    (q : CorrelatedStrategy G) (i : N) (s t : G.strategy i) : U :=
  ∑ rho : G.Profile,
    if rho i = s then
      q.val rho * (G.payoff rho i - G.payoff (deviate rho i t) i)
    else 0

/-- A single finite obedience inequality. -/
def ObedienceInequality
    (q : CorrelatedStrategy G) (i : N) (s t : G.strategy i) : Prop :=
  0 <= obedienceDifference q i s t

/-- The finite global obedience predicate from MFoGT Theorem 7.2.7. -/
def IsCorrelatedEq
    (G : StrategicGame.{u_N, u_U, u_S} N U)
    [∀ i : N, Fintype (G.strategy i)]
    [∀ i : N, DecidableEq (G.strategy i)]
    (q : CorrelatedStrategy G) : Prop :=
  ∀ (i : N) (s t : G.strategy i), ObedienceInequality q i s t

/-- Global obedience of an induced distribution is the sum of its
signal-specific obedience contributions. -/
theorem obedienceDifference_induced_eq_sum_signal
    {Omega : Type uOmega} [Fintype Omega]
    (I : InformationStructure G Omega) (sigma : ExtendedProfile I)
    (i : N) (s t : G.strategy i) :
    obedienceDifference (inducedDistribution I sigma) i s t =
      ∑ a : I.Signal i, signalObedienceDifference I sigma i a s t := by
  classical
  unfold obedienceDifference signalObedienceDifference
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro rho _
  by_cases hrho : rho i = s
  · simp only [hrho, if_true, inducedDistribution_val, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro omega _
    simp
  · simp [hrho]

/-- Every signalwise correlated-equilibrium profile induces a distribution
satisfying all global obedience inequalities. -/
theorem obedienceDifference_of_isSignalwiseCorrelatedEquilibrium
    {Omega : Type uOmega} [Fintype Omega]
    (I : InformationStructure G Omega) (sigma : ExtendedProfile I)
    (hsigma : IsSignalwiseCorrelatedEquilibrium I sigma)
    (i : N) (s t : G.strategy i) :
    0 <= obedienceDifference (inducedDistribution I sigma) i s t := by
  rw [obedienceDifference_induced_eq_sum_signal]
  have hactionwise :=
    (isSignalwiseCorrelatedEquilibrium_iff_actionwise I sigma).mp hsigma
  exact Finset.sum_nonneg fun a _ => hactionwise i a s t

/-- Every behavioral-extension Nash equilibrium induces a distribution
satisfying all global obedience inequalities. -/
theorem obedienceDifference_of_isCorrelatedEquilibrium
    {Omega : Type uOmega} [Fintype Omega]
    (I : InformationStructure G Omega) (sigma : ExtendedProfile I)
    (hsigma : IsCorrelatedEquilibrium I sigma)
    (i : N) (s t : G.strategy i) :
    0 <= obedienceDifference (inducedDistribution I sigma) i s t :=
  obedienceDifference_of_isSignalwiseCorrelatedEquilibrium I sigma
    ((isCorrelatedEquilibrium_iff_signalwise I sigma).mp hsigma) i s t

/-- For canonical truthful behavior, a signal different from the candidate own
action contributes zero to that action's obedience inequality. -/
theorem signalObedienceDifference_canonical_truthful_of_ne
    (q : CorrelatedStrategy G) (i : N) (a s t : G.strategy i) (has : a ≠ s) :
    signalObedienceDifference (canonicalInformationStructure G q)
        (truthfulCanonicalStrategy G q) i a s t = 0 := by
  classical
  unfold signalObedienceDifference
  apply Finset.sum_eq_zero
  intro rho _
  by_cases hrho : rho i = s
  · rw [if_pos hrho]
    apply Finset.sum_eq_zero
    intro omega _
    by_cases homega : omega i = a
    · change (if omega i = a then _ else _) = 0
      rw [if_pos homega, extendedActionProbability_canonical_truthful]
      have hne : rho ≠ omega := by
        intro h
        subst omega
        exact has (homega.symm.trans hrho)
      simp [hne]
    · change (if omega i = a then _ else _) = 0
      rw [if_neg homega]
  · simp [hrho]

/-- The only nonzero signal contribution for canonical truthful behavior is the
one whose signal equals the candidate own action. -/
theorem signalObedienceDifference_canonical_truthful_self
    (q : CorrelatedStrategy G) (i : N) (s t : G.strategy i) :
    signalObedienceDifference (canonicalInformationStructure G q)
        (truthfulCanonicalStrategy G q) i s s t =
      obedienceDifference q i s t := by
  classical
  have hsum := obedienceDifference_induced_eq_sum_signal
    (canonicalInformationStructure G q) (truthfulCanonicalStrategy G q) i s t
  rw [inducedDistribution_canonical_truthful] at hsum
  rw [hsum]
  symm
  apply Finset.sum_eq_single s
  · intro a _ has
    exact signalObedienceDifference_canonical_truthful_of_ne q i a s t has
  · intro hs
    exact (hs (Finset.mem_univ s)).elim

/-- Global obedience implies correlated equilibrium in the canonical
information structure. -/
theorem isSignalwiseCanonical_of_obedience (q : CorrelatedStrategy G)
    (h : ∀ (i : N) (s t : G.strategy i),
      0 <= obedienceDifference q i s t) :
    IsSignalwiseCanonicalCorrelatedEquilibriumDistribution G q := by
  apply (isSignalwiseCorrelatedEquilibrium_iff_actionwise
    (canonicalInformationStructure G q) (truthfulCanonicalStrategy G q)).mpr
  intro i a s t
  by_cases has : a = s
  · subst a
    rw [signalObedienceDifference_canonical_truthful_self]
    exact h i s t
  · rw [signalObedienceDifference_canonical_truthful_of_ne q i a s t has]

/-- Canonical correlated-equilibrium distributions satisfy global obedience. -/
theorem obedience_of_isSignalwiseCanonical (q : CorrelatedStrategy G)
    (h : IsSignalwiseCanonicalCorrelatedEquilibriumDistribution G q) :
    ∀ (i : N) (s t : G.strategy i),
      0 <= obedienceDifference q i s t := by
  intro i s t
  rw [← inducedDistribution_canonical_truthful (G := G) q]
  exact obedienceDifference_of_isSignalwiseCorrelatedEquilibrium
    (canonicalInformationStructure G q) (truthfulCanonicalStrategy G q) h i s t

/-- Every obedient distribution belongs to the signalwise outcome set via its
canonical information structure. -/
theorem mem_signalwiseCED_of_obedience (q : CorrelatedStrategy G)
    (h : ∀ (i : N) (s t : G.strategy i),
      0 <= obedienceDifference q i s t) :
    q ∈ SignalwiseCorrelatedEquilibriumDistributions G := by
  refine ⟨G.Profile, inferInstance, canonicalInformationStructure G q,
    truthfulCanonicalStrategy G q, isSignalwiseCanonical_of_obedience q h, ?_⟩
  exact inducedDistribution_canonical_truthful q

/-- Every signalwise canonical distribution belongs to the signalwise outcome
set. -/
theorem mem_signalwiseCED_of_isSignalwiseCanonical (q : CorrelatedStrategy G)
    (h : IsSignalwiseCanonicalCorrelatedEquilibriumDistribution G q) :
    q ∈ SignalwiseCorrelatedEquilibriumDistributions G :=
  mem_signalwiseCED_of_obedience q (obedience_of_isSignalwiseCanonical q h)

/-- Canonical and general signalwise correlated-equilibrium distributions
coincide. -/
theorem signalwiseCanonicalCorrelatedEquilibriumDistributions_eq_signalwiseCorrelatedEquilibriumDistributions
    (G : StrategicGame.{u_N, u_U, u_S} N U)
    [∀ i : N, Fintype (G.strategy i)]
    [∀ i : N, DecidableEq (G.strategy i)] :
    SignalwiseCanonicalCorrelatedEquilibriumDistributions G =
      SignalwiseCorrelatedEquilibriumDistributions G := by
  ext q
  constructor
  · exact mem_signalwiseCED_of_isSignalwiseCanonical q
  · rintro ⟨Omega, hOmega, I, sigma, hsigma, hinduced⟩
    letI := hOmega
    apply isSignalwiseCanonical_of_obedience q
    intro i s t
    rw [← hinduced]
    exact obedienceDifference_of_isSignalwiseCorrelatedEquilibrium I sigma hsigma i s t

/-- **MFoGT Theorem 7.2.6.** Canonical correlated-equilibrium distributions
exhaust all correlated-equilibrium distributions. Both sides use the same
behavioral-extension Nash-equilibrium predicate. -/
theorem canonicalCorrelatedEquilibriumDistributions_eq_correlatedEquilibriumDistributions
    (G : StrategicGame.{u_N, u_U, u_S} N U)
    [∀ i : N, Fintype (G.strategy i)]
    [∀ i : N, DecidableEq (G.strategy i)] :
    CanonicalCorrelatedEquilibriumDistributions G =
      CorrelatedEquilibriumDistributions G := by
  calc
    CanonicalCorrelatedEquilibriumDistributions G =
        SignalwiseCanonicalCorrelatedEquilibriumDistributions G :=
      canonicalCorrelatedEquilibriumDistributions_eq_signalwise G
    _ = SignalwiseCorrelatedEquilibriumDistributions G :=
      signalwiseCanonicalCorrelatedEquilibriumDistributions_eq_signalwiseCorrelatedEquilibriumDistributions G
    _ = CorrelatedEquilibriumDistributions G :=
      (correlatedEquilibriumDistributions_eq_signalwise G).symm

/-- **MFoGT Theorem 7.2.6, source-literal mixed-plan form.** The canonical set
defined by the point mass on the identity contingent-plan profile equals the
union of distributions induced by mixed Nash equilibria of all finite
contingent-plan extensions. -/
theorem mixedPlanCanonicalCorrelatedEquilibriumDistributions_eq_mixedPlanCED
    (G : StrategicGame.{u_N, u_U, u_S} N U)
    [∀ i : N, Fintype (G.strategy i)]
    [∀ i : N, DecidableEq (G.strategy i)] :
    MixedPlanCanonicalCorrelatedEquilibriumDistributions G =
      MixedContingentPlanCorrelatedEquilibriumDistributions G := by
  calc
    MixedPlanCanonicalCorrelatedEquilibriumDistributions G =
        CanonicalCorrelatedEquilibriumDistributions G :=
      mixedPlanCanonicalCorrelatedEquilibriumDistributions_eq_behavioral G
    _ = CorrelatedEquilibriumDistributions G :=
      canonicalCorrelatedEquilibriumDistributions_eq_correlatedEquilibriumDistributions G
    _ = MixedContingentPlanCorrelatedEquilibriumDistributions G :=
      (mixedContingentPlanCorrelatedEquilibriumDistributions_eq_behavioral G).symm

/-- Ex-post finite form underlying MFoGT Theorem 7.2.7: `q` belongs to the
signalwise presentation exactly when all finite obedience inequalities hold. -/
theorem mem_signalwiseCorrelatedEquilibriumDistributions_iff_obedience
    (G : StrategicGame.{u_N, u_U, u_S} N U)
    [∀ i : N, Fintype (G.strategy i)]
    [∀ i : N, DecidableEq (G.strategy i)]
    (q : CorrelatedStrategy G) :
    q ∈ SignalwiseCorrelatedEquilibriumDistributions G ↔
      ∀ (i : N) (s t : G.strategy i),
        0 <= obedienceDifference q i s t := by
  constructor
  · rintro ⟨Omega, hOmega, I, sigma, hsigma, hinduced⟩ i s t
    letI := hOmega
    rw [← hinduced]
    exact obedienceDifference_of_isSignalwiseCorrelatedEquilibrium I sigma hsigma i s t
  · exact mem_signalwiseCED_of_obedience q

/-- **MFoGT Theorem 7.2.7.** A distribution belongs to the Nash-based `CED(G)`
exactly when every finite obedience inequality holds. -/
theorem mem_correlatedEquilibriumDistributions_iff_obedience
    (G : StrategicGame.{u_N, u_U, u_S} N U)
    [∀ i : N, Fintype (G.strategy i)]
    [∀ i : N, DecidableEq (G.strategy i)]
    (q : CorrelatedStrategy G) :
    q ∈ CorrelatedEquilibriumDistributions G ↔
      ∀ (i : N) (s t : G.strategy i),
        0 <= obedienceDifference q i s t := by
  rw [correlatedEquilibriumDistributions_eq_signalwise]
  exact mem_signalwiseCorrelatedEquilibriumDistributions_iff_obedience G q

/-- An equilibrium of any finite behavioral information extension, regardless
of the event-space universe, induces an element of `CED(G)`. This theorem hides
the implementation universe chosen by the set-level existential definition. -/
theorem inducedDistribution_mem_correlatedEquilibriumDistributions
    {Omega : Type uOmega} [Fintype Omega]
    (I : InformationStructure G Omega) (sigma : ExtendedProfile I)
    (hsigma : IsExtendedNashEquilibrium I sigma) :
    inducedDistribution I sigma ∈ CorrelatedEquilibriumDistributions G := by
  apply (mem_correlatedEquilibriumDistributions_iff_obedience G _).mpr
  intro i s t
  exact obedienceDifference_of_isCorrelatedEquilibrium I sigma hsigma i s t

/-- **[MSZ, Theorem 8.7].** The independent product distribution induced by a
mixed Nash equilibrium is a correlated-equilibrium distribution. The proof
passes through the one-event, one-signal information extension, whose
equilibrium predicate is proved equivalent to ordinary mixed Nash
equilibrium. -/
theorem piProduct_mem_correlatedEquilibriumDistributions_of_isMixedNashEq
    (p : MixedProfile G) (hp : IsMixedNashEq G p) :
    stdSimplex.piProduct p ∈ CorrelatedEquilibriumDistributions G := by
  have hext :
      IsExtendedNashEquilibrium
          (trivialInformationStructure.{u_N, u_U, u_S, 0, 0} G)
          (trivialExtendedProfile.{u_N, u_U, u_S, 0, 0} G p) :=
    (isExtendedNashEquilibrium_trivial_iff_isMixedNashEq G p).2 hp
  rw [← inducedDistribution_trivial_eq_piProduct (G := G) p]
  exact inducedDistribution_mem_correlatedEquilibriumDistributions
    (trivialInformationStructure.{u_N, u_U, u_S, 0, 0} G)
    (trivialExtendedProfile.{u_N, u_U, u_S, 0, 0} G p)
    hext

/-- Obedience at a point mass reduces to the corresponding pure unilateral
deviation inequality when the recommended action is the point's own action,
and is zero for every other recommendation. -/
private theorem obedienceDifference_vertex
    (sigma : G.Profile) (i : N) (s t : G.strategy i) :
    obedienceDifference (stdSimplex.vertex sigma) i s t =
      if sigma i = s then
        G.payoff sigma i - G.payoff (deviate sigma i t) i
      else 0 := by
  classical
  unfold obedienceDifference
  rw [Finset.sum_eq_single sigma]
  · simp
  · intro rho _ hrho
    simp [hrho]
  · intro hsigma
    exact (hsigma (Finset.mem_univ sigma)).elim

/-- A point mass at `sigma` is a correlated-equilibrium distribution exactly
when `sigma` is a pure Nash equilibrium. This is the pure-strategy boundary
case of [MSZ, Theorem 8.7], with the converse supplied by the obedience
inequalities. -/
theorem vertex_mem_correlatedEquilibriumDistributions_iff_isNashEquilibrium
    (sigma : G.Profile) :
    stdSimplex.vertex sigma ∈ CorrelatedEquilibriumDistributions G ↔
      IsNashEquilibrium G sigma := by
  rw [mem_correlatedEquilibriumDistributions_iff_obedience]
  constructor
  · intro h i t
    have hi := h i (sigma i) t
    rw [obedienceDifference_vertex] at hi
    simpa using hi
  · intro h i s t
    by_cases hs : sigma i = s
    · subst s
      have hi : G.payoff (deviate sigma i t) i ≤ G.payoff sigma i := h i t
      rw [obedienceDifference_vertex]
      simpa using (sub_nonneg.mpr hi)
    · rw [obedienceDifference_vertex, if_neg hs]

/-- A mixed-plan equilibrium of any finite information extension induces an
element of `CED(G)`, independently of universe levels. -/
theorem inducedMixedContingentPlanDistribution_mem_correlatedEquilibriumDistributions
    {Omega : Type uOmega} [Fintype Omega]
    (I : InformationStructure G Omega) (mu : MixedContingentPlanProfile I)
    (hmu : IsMixedContingentPlanNashEquilibrium I mu) :
    inducedMixedContingentPlanDistribution I mu ∈
      CorrelatedEquilibriumDistributions G := by
  unfold inducedMixedContingentPlanDistribution
  exact inducedDistribution_mem_correlatedEquilibriumDistributions I
    (mixedContingentPlanProfileToBehavior I mu)
    ((isMixedContingentPlanNashEquilibrium_iff_behavioral I mu).mp hmu)

/-- Membership in the signalwise presentation is exactly the global obedience
predicate. -/
theorem mem_signalwiseCorrelatedEquilibriumDistributions_iff_isCorrelatedEq
    (G : StrategicGame.{u_N, u_U, u_S} N U)
    [∀ i : N, Fintype (G.strategy i)]
    [∀ i : N, DecidableEq (G.strategy i)]
    (q : CorrelatedStrategy G) :
    q ∈ SignalwiseCorrelatedEquilibriumDistributions G ↔ IsCorrelatedEq G q := by
  simpa [IsCorrelatedEq, ObedienceInequality] using
    mem_signalwiseCorrelatedEquilibriumDistributions_iff_obedience G q

/-- Membership in the Nash-based `CED(G)` is exactly the global obedience
predicate. -/
theorem mem_correlatedEquilibriumDistributions_iff_isCorrelatedEq
    (G : StrategicGame.{u_N, u_U, u_S} N U)
    [∀ i : N, Fintype (G.strategy i)]
    [∀ i : N, DecidableEq (G.strategy i)]
    (q : CorrelatedStrategy G) :
    q ∈ CorrelatedEquilibriumDistributions G ↔ IsCorrelatedEq G q := by
  simpa [IsCorrelatedEq, ObedienceInequality] using
    mem_correlatedEquilibriumDistributions_iff_obedience G q

/-- The ambient-vector set cut out by nonnegativity, total mass one, and the
finite family of linear obedience inequalities. -/
def SignalwiseCEDFiniteLinearInequalitySet
    (G : StrategicGame.{u_N, u_U, u_S} N U)
    [∀ i : N, Fintype (G.strategy i)]
    [∀ i : N, DecidableEq (G.strategy i)] :
    Set (G.Profile -> U) :=
  {x | (∀ rho : G.Profile, 0 ≤ x rho) ∧
    (∑ rho : G.Profile, x rho) = 1 ∧
    ∀ (i : N) (s t : G.strategy i),
      0 ≤ ∑ rho : G.Profile,
        if rho i = s then
          x rho * (G.payoff rho i - G.payoff (deviate rho i t) i)
        else 0}

/-- Exact finite linear-inequality representation of the signalwise outcome set
in the ambient profile-weight vector space. -/
theorem signalwiseCorrelatedEquilibriumDistributions_eq_finiteLinearInequalitySet
    (G : StrategicGame.{u_N, u_U, u_S} N U)
    [∀ i : N, Fintype (G.strategy i)]
    [∀ i : N, DecidableEq (G.strategy i)] :
    Subtype.val '' SignalwiseCorrelatedEquilibriumDistributions G =
      SignalwiseCEDFiniteLinearInequalitySet G := by
  ext x
  constructor
  · rintro ⟨q, hq, rfl⟩
    refine ⟨q.property.1, q.property.2, ?_⟩
    exact (mem_signalwiseCorrelatedEquilibriumDistributions_iff_obedience G q).mp hq
  · rintro ⟨hxnonneg, hxsum, hxobedience⟩
    let q : CorrelatedStrategy G := ⟨x, hxnonneg, hxsum⟩
    refine ⟨q, ?_, rfl⟩
    exact (mem_signalwiseCorrelatedEquilibriumDistributions_iff_obedience G q).mpr hxobedience

/-- The finite system of simplex and obedience constraints defining `CED(G)`. -/
abbrev CEDFiniteLinearInequalitySet
    (G : StrategicGame.{u_N, u_U, u_S} N U)
    [∀ i : N, Fintype (G.strategy i)]
    [∀ i : N, DecidableEq (G.strategy i)] :
    Set (G.Profile -> U) :=
  SignalwiseCEDFiniteLinearInequalitySet G

/-- Exact finite linear-inequality representation of the Nash-based `CED(G)`.
This is the formal linear-description assertion used in MFoGT Corollary 7.2.8. -/
theorem correlatedEquilibriumDistributions_eq_finiteLinearInequalitySet
    (G : StrategicGame.{u_N, u_U, u_S} N U)
    [∀ i : N, Fintype (G.strategy i)]
    [∀ i : N, DecidableEq (G.strategy i)] :
    Subtype.val '' CorrelatedEquilibriumDistributions G =
      CEDFiniteLinearInequalitySet G := by
  rw [correlatedEquilibriumDistributions_eq_signalwise]
  exact signalwiseCorrelatedEquilibriumDistributions_eq_finiteLinearInequalitySet G

/-- The finite simplex-and-obedience description is convex. -/
theorem cedFiniteLinearInequalitySet_convex
    (G : StrategicGame.{u_N, u_U, u_S} N U)
    [∀ i : N, Fintype (G.strategy i)]
    [∀ i : N, DecidableEq (G.strategy i)] :
    Convex U (CEDFiniteLinearInequalitySet G) := by
  classical
  intro x hx y hy a b ha hb hab
  rcases hx with ⟨hxnonneg, hxsum, hxobedience⟩
  rcases hy with ⟨hynonneg, hysum, hyobedience⟩
  refine ⟨?_, ?_, ?_⟩
  · intro rho
    change 0 ≤ a * x rho + b * y rho
    exact add_nonneg (mul_nonneg ha (hxnonneg rho))
      (mul_nonneg hb (hynonneg rho))
  · change (∑ rho : G.Profile, (a * x rho + b * y rho)) = 1
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hxsum, hysum]
    simpa using hab
  · intro i s t
    have hexpand :
        (∑ rho : G.Profile,
          if rho i = s then
            (a * x rho + b * y rho) *
              (G.payoff rho i - G.payoff (deviate rho i t) i)
          else 0) =
          a * (∑ rho : G.Profile,
            if rho i = s then
              x rho * (G.payoff rho i - G.payoff (deviate rho i t) i)
            else 0) +
          b * (∑ rho : G.Profile,
            if rho i = s then
              y rho * (G.payoff rho i - G.payoff (deviate rho i t) i)
            else 0) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro rho _
      by_cases hrho : rho i = s <;> simp [hrho]
      ring
    change 0 ≤ ∑ rho : G.Profile,
      if rho i = s then
        (a * x rho + b * y rho) *
          (G.payoff rho i - G.payoff (deviate rho i t) i)
      else 0
    rw [hexpand]
    exact add_nonneg (mul_nonneg ha (hxobedience i s t))
      (mul_nonneg hb (hyobedience i s t))

/-- The Nash-based correlated-equilibrium distributions form a convex subset
of the ambient profile-weight vector space, as observed after MFoGT Definition
7.2.4. -/
theorem correlatedEquilibriumDistributions_image_convex
    (G : StrategicGame.{u_N, u_U, u_S} N U)
    [∀ i : N, Fintype (G.strategy i)]
    [∀ i : N, DecidableEq (G.strategy i)] :
    Convex U (Subtype.val '' CorrelatedEquilibriumDistributions G) := by
  rw [correlatedEquilibriumDistributions_eq_finiteLinearInequalitySet]
  exact cedFiniteLinearInequalitySet_convex G

/-! #### MFoGT Corollary 7.2.8: finite convex-hull representation -/

/-- Finite index type for the simplex and obedience constraints defining
`CED(G)`: one nonnegativity constraint per profile, two inequalities for total
mass one, and one obedience constraint per player and ordered action pair. -/
private abbrev CEDLinearConstraint
    (G : StrategicGame.{u_N, 0, u_S} N ℝ) :=
  G.Profile ⊕ (Bool ⊕ Σ i : N, G.strategy i × G.strategy i)

private def cedConstraintCoefficient
    (G : StrategicGame.{u_N, 0, u_S} N ℝ)
    [∀ i : N, Fintype (G.strategy i)]
    [∀ i : N, DecidableEq (G.strategy i)]
    (c : CEDLinearConstraint G) : G.Profile → ℝ :=
  match c with
  | Sum.inl rho₀ => fun rho => if rho = rho₀ then 1 else 0
  | Sum.inr (Sum.inl false) => fun _ => 1
  | Sum.inr (Sum.inl true) => fun _ => -1
  | Sum.inr (Sum.inr ⟨i, (s, t)⟩) => fun rho =>
      if rho i = s then
        G.payoff rho i - G.payoff (deviate rho i t) i
      else 0

private def cedConstraintOffset
    (G : StrategicGame.{u_N, 0, u_S} N ℝ)
    (c : CEDLinearConstraint G) : ℝ :=
  match c with
  | Sum.inr (Sum.inl false) => 1
  | Sum.inr (Sum.inl true) => -1
  | _ => 0

private def cedConstraintLinear
    (G : StrategicGame.{u_N, 0, u_S} N ℝ)
    [∀ i : N, Fintype (G.strategy i)]
    [∀ i : N, DecidableEq (G.strategy i)]
    (c : CEDLinearConstraint G) :
    Module.Dual ℝ (G.Profile → ℝ) :=
  EconCSLib.Convex.finiteDotLinear (cedConstraintCoefficient G c)

/-- The explicit CED inequalities are a single finite family in the generic
finite-polyhedron interface. -/
private theorem cedFiniteLinearInequalitySet_eq_generic
    (G : StrategicGame.{u_N, 0, u_S} N ℝ)
    [∀ i : N, Fintype (G.strategy i)]
    [∀ i : N, DecidableEq (G.strategy i)] :
    CEDFiniteLinearInequalitySet G =
      EconCSLib.Convex.FiniteLinearInequalitySet
        (cedConstraintLinear G) (cedConstraintOffset G) := by
  classical
  ext x
  constructor
  · rintro ⟨hxnonneg, hxsum, hxobedience⟩ c
    rcases c with rho₀ | c
    · simpa [cedConstraintLinear, cedConstraintCoefficient,
        cedConstraintOffset] using hxnonneg rho₀
    · rcases c with mass | obedience
      · cases mass
        · simp [cedConstraintLinear, cedConstraintCoefficient,
            cedConstraintOffset, hxsum]
        · simp [cedConstraintLinear, cedConstraintCoefficient,
            cedConstraintOffset, hxsum]
      · rcases obedience with ⟨i, st⟩
        rcases st with ⟨s, t⟩
        simpa [cedConstraintLinear, cedConstraintCoefficient,
            cedConstraintOffset, mul_comm] using hxobedience i s t
  · intro hx
    refine ⟨?_, ?_, ?_⟩
    · intro rho₀
      simpa [cedConstraintLinear, cedConstraintCoefficient,
        cedConstraintOffset] using hx (Sum.inl rho₀)
    · have hlower := hx (Sum.inr (Sum.inl false))
      have hupper := hx (Sum.inr (Sum.inl true))
      simp [cedConstraintLinear, cedConstraintCoefficient,
        cedConstraintOffset] at hlower hupper
      linarith
    · intro i s t
      simpa [cedConstraintLinear, cedConstraintCoefficient,
        cedConstraintOffset, mul_comm] using
        hx (Sum.inr (Sum.inr ⟨i, (s, t)⟩))

/-- The CED finite inequality set is bounded because it lies in the standard
probability simplex. -/
private theorem cedFiniteLinearInequalitySet_isBounded
    (G : StrategicGame.{u_N, 0, u_S} N ℝ)
    [∀ i : N, Fintype (G.strategy i)]
    [∀ i : N, DecidableEq (G.strategy i)] :
    Bornology.IsBounded (CEDFiniteLinearInequalitySet G) := by
  apply (isCompact_stdSimplex ℝ G.Profile).isBounded.subset
  intro x hx
  exact ⟨hx.1, hx.2.1⟩

/-- The finite simplex-and-obedience system defining `CED(G)` is exactly the
convex hull of finitely many ambient profile-weight vectors. -/
theorem cedFiniteLinearInequalitySet_eq_convexHull_finset
    (G : StrategicGame.{u_N, 0, u_S} N ℝ)
    [∀ i : N, Fintype (G.strategy i)]
    [∀ i : N, DecidableEq (G.strategy i)] :
    ∃ V : Finset (G.Profile → ℝ),
      CEDFiniteLinearInequalitySet G = convexHull ℝ (V : Set (G.Profile → ℝ)) := by
  rw [cedFiniteLinearInequalitySet_eq_generic]
  apply EconCSLib.Convex.finiteLinearInequalitySet_eq_convexHull_finset
  rw [← cedFiniteLinearInequalitySet_eq_generic]
  exact cedFiniteLinearInequalitySet_isBounded G

/-- **MFoGT Corollary 7.2.8.** For a finite real-payoff strategic game, the set
of correlated-equilibrium distributions is a polytope: the convex hull of
finitely many points in the ambient profile-weight space. -/
theorem correlatedEquilibriumDistributions_eq_convexHull_finset
    (G : StrategicGame.{u_N, 0, u_S} N ℝ)
    [∀ i : N, Fintype (G.strategy i)]
    [∀ i : N, DecidableEq (G.strategy i)] :
    ∃ V : Finset (G.Profile → ℝ),
      Subtype.val '' CorrelatedEquilibriumDistributions G =
        convexHull ℝ (V : Set (G.Profile → ℝ)) := by
  obtain ⟨V, hV⟩ := cedFiniteLinearInequalitySet_eq_convexHull_finset G
  refine ⟨V, ?_⟩
  rw [correlatedEquilibriumDistributions_eq_finiteLinearInequalitySet, hV]

/-- The finite real correlated-equilibrium distribution set is compact in the
ambient profile-weight space. This is the compactness consequence of MFoGT
Corollary 7.2.8. -/
theorem correlatedEquilibriumDistributions_image_isCompact
    (G : StrategicGame.{u_N, 0, u_S} N ℝ)
    [∀ i : N, Fintype (G.strategy i)]
    [∀ i : N, DecidableEq (G.strategy i)] :
    IsCompact (Subtype.val '' CorrelatedEquilibriumDistributions G) := by
  obtain ⟨V, hV⟩ :=
    correlatedEquilibriumDistributions_eq_convexHull_finset G
  rw [hV]
  exact V.finite_toSet.isCompact_convexHull ℝ

end FiniteCorrelatedEquilibrium

section RealNashProduct

variable {N : Type u_N} [Fintype N] [DecidableEq N]
variable {G : StrategicGame.{u_N, 0, u_S} N ℝ}
variable [∀ i : N, Fintype (G.strategy i)]
variable [∀ i : N, DecidableEq (G.strategy i)]

/-- Real-payoff bridge from the all-mixed-deviations Nash predicate used by
the Brouwer existence theorem to [MSZ, Theorem 8.7]. Pure deviations are
special cases of mixed deviations, and the two expected-payoff definitions
unfold to the same finite product sum. -/
theorem piProduct_mem_correlatedEquilibriumDistributions_of_mixedNashEquilibrium
    (p : MixedS G) (hp : mixedNashEquilibrium G p) :
    stdSimplex.piProduct p ∈ CorrelatedEquilibriumDistributions G := by
  apply piProduct_mem_correlatedEquilibriumDistributions_of_isMixedNashEq p
  intro i s
  have h := hp i (pureToMixed s)
  simpa [evaluate_at_mixed, expectedPayoff, deviateMixed] using h

end RealNashProduct

end StrategicGame
