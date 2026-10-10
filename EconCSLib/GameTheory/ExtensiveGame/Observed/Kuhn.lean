/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Observed.Continuation
import EconCSLib.GameTheory.ExtensiveGame.Observed.Mixed
import EconCSLib.GameTheory.ExtensiveGame.Observed.PerfectRecall
import EconCSLib.GameTheory.ExtensiveGame.Observed.WellFormed

/-!
# EconCSLib.GameTheory.ExtensiveGame.Observed.Kuhn

Realization certificates between mixed contingent plans and behavioral
strategies.

Kuhn's theorem is a realization theorem, not generally a strict isomorphism of
strategy spaces.  This module makes that distinction structural.  A
root-scoped certificate supplies:

* a playerwise map from mixed plans to behavioral strategies;
* equality of the complete bounded payoff law at the selected root;
* exact realization of every unilateral behavioral deviation by a mixed
  deviation.

These fields induce a `LawGameForm.Hom` with semantic deviation completeness,
and therefore give two-way Nash transfer without claiming strategy
surjectivity.

A second, deliberately stronger continuation-wide certificate requires one
global behavioralization map to satisfy the same equations at every
continuation root.  It induces a `ContinuationGameForm.Hom` and bounded Nash on presentation-designated continuations
transfer.  Perfect recall alone should not be used to construct this stronger
certificate for arbitrary mixed profiles: ex-ante correlations between a
player's choices can make root-scoped conditioning depend on the continuation.

`FiniteKuhnHypotheses` records the assumptions used by the constructive
root-scoped theorem in `KuhnConditioning`: perfect recall and finitely
many decision information states per player.

`FiniteInformationHypotheses` records exactly what is needed to construct the
independent complete-plan law and prove its local marginals.
`FiniteNoAbsentMindednessHypotheses` adds the no-repeated-decision-key property
needed only when that pre-sampled law is compared with repeated local
behavioral execution.

## Main definitions

* `ObservedGame.FiniteKuhnHypotheses`.
* `ObservedGame.FiniteInformationHypotheses`.
* `ObservedGame.FiniteNoAbsentMindednessHypotheses`.
* `ObservedGame.BehavioralStrategy.toMixed`.
* `ObservedChanceGame.mixedContinuationFamilyOnRoots`.
* `ObservedChanceGame.MixedBehavioralRealizationAt`.
* `ObservedChanceGame.MixedBehavioralContinuationRealization`.

## Main results

* `MixedBehavioralRealizationAt.lawHom`.
* `MixedBehavioralRealizationAt.isNash_iff`.
* `MixedBehavioralContinuationRealization.continuationHom`.
* `MixedBehavioralContinuationRealization.isNashOnRootsAtFuel_iff`.

The concrete conditional construction and the resulting unconditional
bounded Kuhn Nash-on-designated-continuations theorems are in `KuhnConditioning`.

## Source boundary

The finite perfect-recall realization target is [Kuhn 1953, §4, Thm. 4] and
[MFoGT, Thm. 6.3.4]. The Lean certificates below use discrete `FiniteLaw` laws and
terminal-aware bounded complete-history execution. Root-scoped conditioning,
deviation-complete law morphisms, and continuation-family transport are
EconCSLib representation theorems; the citations do not justify an
arbitrary-measure or infinite-path equivalence.
-/

namespace ExtensiveGame.ObservedGame

variable {N U : Type*}

/-- Standard finiteness and recall hypotheses for the constructive,
root-scoped Kuhn realization theorem proved in `KuhnConditioning`.

Keeping the hypotheses separate from the realization certificate lets the
base API state generic transfer theorems without baking in one particular
conditionalization construction. -/
structure FiniteKuhnHypotheses
    (G : ObservedGame N U) [DecidableEq N] where
  /-- Executable factorization of remembered own decisions. -/
  recallCertificate : G.RecallCertificate
  /-- Explicit represented-information order and executable action equality. -/
  finiteDecisionPresentation :
    ∀ i : N,
      (Σ size : ℕ, G.RepresentedInfo i ≃ Fin size) ×
        (∀ information : G.RepresentedInfo i,
          DecidableEq (G.InfoAction i information.1))

/-- The exact hypotheses needed to pre-sample a behavioral profile as
independent complete contingent plans and prove their local action marginals.

No player equality or recall property is needed at this construction layer. -/
structure FiniteInformationHypotheses
    (G : ObservedGame N U) where
  /-- Explicit represented-information order and executable action equality. -/
  finiteDecisionPresentation :
    ∀ i : N,
      (Σ size : ℕ, G.RepresentedInfo i ≃ Fin size) ×
        (∀ information : G.RepresentedInfo i,
          DecidableEq (G.InfoAction i information.1))

/-- The exact structural hypotheses needed to identify pre-sampled complete
plans with repeated local behavioral execution.

Unlike `FiniteKuhnHypotheses`, this does not require perfect recall.  It
requires only the no-repeated-decision-key property consumed by deferred
sampling, together with finite decision-information types. -/
structure FiniteNoAbsentMindednessHypotheses
    (G : ObservedGame N U) [DecidableEq N] where
  /-- No player revisits one decision information state along a history. -/
  noAbsentMindedness : G.NoAbsentMindedness
  /-- Explicit represented-information order and executable action equality. -/
  finiteDecisionPresentation :
    ∀ i : N,
      (Σ size : ℕ, G.RepresentedInfo i ≃ Fin size) ×
        (∀ information : G.RepresentedInfo i,
          DecidableEq (G.InfoAction i information.1))

namespace FiniteEFGHypotheses

variable {G : ObservedGame N U}

/-- The structural finite-EFG certificate supplies the finite-information
hypothesis needed for independent complete-plan sampling. -/
def toFiniteInformationHypotheses
    (h : G.FiniteEFGHypotheses) :
    G.FiniteInformationHypotheses where
  finiteDecisionPresentation := h.finiteDecisionPresentation

/-- Adding an explicit recall certificate to a structural finite-EFG
certificate supplies the standard hypotheses for root-scoped constructive
Kuhn realization. -/
def toFiniteKuhnHypotheses
    [DecidableEq N]
    (h : G.FiniteEFGHypotheses)
    (recallCertificate : G.RecallCertificate) :
    G.FiniteKuhnHypotheses where
  recallCertificate := recallCertificate
  finiteDecisionPresentation := h.finiteDecisionPresentation

end FiniteEFGHypotheses

namespace BehavioralStrategy

variable (G : ObservedGame N U)

/-- Independently sample one abstract action at every decision information
state to obtain a law on complete pure contingent plans.

This construction is the behavioral-to-mixed half of the finite Kuhn bridge.
Perfect recall is not needed for the construction or its local marginals; it
is not needed for the execution comparison either: no-absent-mindedness is the
strictly weaker property consumed there. -/
def toMixed {i : N}
    [Fintype (G.RepresentedInfo i)] [LinearOrder (G.RepresentedInfo i)]
    (strategy : G.BehavioralStrategy i) :
    G.MixedStrategy i := by
  change
    (information : G.RepresentedInfo i) →
      FiniteLaw (G.InfoAction i information.1) at strategy
  change
    FiniteLaw
      ((information : G.RepresentedInfo i) →
        G.InfoAction i information.1)
  exact FiniteLaw.fintypePi strategy

/-- The sampled pure plan has exactly the declared behavioral action law at
each information state. -/
theorem toMixed_actionMarginal {i : N}
    [Fintype (G.RepresentedInfo i)] [LinearOrder (G.RepresentedInfo i)]
    (strategy : G.BehavioralStrategy i)
    (information : G.RepresentedInfo i) :
    ((toMixed G strategy).map
        (fun pureStrategy =>
          pureStrategy information)).Equivalent
      (strategy information) := by
  change
    (information : G.RepresentedInfo i) →
      FiniteLaw (G.InfoAction i information.1) at strategy
  change
    ((FiniteLaw.fintypePi strategy).map
        (fun pureStrategy =>
          pureStrategy information)).Equivalent
      (strategy information)
  exact FiniteLaw.fintypePi_map_apply
    strategy information

end BehavioralStrategy

namespace FiniteInformationHypotheses

variable {G : ObservedGame N U}

/-- Behavioral-to-mixed construction under an explicit finite decision
presentation. -/
def behavioralToMixedStrategy
    (h : G.FiniteInformationHypotheses)
    (i : N)
    (strategy : G.BehavioralStrategy i) :
    G.MixedStrategy i :=
  let presentation := (h.finiteDecisionPresentation i).1
  letI : Fintype (G.RepresentedInfo i) :=
    Fintype.ofEquiv (Fin presentation.1) presentation.2.symm
  letI : LinearOrder (G.RepresentedInfo i) :=
    LinearOrder.lift' presentation.2 presentation.2.injective
  strategy.toMixed G

/-- Independently pre-sample every player's complete contingent plan. -/
def behavioralToMixedProfile
    (h : G.FiniteInformationHypotheses)
    (profile : G.BehavioralProfile) :
    G.MixedProfile :=
  fun i =>
    h.behavioralToMixedStrategy i (profile i)

/-- Every local action marginal of the weak-hypothesis construction is the
declared behavioral law. -/
theorem behavioralToMixedStrategy_actionMarginal
    (h : G.FiniteInformationHypotheses)
    (i : N)
    (strategy : G.BehavioralStrategy i)
    (information : G.RepresentedInfo i) :
    ((h.behavioralToMixedStrategy i strategy).map
        (fun pureStrategy => pureStrategy information)).Equivalent
      (strategy information) := by
  let presentation := (h.finiteDecisionPresentation i).1
  letI : Fintype (G.RepresentedInfo i) :=
    Fintype.ofEquiv (Fin presentation.1) presentation.2.symm
  letI : LinearOrder (G.RepresentedInfo i) :=
    LinearOrder.lift' presentation.2 presentation.2.injective
  exact
    BehavioralStrategy.toMixed_actionMarginal
      G strategy information

/-! The concrete-history forms below still consume only finite represented information:
`actionAt` merely realizes the already-sampled abstract action through the
game's indexed action equivalence. -/

/-- At a concrete player history, the action prescribed by the sampled pure
plan has exactly the source behavioral concrete-action law. -/
theorem behavioralToMixedStrategy_actionLawAt
    (h : G.FiniteInformationHypotheses)
    (i : N)
    (strategy : G.BehavioralStrategy i)
    (history :
      G.base.toArena.HistoryFrom G.base.init)
    (hmover :
      G.base.mover history.1 = some i)
    (hnonterminal :
      ¬ G.base.isTerminal history.1) :
    ((h.behavioralToMixedStrategy
      i strategy).map
        (fun pureStrategy =>
          pureStrategy.actionAt
            G history hmover
              (G.base.toArena.isDecision_of_not_isTerminal _
                hnonterminal))).Equivalent
      (strategy.actionLawAt
        G history hmover hnonterminal) := by
  let hdecision :=
    G.base.toArena.isDecision_of_not_isTerminal
      history.1 hnonterminal
  unfold PureStrategy.actionAt
    BehavioralStrategy.actionLawAt
  apply FiniteLaw.Equivalent.trans
    (second :=
      ((h.behavioralToMixedStrategy i strategy).map
        (fun pureStrategy =>
          pureStrategy
            (G.representedInfoAt history i hmover hdecision))).map
        (G.actionEquiv history i hmover hdecision))
  · apply FiniteLaw.Equivalent.of_eq
    exact
      (FiniteLaw.map_comp
        (fun pureStrategy =>
          pureStrategy
            (G.representedInfoAt history i hmover hdecision))
        (h.behavioralToMixedStrategy i strategy)
        (G.actionEquiv history i hmover hdecision)).symm
  · exact
      (h.behavioralToMixedStrategy_actionMarginal
        i strategy
        (G.representedInfoAt history i hmover hdecision)).map
          (G.actionEquiv history i hmover hdecision)

/-- The independently sampled complete pure profile has the same current
concrete-action marginal as the source behavioral profile. -/
theorem behavioralToMixedProfile_actionLawAt
    [Fintype N] [LinearOrder N]
    (h : G.FiniteInformationHypotheses)
    (profile : G.BehavioralProfile)
    (history :
      G.base.toArena.HistoryFrom G.base.init)
    (i : N)
    (hmover :
      G.base.mover history.1 = some i)
    (hnonterminal :
      ¬ G.base.isTerminal history.1) :
    (((h.behavioralToMixedProfile
        profile).pureProfileLaw G).map
        (fun pureProfile =>
          pureProfile.actionAt
            G history i hmover
              (G.base.toArena.isDecision_of_not_isTerminal _
                hnonterminal))).Equivalent
      (profile.actionLawAt
        G history i hmover hnonterminal) := by
  unfold MixedProfile.pureProfileLaw
  apply FiniteLaw.Equivalent.trans
    (second :=
      ((FiniteLaw.fintypePi
        (h.behavioralToMixedProfile profile)).map
          (fun pureProfile => pureProfile i)).map
        (fun pureStrategy =>
          PureStrategy.actionAt G pureStrategy history hmover
            (G.base.toArena.isDecision_of_not_isTerminal _ hnonterminal)))
  · apply FiniteLaw.Equivalent.of_eq
    exact
      (FiniteLaw.map_comp
        (fun pureProfile => pureProfile i)
        (FiniteLaw.fintypePi (h.behavioralToMixedProfile profile))
        (fun pureStrategy =>
          PureStrategy.actionAt G pureStrategy history hmover
            (G.base.toArena.isDecision_of_not_isTerminal _ hnonterminal))).symm
  · exact
      (FiniteLaw.fintypePi_map_apply
        (h.behavioralToMixedProfile profile) i).map
          (fun pureStrategy =>
            PureStrategy.actionAt G pureStrategy history hmover
              (G.base.toArena.isDecision_of_not_isTerminal _ hnonterminal) ) |>.trans
        (h.behavioralToMixedStrategy_actionLawAt
          i (profile i) history hmover hnonterminal)

end FiniteInformationHypotheses

namespace FiniteNoAbsentMindednessHypotheses

variable {G : ObservedGame N U} [DecidableEq N]

/-- Forget no-absent-mindedness and retain exactly the finite-information
construction hypotheses. -/
def toFiniteInformationHypotheses
    (h : G.FiniteNoAbsentMindednessHypotheses) :
    G.FiniteInformationHypotheses where
  finiteDecisionPresentation := h.finiteDecisionPresentation

/-- Compatibility wrapper for the finite-information construction. -/
def behavioralToMixedStrategy
    (h : G.FiniteNoAbsentMindednessHypotheses)
    (i : N)
    (strategy : G.BehavioralStrategy i) :
    G.MixedStrategy i :=
  h.toFiniteInformationHypotheses.behavioralToMixedStrategy i strategy

/-- Compatibility wrapper for independently sampled complete profiles. -/
def behavioralToMixedProfile
    (h : G.FiniteNoAbsentMindednessHypotheses)
    (profile : G.BehavioralProfile) :
    G.MixedProfile :=
  h.toFiniteInformationHypotheses.behavioralToMixedProfile profile

/-- Compatibility wrapper for the abstract local marginal theorem. -/
theorem behavioralToMixedStrategy_actionMarginal
    (h : G.FiniteNoAbsentMindednessHypotheses)
    (i : N)
    (strategy : G.BehavioralStrategy i)
    (information : G.RepresentedInfo i) :
    ((h.behavioralToMixedStrategy i strategy).map
        (fun pureStrategy => pureStrategy information)).Equivalent
      (strategy information) :=
  h.toFiniteInformationHypotheses.behavioralToMixedStrategy_actionMarginal
    i strategy information

/-- Compatibility wrapper for the concrete local action-law theorem. -/
theorem behavioralToMixedStrategy_actionLawAt
    (h : G.FiniteNoAbsentMindednessHypotheses)
    (i : N)
    (strategy : G.BehavioralStrategy i)
    (history :
      G.base.toArena.HistoryFrom G.base.init)
    (hmover :
      G.base.mover history.1 = some i)
    (hnonterminal :
      ¬ G.base.isTerminal history.1) :
    ((h.behavioralToMixedStrategy i strategy).map
        (fun pureStrategy =>
          pureStrategy.actionAt G history hmover
            (G.base.toArena.isDecision_of_not_isTerminal _
              hnonterminal))).Equivalent
      (strategy.actionLawAt G history hmover hnonterminal) :=
  h.toFiniteInformationHypotheses.behavioralToMixedStrategy_actionLawAt
    i strategy history hmover hnonterminal

/-- Compatibility wrapper for the complete-profile concrete marginal. -/
theorem behavioralToMixedProfile_actionLawAt
    [Fintype N] [LinearOrder N]
    (h : G.FiniteNoAbsentMindednessHypotheses)
    (profile : G.BehavioralProfile)
    (history :
      G.base.toArena.HistoryFrom G.base.init)
    (i : N)
    (hmover :
      G.base.mover history.1 = some i)
    (hnonterminal :
      ¬ G.base.isTerminal history.1) :
    (((h.behavioralToMixedProfile profile).pureProfileLaw G).map
        (fun pureProfile =>
          pureProfile.actionAt G history i hmover
            (G.base.toArena.isDecision_of_not_isTerminal _
              hnonterminal))).Equivalent
      (profile.actionLawAt G history i hmover hnonterminal) :=
  h.toFiniteInformationHypotheses.behavioralToMixedProfile_actionLawAt
    profile history i hmover hnonterminal

end FiniteNoAbsentMindednessHypotheses

namespace FiniteKuhnHypotheses

variable {G : ObservedGame N U} [DecidableEq N]

/-- Forget recall and retain exactly the finite-information construction
hypotheses. -/
def toFiniteInformationHypotheses
    (h : G.FiniteKuhnHypotheses) :
    G.FiniteInformationHypotheses where
  finiteDecisionPresentation := h.finiteDecisionPresentation

/-- The perfect-recall component supplies the no-repeated-information-key
condition needed by the pre-sampled execution proof. -/
theorem noAbsentMindedness
    (h : G.FiniteKuhnHypotheses) :
    G.NoAbsentMindedness :=
  h.recallCertificate.perfectRecall.noAbsentMindedness

/-- Forget perfect recall and retain exactly the assumptions required for the
behavioral-to-mixed deferred-sampling direction. -/
def toFiniteNoAbsentMindednessHypotheses
    (h : G.FiniteKuhnHypotheses) :
    G.FiniteNoAbsentMindednessHypotheses where
  noAbsentMindedness := h.noAbsentMindedness
  finiteDecisionPresentation := h.finiteDecisionPresentation

/-- Behavioral-to-mixed construction using the finite-information witness
stored in the Kuhn hypotheses.

This is a compatibility wrapper around the weaker
`FiniteNoAbsentMindednessHypotheses` construction. -/
def behavioralToMixedStrategy
    (h : G.FiniteKuhnHypotheses)
    (i : N)
    (strategy : G.BehavioralStrategy i) :
    G.MixedStrategy i :=
  h.toFiniteNoAbsentMindednessHypotheses.behavioralToMixedStrategy
    i strategy

/-- Map a complete behavioral profile to independent laws on each player's
complete contingent plans.

This is a compatibility wrapper around the weaker
`FiniteNoAbsentMindednessHypotheses` construction. -/
def behavioralToMixedProfile
    (h : G.FiniteKuhnHypotheses)
    (profile : G.BehavioralProfile) :
    G.MixedProfile :=
  h.toFiniteNoAbsentMindednessHypotheses.behavioralToMixedProfile
    profile

/-- Every local action marginal of the constructed mixed plan is the source
behavioral law. -/
theorem behavioralToMixedStrategy_actionMarginal
    (h : G.FiniteKuhnHypotheses)
    (i : N)
    (strategy : G.BehavioralStrategy i)
    (information : G.RepresentedInfo i) :
    ((h.behavioralToMixedStrategy
      i strategy).map
        (fun pureStrategy =>
          pureStrategy information)).Equivalent
      (strategy information) := by
  exact
    FiniteNoAbsentMindednessHypotheses.behavioralToMixedStrategy_actionMarginal
      h.toFiniteNoAbsentMindednessHypotheses
      i strategy information

/-- At a concrete player history, the action prescribed by the sampled pure
plan has exactly the source behavioral concrete-action law. -/
theorem behavioralToMixedStrategy_actionLawAt
    (h : G.FiniteKuhnHypotheses)
    (i : N)
    (strategy : G.BehavioralStrategy i)
    (history :
      G.base.toArena.HistoryFrom G.base.init)
    (hmover :
      G.base.mover history.1 = some i)
    (hnonterminal :
      ¬ G.base.isTerminal history.1) :
    ((h.behavioralToMixedStrategy
      i strategy).map
        (fun pureStrategy =>
          pureStrategy.actionAt
            G history hmover
              (G.base.toArena.isDecision_of_not_isTerminal _
                hnonterminal))).Equivalent
      (strategy.actionLawAt
        G history hmover hnonterminal) :=
  FiniteNoAbsentMindednessHypotheses.behavioralToMixedStrategy_actionLawAt
    h.toFiniteNoAbsentMindednessHypotheses
    i strategy history hmover hnonterminal

/-- The independently sampled complete pure profile has the same current
concrete-action marginal as the source behavioral profile. -/
theorem behavioralToMixedProfile_actionLawAt
    [Fintype N] [LinearOrder N]
    (h : G.FiniteKuhnHypotheses)
    (profile : G.BehavioralProfile)
    (history :
      G.base.toArena.HistoryFrom G.base.init)
    (i : N)
    (hmover :
      G.base.mover history.1 = some i)
    (hnonterminal :
      ¬ G.base.isTerminal history.1) :
    (((h.behavioralToMixedProfile
        profile).pureProfileLaw G).map
        (fun pureProfile =>
          pureProfile.actionAt
            G history i hmover
              (G.base.toArena.isDecision_of_not_isTerminal _
                hnonterminal))).Equivalent
      (profile.actionLawAt
        G history i hmover hnonterminal) :=
  FiniteNoAbsentMindednessHypotheses.behavioralToMixedProfile_actionLawAt
    h.toFiniteNoAbsentMindednessHypotheses
    profile history i hmover hnonterminal

end FiniteKuhnHypotheses

end ExtensiveGame.ObservedGame

namespace ExtensiveGame.ObservedChanceGame

universe uV

variable {N U : Type*}

/-- Bounded mixed contingent-plan continuations on a separately supplied root
presentation. -/
def mixedContinuationFamilyOnRoots
    (G : ObservedChanceGame N U)
    [Fintype N] [LinearOrder N]
    [(state : G.observed.base.State) →
      Decidable (G.observed.base.isTerminal state)]
    (roots : G.observed.RootPresentation)
    (fuel : ℕ) :
    ContinuationGameForm N where
  Strategy := G.observed.MixedStrategy
  Root :=
    G.observed.base.toArena.HistoryFrom
      G.observed.base.init
  IsDeclaredRoot := roots.IsRoot
  Outcome := FiniteLaw (Option (N → U))
  outcome := fun current profile =>
    G.mixedStoppedPayoffLawFrom profile current fuel

/-- Fixing a root in the mixed continuation family recovers the deterministic
view of the mixed law game form definitionally. -/
theorem mixedContinuationFamilyOnRoots_toGameForm
    (G : ObservedChanceGame N U)
    [Fintype N] [LinearOrder N]
    [(state : G.observed.base.State) →
      Decidable
        (G.observed.base.isTerminal state)]
    (roots : G.observed.RootPresentation)
    (fuel : ℕ)
    (current :
      G.observed.base.toArena.HistoryFrom
        G.observed.base.init) :
    (G.mixedContinuationFamilyOnRoots
      roots fuel).toGameForm current =
      (G.mixedLawGameForm current fuel).toGameForm :=
  rfl

/-- Bounded mixed Nash on presentation-designated continuations is exactly Nash on presentation-designated continuations in the representation-neutral mixed
continuation family. -/
theorem isMixedNashOnRootsAtFuel_iff_continuationFamily
    (G : ObservedChanceGame N U)
    [Fintype N] [LinearOrder N] [DecidableEq N] [Preorder V]
    [(state : G.observed.base.State) →
      Decidable
        (G.observed.base.isTerminal state)]
    (roots : G.observed.RootPresentation)
    (utility :
      FiniteLaw (Option (N → U)) → N → V)
    (profile : G.observed.MixedProfile)
    (fuel : ℕ) :
    G.IsMixedNashOnRootsAtFuel
        roots utility profile fuel ↔
      (G.mixedContinuationFamilyOnRoots
        roots fuel).IsNashOnRoots
          (fun _ => utility) profile :=
  Iff.rfl

/-! ### Root-scoped realization -/

/-- Exact strategic realization of mixed contingent plans by behavioral
strategies at one bounded continuation.

The deviation field is semantic rather than syntactic: every behavioral
deviation must have the same payoff law as some mixed deviation, but the
behavioral strategy itself need not lie in the image of `behavioralize`. -/
structure MixedBehavioralRealizationAt
    (G : ObservedChanceGame N U)
    [Fintype N] [LinearOrder N]
    [(state : G.observed.base.State) →
      Decidable
        (G.observed.base.isTerminal state)]
    (current :
      G.observed.base.toArena.HistoryFrom
        G.observed.base.init)
    (fuel : ℕ) where
  /-- Convert each player's mixed plan to a behavioral strategy. -/
  behavioralize :
    (i : N) →
      G.observed.MixedStrategy i →
        G.observed.BehavioralStrategy i
  /-- The mapped complete profile has the same semantic payoff law as the
  source profile. -/
  map_payoffLaw :
    ∀ profile : G.observed.MixedProfile,
      (G.behavioralStoppedPayoffLawFrom
          (fun i => behavioralize i (profile i))
          current fuel).Equivalent
        (G.mixedStoppedPayoffLawFrom
          profile current fuel)
  /-- Every unilateral behavioral deviation is semantically realized by a
  mixed deviation in the same opponents' context. -/
  realize_deviation :
    ∀ (profile : G.observed.MixedProfile)
      (i : N)
      (targetStrategy :
        G.observed.BehavioralStrategy i),
      ∃ sourceStrategy :
          G.observed.MixedStrategy i,
        (G.behavioralStoppedPayoffLawFrom
            (Function.update
              (fun j => behavioralize j (profile j))
              i targetStrategy)
            current fuel).Equivalent
          (G.mixedStoppedPayoffLawFrom
            (Function.update profile i sourceStrategy)
            current fuel)

namespace MixedBehavioralRealizationAt

variable
    {G : ObservedChanceGame N U}
    [Fintype N] [LinearOrder N]
    [(state : G.observed.base.State) →
      Decidable
        (G.observed.base.isTerminal state)]
    {current :
      G.observed.base.toArena.HistoryFrom
        G.observed.base.init}
    {fuel : ℕ}

/-- Map a complete mixed profile through a root-scoped realization. -/
def mapProfile
    (R : G.MixedBehavioralRealizationAt current fuel)
    (profile : G.observed.MixedProfile) :
    G.observed.BehavioralProfile :=
  fun i => R.behavioralize i (profile i)

@[simp]
theorem mapProfile_apply
    (R : G.MixedBehavioralRealizationAt current fuel)
    (profile : G.observed.MixedProfile)
    (i : N) :
    R.mapProfile profile i =
      R.behavioralize i (profile i) :=
  rfl

/-- The root-scoped certificate semantically realizes every mixed profile by
its mapped behavioral profile. -/
theorem lawHom
    (R : G.MixedBehavioralRealizationAt current fuel)
    (profile : G.observed.MixedProfile) :
    (G.mixedStoppedPayoffLawFrom
      profile current fuel).Equivalent
      (G.behavioralStoppedPayoffLawFrom
        (R.mapProfile profile) current fuel) :=
  (R.map_payoffLaw profile).symm

/-- The induced law morphism uses the certificate's profile map. -/
@[simp]
theorem lawHom_mapProfile
    (R : G.MixedBehavioralRealizationAt current fuel)
    (profile : G.observed.MixedProfile) :
    (G.mixedStoppedPayoffLawFrom
      profile current fuel).Equivalent
      (G.behavioralStoppedPayoffLawFrom
        (R.mapProfile profile) current fuel) :=
  R.lawHom profile

/-- The root-scoped realization gives exact semantic coverage of all
behavioral deviation laws. -/
theorem lawHom_outcomeDeviationCompleteAt
    (R : G.MixedBehavioralRealizationAt current fuel)
    (profile : G.observed.MixedProfile) :
    ∀ (i : N)
      (targetStrategy : G.observed.BehavioralStrategy i),
      ∃ sourceStrategy : G.observed.MixedStrategy i,
        (G.behavioralStoppedPayoffLawFrom
          (Function.update
            (R.mapProfile profile)
            i targetStrategy)
          current fuel).Equivalent
        (G.mixedStoppedPayoffLawFrom
          (Function.update profile i sourceStrategy)
          current fuel) := by
  intro i targetStrategy
  obtain ⟨sourceStrategy, hrealizes⟩ :=
    R.realize_deviation
      profile i targetStrategy
  refine ⟨sourceStrategy, ?_⟩
  exact hrealizes

/-- Root-scoped realization preserves and reflects Nash equilibrium for every
functional on the complete payoff law. -/
theorem isNash_iff
    [Preorder V]
    (R : G.MixedBehavioralRealizationAt current fuel)
    (utility :
      FiniteLaw (Option (N → U)) → N → V)
    (hutility : ∀ {left right}, left.Equivalent right →
      ∀ i, utility left i = utility right i)
    (profile : G.observed.MixedProfile) :
    (G.mixedLawGameForm current fuel).IsNash
        utility profile ↔
      (G.behavioralLawGameForm current fuel).IsNash
        utility (R.mapProfile profile) := by
  constructor
  · intro hmixed i targetStrategy
    obtain ⟨sourceStrategy, hdeviation⟩ :=
      R.realize_deviation profile i targetStrategy
    have hmixedDeviation := hmixed i sourceStrategy
    calc
      utility (G.behavioralStoppedPayoffLawFrom
          (Function.update (R.mapProfile profile)
            i targetStrategy) current fuel) i =
          utility (G.mixedStoppedPayoffLawFrom
            (Function.update profile i sourceStrategy)
            current fuel) i :=
        hutility hdeviation i
      _ ≤ utility (G.mixedStoppedPayoffLawFrom
            profile current fuel) i := hmixedDeviation
      _ = utility (G.behavioralStoppedPayoffLawFrom
            (R.mapProfile profile) current fuel) i :=
        (hutility (R.map_payoffLaw profile) i).symm
  · intro hbehavior i targetStrategy
    have hbehaviorDeviation :=
      hbehavior i (R.behavioralize i targetStrategy)
    have hupdated :
        R.mapProfile (Function.update profile i targetStrategy) =
          Function.update (R.mapProfile profile) i
            (R.behavioralize i targetStrategy) := by
      funext j
      by_cases hji : j = i
      · subst j
        simp [mapProfile]
      · simp [mapProfile, hji]
    have hdeviation :=
      R.map_payoffLaw (Function.update profile i targetStrategy)
    change
      (G.behavioralStoppedPayoffLawFrom
        (R.mapProfile (Function.update profile i targetStrategy))
        current fuel).Equivalent
      (G.mixedStoppedPayoffLawFrom
        (Function.update profile i targetStrategy)
        current fuel) at hdeviation
    rw [hupdated] at hdeviation
    calc
      utility (G.mixedStoppedPayoffLawFrom
          (Function.update profile i targetStrategy)
          current fuel) i =
          utility (G.behavioralStoppedPayoffLawFrom
            (Function.update (R.mapProfile profile) i
              (R.behavioralize i targetStrategy))
            current fuel) i :=
        (hutility hdeviation i).symm
      _ ≤ utility (G.behavioralStoppedPayoffLawFrom
            (R.mapProfile profile) current fuel) i :=
        hbehaviorDeviation
      _ = utility (G.mixedStoppedPayoffLawFrom
            profile current fuel) i :=
        hutility (R.map_payoffLaw profile) i

end MixedBehavioralRealizationAt

/-! ### Continuation-wide realization -/

/-- A single mixed-to-behavioral strategy map that realizes complete laws and
all unilateral deviations at every continuation root.

This is intentionally stronger than a root-scoped Kuhn certificate.  Supplying
it is sufficient for Nash on presentation-designated continuations transfer; `FiniteKuhnHypotheses` alone is not claimed
to imply it for arbitrary mixed profiles. -/
structure MixedBehavioralContinuationRealization
    (G : ObservedChanceGame N U)
    [Fintype N] [LinearOrder N]
    [(state : G.observed.base.State) →
      Decidable
        (G.observed.base.isTerminal state)]
    (fuel : ℕ) where
  /-- One root-independent behavioralization map for complete strategies. -/
  behavioralize :
    (i : N) →
      G.observed.MixedStrategy i →
        G.observed.BehavioralStrategy i
  /-- Exact payoff-law realization at every continuation. -/
  map_payoffLaw :
    ∀ (profile : G.observed.MixedProfile)
      (current :
        G.observed.base.toArena.HistoryFrom
          G.observed.base.init),
      G.behavioralStoppedPayoffLawFrom
          (fun i => behavioralize i (profile i))
          current fuel =
        G.mixedStoppedPayoffLawFrom
          profile current fuel
  /-- Exact deviation realization at every continuation. -/
  realize_deviation :
    ∀ (profile : G.observed.MixedProfile)
      (current :
        G.observed.base.toArena.HistoryFrom
          G.observed.base.init)
      (i : N)
      (targetStrategy :
        G.observed.BehavioralStrategy i),
      ∃ sourceStrategy :
          G.observed.MixedStrategy i,
        G.behavioralStoppedPayoffLawFrom
            (Function.update
              (fun j => behavioralize j (profile j))
              i targetStrategy)
            current fuel =
          G.mixedStoppedPayoffLawFrom
            (Function.update profile i sourceStrategy)
            current fuel

namespace MixedBehavioralContinuationRealization

variable
    {G : ObservedChanceGame N U}
    [Fintype N] [LinearOrder N]
    [(state : G.observed.base.State) →
      Decidable
        (G.observed.base.isTerminal state)]
    {fuel : ℕ}

/-- Map a complete mixed profile through a continuation-wide realization. -/
def mapProfile
    (R : G.MixedBehavioralContinuationRealization fuel)
    (profile : G.observed.MixedProfile) :
    G.observed.BehavioralProfile :=
  fun i => R.behavioralize i (profile i)

/-- Restrict a continuation-wide realization to one root. -/
def atRoot
    (R : G.MixedBehavioralContinuationRealization fuel)
    (current :
      G.observed.base.toArena.HistoryFrom
        G.observed.base.init) :
    G.MixedBehavioralRealizationAt
      current fuel where
  behavioralize :=
    R.behavioralize
  map_payoffLaw :=
    fun profile =>
      FiniteLaw.Equivalent.of_eq
        (R.map_payoffLaw profile current)
  realize_deviation :=
    fun profile i targetStrategy => by
      obtain ⟨sourceStrategy, hsource⟩ :=
        R.realize_deviation
          profile current i targetStrategy
      exact ⟨sourceStrategy,
        FiniteLaw.Equivalent.of_eq hsource⟩

/-- A continuation-wide realization induces a representation-neutral
continuation morphism. -/
def continuationHom
    (R : G.MixedBehavioralContinuationRealization fuel)
    (roots : G.observed.RootPresentation) :
    (G.mixedContinuationFamilyOnRoots roots fuel).Hom
      (G.behavioralContinuationFamilyOnRoots roots fuel) where
  rootMap := id
  strategyMap :=
    R.behavioralize
  outcomeMap := id
  map_declaredRoot := by
    intro current hroot
    exact hroot
  map_outcome := by
    intro current profile
    change
      G.mixedStoppedPayoffLawFrom
          profile current fuel =
        G.behavioralStoppedPayoffLawFrom
          (R.mapProfile profile) current fuel
    exact (R.map_payoffLaw profile current).symm

/-- The identity root map covers every target declared root. -/
theorem continuationHom_declaredRootSurjective
    (R : G.MixedBehavioralContinuationRealization fuel)
    (roots : G.observed.RootPresentation) :
    (R.continuationHom roots).DeclaredRootSurjective := by
  intro targetRoot htargetRoot
  exact ⟨targetRoot, htargetRoot, rfl⟩

/-- The continuation certificate gives rootwise exact semantic deviation
coverage. -/
theorem continuationHom_outcomeDeviationCompleteAt
    (R : G.MixedBehavioralContinuationRealization fuel)
    (roots : G.observed.RootPresentation)
    (profile : G.observed.MixedProfile) :
    (R.continuationHom roots).OutcomeDeviationCompleteAt
      profile := by
  intro current hroot i targetStrategy
  obtain ⟨sourceStrategy, hrealizes⟩ :=
    R.realize_deviation
      profile current i targetStrategy
  refine ⟨sourceStrategy, ?_⟩
  change
    G.behavioralStoppedPayoffLawFrom
        (Function.update
          (R.mapProfile profile)
          i targetStrategy)
        current fuel =
      G.mixedStoppedPayoffLawFrom
        (Function.update profile i sourceStrategy)
        current fuel
  exact hrealizes

/-- A continuation-wide realization preserves and reflects bounded Nash on presentation-designated continuations. -/
theorem isNashOnRootsAtFuel_iff
    [Preorder V]
    (R : G.MixedBehavioralContinuationRealization fuel)
    (roots : G.observed.RootPresentation)
    (utility :
      FiniteLaw (Option (N → U)) → N → V)
    (profile : G.observed.MixedProfile) :
    G.IsMixedNashOnRootsAtFuel
        roots utility profile fuel ↔
      G.IsBehavioralNashOnRootsAtFuel
        roots utility (R.mapProfile profile) fuel := by
  change
    (G.mixedContinuationFamilyOnRoots
      roots fuel).IsNashOnRoots
        (fun _ => utility) profile ↔
      (G.behavioralContinuationFamilyOnRoots
        roots fuel).IsNashOnRoots
          (fun _ => utility)
          ((R.continuationHom roots).mapProfile profile)
  apply
    (R.continuationHom roots).isNashOnRoots_iff_of_outcomeDeviationCompleteAt
      (profile := profile)
  · intro root outcome i
    rfl
  · exact
      R.continuationHom_declaredRootSurjective roots
  · exact
      R.continuationHom_outcomeDeviationCompleteAt roots profile

end MixedBehavioralContinuationRealization

end ExtensiveGame.ObservedChanceGame
