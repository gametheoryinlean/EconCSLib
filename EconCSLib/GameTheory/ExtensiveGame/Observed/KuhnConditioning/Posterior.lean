/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.Math.Probability.FiniteLaw.Conditioning
import EconCSLib.Math.Probability.FiniteLaw.Product
import EconCSLib.GameTheory.ExtensiveGame.Observed.Kuhn

/-!
# EconCSLib.GameTheory.ExtensiveGame.Observed.KuhnConditioning.Posterior

Batch and sequential posterior conditioning of complete pure plans.
-/

namespace ExtensiveGame.ObservedGame

variable {N U : Type*} (G : ObservedGame N U)

namespace PureStrategy

/-- A pure contingent plan agrees with one remembered personal decision. -/
def AgreesWithDecision {i : N}
    (strategy : G.PureStrategy i)
    (decision : G.PersonalDecision i) : Prop :=
  strategy decision.1 = decision.2

/-- A pure contingent plan agrees with every information/action record in a
remembered decision sequence. -/
def AgreesWithDecisions {i : N}
    (strategy : G.PureStrategy i)
    (decisions : List (G.PersonalDecision i)) : Prop :=
  ∀ decision ∈ decisions,
    strategy.AgreesWithDecision G decision

/-- The event of complete pure plans agreeing with a remembered decision
sequence. -/
def agreesWithDecisionsSet {i : N}
    (decisions : List (G.PersonalDecision i)) :
    Set (G.PureStrategy i) :=
  {strategy |
    strategy.AgreesWithDecisions G decisions}

@[simp]
theorem agreesWithDecisions_nil {i : N}
    (strategy : G.PureStrategy i) :
    strategy.AgreesWithDecisions G [] := by
  simp [AgreesWithDecisions]

@[simp]
theorem agreesWithDecisions_cons {i : N}
    (strategy : G.PureStrategy i)
    (decision : G.PersonalDecision i)
    (decisions : List (G.PersonalDecision i)) :
    strategy.AgreesWithDecisions
        G (decision :: decisions) ↔
      strategy.AgreesWithDecision G decision ∧
        strategy.AgreesWithDecisions G decisions := by
  simp [AgreesWithDecisions]

@[simp]
theorem agreesWithDecisions_append {i : N}
    (strategy : G.PureStrategy i)
    (first second :
      List (G.PersonalDecision i)) :
    strategy.AgreesWithDecisions
        G (first ++ second) ↔
      strategy.AgreesWithDecisions G first ∧
        strategy.AgreesWithDecisions G second := by
  constructor
  · intro hagrees
    constructor
    · intro decision hmem
      exact
        hagrees decision
          (List.mem_append_left second hmem)
    · intro decision hmem
      exact
        hagrees decision
          (List.mem_append_right first hmem)
  · rintro ⟨hfirst, hsecond⟩ decision hmem
    rcases List.mem_append.mp hmem with
      hmem | hmem
    · exact hfirst decision hmem
    · exact hsecond decision hmem

@[simp]
theorem mem_agreesWithDecisionsSet {i : N}
    (strategy : G.PureStrategy i)
    (decisions : List (G.PersonalDecision i)) :
    strategy ∈ agreesWithDecisionsSet G decisions ↔
      strategy.AgreesWithDecisions G decisions :=
  Iff.rfl

end PureStrategy

namespace MixedStrategy

/-- A remembered decision sequence has positive probability under a mixed
plan when some supported pure plan agrees with every recorded decision. -/
def DecisionsPossible {i : N}
    (strategy : G.MixedStrategy i)
    (decisions : List (G.PersonalDecision i)) : Prop :=
  ∃ pureStrategy,
    strategy.HasPositiveAtom pureStrategy ∧
      pureStrategy.AgreesWithDecisions G decisions

/-- Normalize a mixed plan on the event that it agrees with a remembered
decision sequence.  A zero-mass event has no posterior. -/
def conditionOnDecisions {i : N}
    [∀ information : G.RepresentedInfo i,
      DecidableEq (G.InfoAction i information.1)]
    (strategy : G.MixedStrategy i)
    (decisions : List (G.PersonalDecision i)) :
    Option (G.MixedStrategy i) :=
  if decisions.isEmpty then
      some strategy
    else
      strategy.conditionOnFiber
        (fun pureStrategy =>
          decisions.all fun decision =>
            decide (pureStrategy decision.1 = decision.2))
        true

/-- The empty decision sequence is possible under every mixed plan. -/
theorem decisionsPossible_nil {i : N}
    (strategy : G.MixedStrategy i) :
    strategy.DecisionsPossible G [] := by
  obtain ⟨pureStrategy, hsupported⟩ :=
    strategy.exists_hasPositiveAtom
  exact ⟨pureStrategy, hsupported, by simp⟩

/-- Conditioning on the empty decision sequence changes no mixed plan. -/
theorem conditionOnDecisions_nil {i : N}
    [∀ information : G.RepresentedInfo i,
      DecidableEq (G.InfoAction i information.1)]
    (strategy : G.MixedStrategy i) :
    strategy.conditionOnDecisions
        G [] =
      some strategy := by
  simp [conditionOnDecisions]

/-- The action law of a mixed plan after conditioning on the recorded own
decisions.  A zero-mass record sequence has no conditional action law. -/
def conditionalActionLaw {i : N}
    [∀ information : G.RepresentedInfo i,
      DecidableEq (G.InfoAction i information.1)]
    (strategy : G.MixedStrategy i)
    (decisions : List (G.PersonalDecision i))
    (information : G.RepresentedInfo i) :
    Option (FiniteLaw (G.InfoAction i information.1)) :=
  (strategy.conditionOnDecisions G decisions).map
    (fun conditioned =>
      conditioned.map fun pureStrategy =>
        pureStrategy information)

/-- A successfully computed consistency posterior maps to its declared action
marginal. -/
theorem conditionalActionLaw_of_possible
    {i : N}
    [∀ information : G.RepresentedInfo i,
      DecidableEq (G.InfoAction i information.1)]
    (strategy : G.MixedStrategy i)
    (decisions : List (G.PersonalDecision i))
    (information : G.RepresentedInfo i)
    (conditioned : G.MixedStrategy i)
    (hconditioned :
      strategy.conditionOnDecisions G decisions = some conditioned) :
    strategy.conditionalActionLaw
        G decisions information =
      some (conditioned.map fun pureStrategy =>
        pureStrategy information) := by
  simp [conditionalActionLaw, hconditioned]

/-- A zero-mass consistency event has no conditional action law. -/
theorem conditionalActionLaw_of_impossible
    {i : N}
    [∀ information : G.RepresentedInfo i,
      DecidableEq (G.InfoAction i information.1)]
    (strategy : G.MixedStrategy i)
    (decisions : List (G.PersonalDecision i))
    (information : G.RepresentedInfo i)
    (himpossible :
      strategy.conditionOnDecisions G decisions = none) :
    strategy.conditionalActionLaw
        G decisions information =
      none := by
  simp [conditionalActionLaw, himpossible]

/-- With no prior continuation-local decisions, conditional
behavioralization is exactly the ordinary mixed action marginal. -/
theorem conditionalActionLaw_nil
    {i : N}
    [∀ information : G.RepresentedInfo i,
      DecidableEq (G.InfoAction i information.1)]
    (strategy : G.MixedStrategy i)
    (information : G.RepresentedInfo i) :
    strategy.conditionalActionLaw
        G [] information =
      some (strategy.map fun pureStrategy =>
        pureStrategy information) := by
  simp [conditionalActionLaw, conditionOnDecisions]

/-- Posterior mixed-plan law obtained by exposing a chronological sequence of
the player's own decisions one at a time.

Sequential conditioning is definitionally suited to execution induction: when
one more decision is observed, the current posterior is conditioned on one
additional evaluation fiber.  A zero-mass prefix stops the computation with
`none`. -/
def posteriorAfterDecisions {i : N}
    [∀ information : G.RepresentedInfo i,
      DecidableEq (G.InfoAction i information.1)]
    (strategy : G.MixedStrategy i)
    (decisions : List (G.PersonalDecision i)) :
    Option (G.MixedStrategy i) :=
  decisions.foldlM
    (fun posterior decision =>
      posterior.conditionOnFiber
        (fun pureStrategy =>
          pureStrategy decision.1)
        decision.2)
    strategy

private theorem posteriorAfterDecisions_congr {i : N}
    [∀ information : G.RepresentedInfo i,
      DecidableEq (G.InfoAction i information.1)]
    [DecidableEq (G.PureStrategy i)]
    {left right : G.MixedStrategy i}
    (h : left.Equivalent right)
    (decisions : List (G.PersonalDecision i)) :
    Option.Rel FiniteLaw.Equivalent
      (left.posteriorAfterDecisions G decisions)
      (right.posteriorAfterDecisions G decisions) := by
  induction decisions generalizing left right with
  | nil => exact Option.Rel.some h
  | cons decision decisions ih =>
      simp only [posteriorAfterDecisions, List.foldlM_cons]
      have hstep := h.conditionOnFiber
        (fun pureStrategy => pureStrategy decision.1) decision.2
      cases hleft : left.conditionOnFiber
          (fun pureStrategy => pureStrategy decision.1) decision.2 with
      | none =>
          cases hright : right.conditionOnFiber
              (fun pureStrategy => pureStrategy decision.1) decision.2 with
          | none =>
              exact Option.Rel.none
          | some rightConditioned =>
              rw [hleft, hright] at hstep
              cases hstep
      | some leftConditioned =>
          cases hright : right.conditionOnFiber
              (fun pureStrategy => pureStrategy decision.1) decision.2 with
          | none =>
              rw [hleft, hright] at hstep
              cases hstep
          | some rightConditioned =>
              rw [hleft, hright] at hstep
              cases hstep with
              | some hconditioned =>
                  simpa [hleft, hright] using ih hconditioned

private theorem optionEquivalent_trans {i : N}
    {first second third : Option (G.MixedStrategy i)}
    (hfirst : Option.Rel FiniteLaw.Equivalent first second)
    (hsecond : Option.Rel FiniteLaw.Equivalent second third) :
    Option.Rel FiniteLaw.Equivalent first third := by
  cases hfirst with
  | none =>
      cases hsecond
      exact Option.Rel.none
  | some hleft =>
      cases hsecond with
      | some hright =>
          exact Option.Rel.some (hleft.trans hright)

@[simp]
theorem posteriorAfterDecisions_nil {i : N}
    [∀ information : G.RepresentedInfo i,
      DecidableEq (G.InfoAction i information.1)]
    (strategy : G.MixedStrategy i) :
    strategy.posteriorAfterDecisions G [] =
      some strategy := by
  simp [posteriorAfterDecisions]

/-- Appending one remembered decision performs exactly one additional
posterior-fiber update. -/
theorem posteriorAfterDecisions_append_singleton
    {i : N}
    [∀ information : G.RepresentedInfo i,
      DecidableEq (G.InfoAction i information.1)]
    (strategy : G.MixedStrategy i)
    (decisions : List (G.PersonalDecision i))
    (decision : G.PersonalDecision i) :
    strategy.posteriorAfterDecisions
        G (decisions ++ [decision]) =
      (strategy.posteriorAfterDecisions G decisions).bind
        (fun posterior =>
          posterior.conditionOnFiber
            (fun pureStrategy =>
              pureStrategy decision.1)
            decision.2) := by
  simp [posteriorAfterDecisions]

/-- Current action marginal of the sequential posterior after a remembered
decision sequence. -/
def sequentialConditionalActionLaw
    {i : N}
    [∀ information : G.RepresentedInfo i,
      DecidableEq (G.InfoAction i information.1)]
    (strategy : G.MixedStrategy i)
    (decisions : List (G.PersonalDecision i))
    (information : G.RepresentedInfo i) :
    Option (FiniteLaw (G.InfoAction i information.1)) :=
  (strategy.posteriorAfterDecisions
    G decisions).map fun posterior =>
      posterior.map fun pureStrategy =>
        pureStrategy information

@[simp]
theorem sequentialConditionalActionLaw_nil
    {i : N}
    [∀ information : G.RepresentedInfo i,
      DecidableEq (G.InfoAction i information.1)]
    (strategy : G.MixedStrategy i)
    (information : G.RepresentedInfo i) :
    strategy.sequentialConditionalActionLaw
        G [] information =
      some (strategy.map fun pureStrategy =>
        pureStrategy information) := by
  simp [sequentialConditionalActionLaw, posteriorAfterDecisions]

end MixedStrategy

namespace BehavioralStrategy

/-- Coordinate-law family remaining after sequentially exposing a list of
personal decisions from an independently sampled behavioral table. -/
def actionLawsAfterDecisions
    {i : N}
    [DecidableEq (G.RepresentedInfo i)]
    [∀ information : G.RepresentedInfo i,
      DecidableEq (G.InfoAction i information.1)]
    (strategy : G.BehavioralStrategy i)
    (decisions : List (G.PersonalDecision i)) :
    Option (G.BehavioralStrategy i) :=
  decisions.foldlM
    (fun laws decision =>
      ((laws decision.1).conditionOnFiber id decision.2).map
        (fun conditioned =>
          Function.update laws decision.1 conditioned))
    strategy

/-- Sequentially conditioning the complete independently sampled table is
again an independent table with the exposed coordinate laws updated one at a
time. -/
theorem toMixed_posteriorAfterDecisions
    {i : N}
    [representedFintype : Fintype (G.RepresentedInfo i)]
    [representedOrder : LinearOrder (G.RepresentedInfo i)]
    [actionDecidable : ∀ information : G.RepresentedInfo i,
      DecidableEq (G.InfoAction i information.1)]
    (strategy : G.BehavioralStrategy i)
    (decisions : List (G.PersonalDecision i)) :
    Option.Rel FiniteLaw.Equivalent
      ((strategy.toMixed G).posteriorAfterDecisions
        G decisions)
      ((strategy.actionLawsAfterDecisions
        G decisions).map FiniteLaw.fintypePi) := by
  letI : DecidableEq (G.PureStrategy i) :=
    Fintype.decidablePiFintype
  induction decisions generalizing strategy with
  | nil =>
      exact Option.Rel.some (FiniteLaw.Equivalent.refl _)
  | cons decision decisions ih =>
      let productLaw : G.MixedStrategy i :=
        @FiniteLaw.fintypePi
          (G.RepresentedInfo i)
          representedFintype representedOrder
          (fun information => G.InfoAction i information.1)
          strategy
      rw [show strategy.toMixed G =
        productLaw from rfl]
      have hproduct :=
        @FiniteLaw.fintypePi_conditionOnFiber_apply
          (G.RepresentedInfo i)
          representedFintype representedOrder
          (fun information => G.InfoAction i information.1)
          actionDecidable this
          strategy decision.1 decision.2
      change Option.Rel FiniteLaw.Equivalent
        ((FiniteLaw.fintypePi strategy).conditionOnFiber
          (fun pureStrategy => pureStrategy decision.1) decision.2)
        _ at hproduct
      have hstepEq :
          @FiniteLaw.conditionOnFiber
              (G.InfoAction i decision.1.1)
              (G.PureStrategy i)
              (actionDecidable decision.1)
              productLaw
              (fun pureStrategy => pureStrategy decision.1)
              decision.2 =
            (FiniteLaw.fintypePi strategy).conditionOnFiber
              (fun pureStrategy => pureStrategy decision.1)
              decision.2 := by
        dsimp only [productLaw]
        exact FiniteLaw.conditionOnFiber_decidableEq_irrel _ _ _ _ _
      rw [← hstepEq] at hproduct
      cases hcoordinate :
          @FiniteLaw.conditionOnFiber
            (G.InfoAction i decision.1.1)
            (G.InfoAction i decision.1.1)
            (actionDecidable decision.1)
            (strategy decision.1) id decision.2 with
      | none =>
          cases hproductConditioned :
              @FiniteLaw.conditionOnFiber
                (G.InfoAction i decision.1.1)
                (G.PureStrategy i)
                (actionDecidable decision.1)
                productLaw
                (fun pureStrategy => pureStrategy decision.1)
                decision.2 with
          | none =>
              simp [MixedStrategy.posteriorAfterDecisions,
                actionLawsAfterDecisions, hcoordinate,
                hproductConditioned]
          | some productConditioned =>
              rw [hcoordinate, hproductConditioned] at hproduct
              cases hproduct
      | some conditioned =>
          cases hproductConditioned :
              @FiniteLaw.conditionOnFiber
                (G.InfoAction i decision.1.1)
                (G.PureStrategy i)
                (actionDecidable decision.1)
                productLaw
                (fun pureStrategy => pureStrategy decision.1)
                decision.2 with
          | none =>
              rw [hcoordinate, hproductConditioned] at hproduct
              cases hproduct
          | some productConditioned =>
              rw [hcoordinate, hproductConditioned] at hproduct
              cases hproduct with
              | some hconditioned =>
                  have hcongr :=
                    MixedStrategy.posteriorAfterDecisions_congr
                      G hconditioned decisions
                  have htail :=
                    ih (strategy :=
                      Function.update strategy decision.1 conditioned)
                  have htrans :=
                    MixedStrategy.optionEquivalent_trans G hcongr htail
                  simp only [MixedStrategy.posteriorAfterDecisions,
                    actionLawsAfterDecisions, List.foldlM_cons]
                  rw [hproductConditioned, hcoordinate]
                  simpa using htrans

/-- Exposing decisions at other information states leaves the current
coordinate law unchanged. -/
theorem actionLawsAfterDecisions_apply_of_ne
    {i : N}
    [DecidableEq (G.RepresentedInfo i)]
    [∀ information : G.RepresentedInfo i,
      DecidableEq (G.InfoAction i information.1)]
    (strategy : G.BehavioralStrategy i)
    (decisions : List (G.PersonalDecision i))
    (information : G.RepresentedInfo i)
    (laws : G.BehavioralStrategy i)
    (hlaws :
      strategy.actionLawsAfterDecisions G decisions = some laws)
    (hdistinct :
      ∀ decision ∈ decisions,
        decision.1 ≠ information) :
    laws information =
      strategy information := by
  induction decisions generalizing strategy laws with
  | nil =>
      simp [actionLawsAfterDecisions] at hlaws
      subst laws
      rfl
  | cons decision decisions ih =>
      simp only [actionLawsAfterDecisions,
        List.foldlM_cons] at hlaws
      cases hcondition :
          (strategy decision.1).conditionOnFiber id decision.2 with
      | none =>
          simp [hcondition] at hlaws
      | some conditioned =>
          simp only [hcondition, Option.map_some] at hlaws
          have htail :=
            ih
              (strategy :=
                Function.update strategy decision.1 conditioned)
              (laws := laws)
              hlaws
              (by
                intro later hlater
                exact hdistinct later (by simp [hlater]))
          rw [htail]
          exact Function.update_of_ne
            (hdistinct decision (by simp)).symm conditioned strategy

/-- The posterior independently sampled table retains the original action
marginal at every information state not listed among the exposed prior
decisions. -/
theorem toMixed_posteriorAfterDecisions_actionMarginal
    {i : N}
    [Fintype (G.RepresentedInfo i)] [LinearOrder (G.RepresentedInfo i)]
    [∀ information : G.RepresentedInfo i,
      DecidableEq (G.InfoAction i information.1)]
    (strategy : G.BehavioralStrategy i)
    (decisions : List (G.PersonalDecision i))
    (information : G.RepresentedInfo i)
    (posterior : G.MixedStrategy i)
    (hposterior :
      (strategy.toMixed G).posteriorAfterDecisions G decisions =
        some posterior)
    (hdistinct :
      ∀ decision ∈ decisions,
        decision.1 ≠ information) :
    (posterior.map
        (fun pureStrategy => pureStrategy information)).Equivalent
      (strategy information) := by
  classical
  have hrelation :=
    strategy.toMixed_posteriorAfterDecisions G decisions
  rw [hposterior] at hrelation
  cases hlaws : strategy.actionLawsAfterDecisions G decisions with
  | none =>
      rw [hlaws] at hrelation
      cases hrelation
  | some laws =>
      rw [hlaws] at hrelation
      cases hrelation with
      | some hequivalent =>
          exact
            (hequivalent.map
              (fun pureStrategy => pureStrategy information)).trans
              ((FiniteLaw.fintypePi_map_apply laws information).trans
                (FiniteLaw.Equivalent.of_eq
                  (strategy.actionLawsAfterDecisions_apply_of_ne
                    G decisions information laws hlaws hdistinct)))

end BehavioralStrategy

/-- One chronological personal-decision sequence for every player. -/
abbrev PersonalDecisionHistories :=
  (i : N) → List (G.PersonalDecision i)

/-- The own-decision sequences accumulated after a selected continuation
root, extracted from a later complete history. -/
def relativeOwnDecisionHistories
    [DecidableEq N]
    (root current :
      G.base.toArena.HistoryFrom G.base.init) :
    G.PersonalDecisionHistories :=
  fun i =>
    (G.ownDecisionHistory i current).drop
      (G.ownDecisionHistory i root).length

@[simp]
theorem relativeOwnDecisionHistories_self
    [DecidableEq N]
    (current :
      G.base.toArena.HistoryFrom G.base.init)
    (i : N) :
    G.relativeOwnDecisionHistories
        current current i =
      [] := by
  simp [relativeOwnDecisionHistories]

/-- A chance or another player's move leaves player `i`'s
continuation-relative own-decision sequence unchanged. -/
theorem relativeOwnDecisionHistories_snoc_of_not_mover
    [DecidableEq N]
    (root :
      G.base.toArena.HistoryFrom G.base.init)
    {state : G.base.State}
    (suffix :
      G.base.toArena.History root.1 state)
    (action : G.base.Action state)
    (i : N)
    (hmover :
      G.base.mover state ≠ some i) :
    G.relativeOwnDecisionHistories
        root
        ⟨G.base.next state action,
          root.2.append (suffix.snoc action)⟩
        i =
      G.relativeOwnDecisionHistories
        root
        ⟨state, root.2.append suffix⟩
        i := by
  unfold relativeOwnDecisionHistories
  rw [Arena.History.append_snoc]
  rw [G.ownDecisionHistory_snoc_of_not_mover
    i (root.2.append suffix) action hmover]

/-- A player's move appends exactly its current information/action record to
that player's continuation-relative sequence. -/
theorem relativeOwnDecisionHistories_snoc_of_mover
    [DecidableEq N]
    (root :
      G.base.toArena.HistoryFrom G.base.init)
    {state : G.base.State}
    (suffix :
      G.base.toArena.History root.1 state)
    (action : G.base.Action state)
    (i : N)
    (hmover :
      G.base.mover state = some i) :
    G.relativeOwnDecisionHistories
        root
        ⟨G.base.next state action,
          root.2.append (suffix.snoc action)⟩
        i =
      G.relativeOwnDecisionHistories
          root
          ⟨state, root.2.append suffix⟩
          i ++
        [G.personalDecisionAt
          i ⟨state, root.2.append suffix⟩
          hmover action] := by
  have hprefix :=
    G.ownDecisionHistory_prefix_append
      i root.2 suffix
  have hlength :
      (G.ownDecisionHistory i root).length ≤
        (G.ownDecisionHistory i
          ⟨state, root.2.append suffix⟩).length :=
    List.IsPrefix.length_le hprefix
  unfold relativeOwnDecisionHistories
  rw [Arena.History.append_snoc]
  rw [G.ownDecisionHistory_snoc_of_mover
    i (root.2.append suffix) action hmover]
  rw [List.drop_append_of_le_length hlength]

/-- No absent-mindedness also separates the current information state from
every decision in the continuation-relative suffix. -/
theorem HasNoAbsentMindedness.info_ne_of_mem_relativeOwnDecisionHistories
    [DecidableEq N]
    {i : N}
    (hnoAbsent : G.HasNoAbsentMindedness i)
    (root current :
      G.base.toArena.HistoryFrom G.base.init)
    (hmover :
      G.base.mover current.1 = some i)
    (hnonterminal :
      ¬ G.base.isTerminal current.1)
    (decision : G.PersonalDecision i)
    (hmem :
      decision ∈
        G.relativeOwnDecisionHistories
          root current i) :
    decision.1 ≠
      G.representedInfoAt current i hmover
        (G.base.toArena.isDecision_of_not_isTerminal _
          hnonterminal) := by
  apply
    hnoAbsent.info_ne_of_mem_ownDecisionHistory
      current hmover
        (G.base.toArena.isDecision_of_not_isTerminal _
          hnonterminal)
      decision
  exact
    (List.drop_sublist
      (G.ownDecisionHistory i root).length
      (G.ownDecisionHistory i current)).subset
        hmem


end ExtensiveGame.ObservedGame
