/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Compat.Infrastructure

/-!
# Recall-hierarchy regressions

Two small games separate the external recall predicates.

* `ForgetOthers` has classic perfect recall: neither player has made a prior
  decision at their current decision information. Player `0` nevertheless
  forgets a transient private signal revealing player `1`'s earlier action,
  so signal recall fails.
* `ForgetOwn` retains only the decision stage. At the second decision it
  forgets which Boolean action it chose at the first decision. Classic
  perfect recall fails although the information states are not repeated, so
  this is distinct from absent-mindedness.
* Payoff-free variants make the public/private boundaries explicit:
  classic or private-signal recall need not imply public recall, while public
  recall need imply neither private-signal nor classic recall.

The absent-minded regression itself remains in `AbsentMinded.lean`.
-/

namespace Examples.RecallHierarchy

open ExtensiveGame

namespace ForgetOthers

/-- Player `1` chooses a bit, nature advances one administrative step, and
player `0` then acts. -/
inductive State
  | root
  | signal (bit : Bool)
  | decision (bit : Bool)
  | terminal (bit : Bool)

def Action : State → Type
  | .root => Bool
  | .signal _ => Unit
  | .decision _ => Unit
  | .terminal _ => Empty

def next : (state : State) → Action state → State
  | .root, bit => .signal bit
  | .signal bit, _ => .decision bit
  | .decision bit, _ => .terminal bit

def base : ExtensiveGame (Fin 2) Unit where
  State := State
  Action := Action
  next := next
  init := .root
  mover
    | .root => some 1
    | .signal _ => none
    | .decision _ => some 0
    | .terminal _ => none
  payoff := fun _ _ => ()

/-- Player `0` sees the bit only at the intermediate signal state. -/
def privateObserve (i : Fin 2)
    (history : base.toArena.HistoryFrom base.init) : Bool :=
  if i = 0 then
    match history.1 with
    | .signal bit => bit
    | _ => false
  else
    false

/-- Decision information remembers only which player's unique decision stage
is current, not player `0`'s earlier transient signal. -/
def game : ObservedGame (Fin 2) Unit where
  base := base
  Observation := fun _ => Bool
  PublicObservation := Unit
  observe := privateObserve
  publicObserve := fun _ => ()
  publicOf := fun _ _ => ()
  observe_public := by simp
  InfoState := fun _ => Unit
  infoObserve := fun _ _ => false
  infoAt := fun _ _ _ _ => ()
  infoAt_observe := by
    intro history i hmover _hnonterminal
    generalize hstate : history.1 = state at hmover ⊢
    cases state with
    | root =>
        have hi : i = 1 := by
          exact (Option.some.inj hmover).symm
        subst i
        simp [privateObserve]
    | signal bit =>
        simp [base] at hmover
    | decision bit =>
        have hi : i = 0 := by
          exact (Option.some.inj hmover).symm
        subst i
        simp [privateObserve, hstate]
    | terminal bit =>
        simp [base] at hmover
  InfoAction := fun i _ =>
    if i = 0 then Unit else Bool
  actionEquiv := by
    intro history i hmover _hnonterminal
    generalize hstate : history.1 = state at hmover ⊢
    cases state with
    | root =>
        have hi : i = 1 := by
          exact (Option.some.inj hmover).symm
        subst i
        exact Equiv.refl Bool
    | signal bit =>
        simp [base] at hmover
    | decision bit =>
        have hi : i = 0 := by
          exact (Option.some.inj hmover).symm
        subst i
        exact Equiv.refl Unit
    | terminal bit =>
        simp [base] at hmover

def initial :
    base.toArena.HistoryFrom base.init :=
  Arena.HistoryFrom.nil base.toArena base.init

def afterChoice (bit : Bool) :
    base.toArena.HistoryFrom base.init :=
  ⟨.signal bit, initial.2.snoc bit⟩

def atDecision (bit : Bool) :
    base.toArena.HistoryFrom base.init :=
  ⟨.decision bit, (afterChoice bit).2.snoc ()⟩

/-- Decision histories have a legal unit action and hence are nonterminal. -/
theorem atDecision_nonterminal (bit : Bool) :
    ¬ base.isTerminal (atDecision bit).1 :=
  fun hterminal => hterminal.false ()

theorem atDecision_decision (bit : Bool) :
    base.toArena.IsDecision (atDecision bit).1 :=
  base.toArena.isDecision_of_not_isTerminal _
    (atDecision_nonterminal bit)

@[simp]
theorem signalHistory_false :
    game.signalHistory 0 (atDecision false) =
      [false, false, false] :=
  rfl

@[simp]
theorem signalHistory_true :
    game.signalHistory 0 (atDecision true) =
      [false, true, false] :=
  rfl

/-- Player `0`'s two current information states coincide although the
transient signal histories differ. -/
theorem not_hasEventClockSignalPerfectRecall :
    ¬ game.HasEventClockSignalPerfectRecall 0 := by
  intro hrecall
  have heq :=
    hrecall
      (atDecision false) (atDecision true)
      rfl (atDecision_decision false)
      rfl (atDecision_decision true) rfl
  have hmiddle :=
    congrArg (fun signals => signals[1]?) heq
  change some false = some true at hmiddle
  exact Bool.noConfusion (Option.some.inj hmiddle)

/-- Neither player's current decision has an earlier decision by that same
player, so classic own-action recall holds despite forgotten transient
signals. -/
def classicRecallCertificate :
    game.RecallCertificate where
  remembered := fun _ _ => []
  remembered_infoAt := by
    intro i history hmover _hnonterminal
    rcases history with ⟨state, path⟩
    cases path with
    | nil =>
        rfl
    | @snoc previous path action =>
        cases path with
        | nil =>
            change
              (none : Option (Fin 2)) = some i
              at hmover
            simp at hmover
        | @snoc previous' path action' =>
            cases path with
            | nil =>
                cases action'
                <;> cases action
                <;>
                  change
                    (some 0 : Option (Fin 2)) = some i
                    at hmover
                <;>
                  have hi : i = 0 :=
                    (Option.some.inj hmover).symm
                <;> subst i
                <;>
                  simp [ControlledObservedGame.ownDecisionHistory,
                    ControlledObservedGame.ownDecisionHistoryPath,
                    game, base, next]
            | @snoc previous'' path action'' =>
                cases previous'' with
                | root =>
                    cases action'' <;>
                      cases action' <;>
                      cases action <;>
                      change
                        (none : Option (Fin 2)) = some i
                        at hmover <;>
                      simp at hmover
                | signal bit =>
                    cases action''
                    cases action'
                    exact action.elim
                | decision bit =>
                    cases action''
                    exact action'.elim
                | terminal bit =>
                    exact action''.elim

/-- Classic perfect recall does not imply signal recall. -/
theorem perfectRecall :
    game.PerfectRecall :=
  classicRecallCertificate.perfectRecall

/-- The payoff-free projection has classic recall. -/
theorem controlledPerfectRecall :
    game.toControlledObservedGame.PerfectRecall :=
  fun i =>
    (game.hasPerfectRecall_iff_toControlled i).mp
      (perfectRecall i)

/-- Constant public observations forget elapsed public time, so classic
recall does not imply public recall even on the payoff-free projection. -/
theorem controlled_not_hasEventClockPublicPerfectRecall :
    ¬ game.toControlledObservedGame.HasEventClockPublicPerfectRecall := by
  intro hrecall
  have heq := hrecall initial (afterChoice false) rfl
  change [()] = [(), ()] at heq
  simp at heq

/-- The public stage of the four-layer tree. -/
inductive PublicStage
  | root
  | signal
  | decision
  | terminal
  deriving DecidableEq

/-- Forget the chosen bit and retain only the public stage. -/
def publicStage : State → PublicStage
  | .root => .root
  | .signal _ => .signal
  | .decision _ => .decision
  | .terminal _ => .terminal

/-- A payoff-free presentation whose public signal records time while player
`0`'s private signal still transiently reveals player `1`'s action. -/
def publicRecallGame : ControlledObservedGame (Fin 2) where
  base := base.toControlledGame
  Observation := fun _ => PublicStage × Bool
  PublicObservation := PublicStage
  observe := fun i history =>
    (publicStage history.1, privateObserve i history)
  publicObserve := fun history => publicStage history.1
  publicOf := fun _ observation => observation.1
  observe_public := by simp
  InfoState := fun _ => Unit
  infoObserve := fun i _ =>
    if i = 0 then (.decision, false) else (.root, false)
  infoAt := fun _ _ _ _ => ()
  infoAt_observe := by
    intro history i hmover _hnonterminal
    generalize hstate : history.1 = state at hmover ⊢
    cases state with
    | root =>
        have hi : i = 1 := by
          exact (Option.some.inj hmover).symm
        subst i
        simp [privateObserve, publicStage]
    | signal bit =>
        simp [base] at hmover
    | decision bit =>
        have hi : i = 0 := by
          exact (Option.some.inj hmover).symm
        subst i
        simp [privateObserve, publicStage, hstate]
    | terminal bit =>
        simp [base] at hmover
  InfoAction := fun i _ =>
    if i = 0 then Unit else Bool
  actionEquiv := by
    intro history i hmover _hnonterminal
    generalize hstate : history.1 = state at hmover ⊢
    cases state with
    | root =>
        have hi : i = 1 := by
          exact (Option.some.inj hmover).symm
        subst i
        exact Equiv.refl Bool
    | signal bit =>
        simp [base] at hmover
    | decision bit =>
        have hi : i = 0 := by
          exact (Option.some.inj hmover).symm
        subst i
        exact Equiv.refl Unit
    | terminal bit =>
        simp [base] at hmover

/-- The public stage determines the complete public-stage sequence. -/
def publicRecallCertificate :
    publicRecallGame.PublicRecallCertificate where
  rememberedPublicSignals
    | .root => [.root]
    | .signal => [.root, .signal]
    | .decision => [.root, .signal, .decision]
    | .terminal => [.root, .signal, .decision, .terminal]
  rememberedPublicSignals_publicObserve := by
    intro history
    rcases history with ⟨state, path⟩
    induction path with
    | nil =>
        rfl
    | @snoc state path action ih =>
        cases state with
        | root =>
            cases action <;>
              simpa [publicRecallGame, publicStage, next,
                ControlledObservedGame.publicSignalHistory,
                ControlledObservedGame.publicSignalHistoryPath] using
                  congrArg
                    (fun signals =>
                      signals ++ [PublicStage.signal])
                    ih
        | signal bit =>
            cases action
            simpa [publicRecallGame, publicStage, next,
              ControlledObservedGame.publicSignalHistory,
              ControlledObservedGame.publicSignalHistoryPath] using
                congrArg
                  (fun signals =>
                    signals ++ [PublicStage.decision])
                  ih
        | decision bit =>
            cases action
            simpa [publicRecallGame, publicStage, next,
              ControlledObservedGame.publicSignalHistory,
              ControlledObservedGame.publicSignalHistoryPath] using
                congrArg
                  (fun signals =>
                    signals ++ [PublicStage.terminal])
                  ih
        | terminal bit =>
            exact action.elim

/-- Public recall holds in the payoff-free staged presentation. -/
theorem publicPerfectRecall :
    publicRecallGame.HasEventClockPublicPerfectRecall :=
  publicRecallCertificate.hasEventClockPublicPerfectRecall

/-- Even with public recall, player `0` forgets the transient private bit. -/
theorem publicRecallGame_not_hasEventClockSignalPerfectRecall :
    ¬ publicRecallGame.HasEventClockSignalPerfectRecall 0 := by
  intro hrecall
  have heq :=
    hrecall
      (atDecision false) (atDecision true)
      rfl (atDecision_decision false)
      rfl (atDecision_decision true) rfl
  have hmiddle :=
    congrArg (fun signals => signals[1]?) heq
  change
    some (PublicStage.signal, false) =
      some (PublicStage.signal, true) at hmiddle
  exact Bool.noConfusion
    (congrArg (fun signal => signal.map Prod.snd) hmiddle
      |> Option.some.inj)

end ForgetOthers

namespace ForgetOwn

/-- One player chooses a Boolean and later moves again. -/
inductive State
  | root
  | second (first : Bool)
  | terminal (first : Bool)

def Action : State → Type
  | .root => Bool
  | .second _ => Unit
  | .terminal _ => Empty

def next : (state : State) → Action state → State
  | .root, first => .second first
  | .second first, _ => .terminal first

def base : ExtensiveGame Unit Unit where
  State := State
  Action := Action
  next := next
  init := .root
  mover
    | .root => some ()
    | .second _ => some ()
    | .terminal _ => none
  payoff := fun _ _ => ()

/-- The current decision stage, which deliberately does not remember the
Boolean selected at the first stage. -/
inductive Stage
  | first
  | second
  deriving DecidableEq

def StageAction : Stage → Type
  | .first => Bool
  | .second => Unit

def game : ObservedGame Unit Unit where
  base := base
  Observation := fun _ => Unit
  PublicObservation := Unit
  observe := fun _ _ => ()
  publicObserve := fun _ => ()
  publicOf := fun _ _ => ()
  observe_public := by simp
  InfoState := fun _ => Stage
  infoObserve := fun _ _ => ()
  infoAt := by
    intro history _i hmover _hnonterminal
    generalize hstate : history.1 = state at hmover
    cases state with
    | root => exact .first
    | second first => exact .second
    | terminal first => simp [base] at hmover
  infoAt_observe := by simp
  InfoAction := fun _ stage => StageAction stage
  actionEquiv := by
    intro history _i hmover _hnonterminal
    generalize hstate : history.1 = state at hmover ⊢
    cases state with
    | root =>
        exact Equiv.refl Bool
    | second first =>
        exact Equiv.refl Unit
    | terminal first =>
        simp [base] at hmover

def initial :
    base.toArena.HistoryFrom base.init :=
  Arena.HistoryFrom.nil base.toArena base.init

def atSecond (first : Bool) :
    base.toArena.HistoryFrom base.init :=
  ⟨.second first, initial.2.snoc first⟩

/-- Second-stage decision histories have a legal unit action and hence are
nonterminal. -/
theorem atSecond_nonterminal (first : Bool) :
    ¬ base.isTerminal (atSecond first).1 :=
  fun hterminal => hterminal.false ()

theorem atSecond_decision (first : Bool) :
    base.toArena.IsDecision (atSecond first).1 :=
  base.toArena.isDecision_of_not_isTerminal _
    (atSecond_nonterminal first)

@[simp]
theorem infoAt_second (first : Bool) :
    game.infoAt (atSecond first) () rfl
        (atSecond_decision first) =
      Stage.second :=
  rfl

/-- The first action is present in the classic remembered own-decision
sequence. -/
theorem ownDecisionHistory_false_ne_true :
    game.ownDecisionHistory () (atSecond false) ≠
      game.ownDecisionHistory () (atSecond true) := by
  intro heq
  change
    [game.personalDecisionAt () initial rfl false] =
      [game.personalDecisionAt () initial rfl true] at heq
  injection heq with hchoice
  have :=
    congrArg
      (fun decision =>
        match decision with
        | ⟨⟨Stage.first, _⟩, choice⟩ => choice
        | ⟨⟨Stage.second, _⟩, _⟩ => false)
      hchoice
  change false = true at this
  exact Bool.noConfusion this

/-- Forgetting one's own first action violates classic perfect recall even
though the current decision stage is remembered. -/
theorem not_hasPerfectRecall :
    ¬ game.HasPerfectRecall () := by
  intro hrecall
  exact ownDecisionHistory_false_ne_true
    (hrecall
      (atSecond false) (atSecond true)
      rfl (atSecond_decision false)
      rfl (atSecond_decision true) rfl)

/-- The private-signal sequence factors through the remembered decision
stage, even though the first chosen action does not. -/
def signalRecallCertificate :
    game.SignalRecallCertificate where
  rememberedSignals := fun _ stage =>
    match stage.1 with
    | .first => [()]
    | .second => [(), ()]
  rememberedSignals_infoAt := by
    intro i history hmover _hnonterminal
    rcases i with ⟨⟩
    rcases history with ⟨state, path⟩
    cases path with
    | nil =>
        rfl
    | @snoc previous path action =>
        cases path with
        | nil =>
            rfl
        | @snoc previous' path action' =>
            cases previous' with
            | root =>
                cases action' <;>
                  cases action <;>
                  simp [game, base, next] at hmover
            | second first =>
                cases action'
                exact action.elim
            | terminal first =>
                exact action'.elim

/-- Forgetting one's own action need not be signal forgetting. -/
theorem eventClockSignalPerfectRecall :
    game.EventClockSignalPerfectRecall :=
  signalRecallCertificate.eventClockSignalPerfectRecall

/-- This regression is not absent-minded: signal recall already rules out
repetition of one decision information state along a play. -/
theorem hasNoAbsentMindedness :
    game.HasNoAbsentMindedness () :=
  (eventClockSignalPerfectRecall ()).hasNoAbsentMindedness

/-- The payoff-free projection has private-signal recall. -/
theorem controlledEventClockSignalPerfectRecall :
    game.toControlledObservedGame.EventClockSignalPerfectRecall :=
  fun i =>
    (game.hasEventClockSignalPerfectRecall_iff_toControlled i).mp
      (eventClockSignalPerfectRecall i)

/-- Constant public observations forget elapsed public time, so private-signal
recall does not imply public recall. -/
theorem controlled_not_hasEventClockPublicPerfectRecall :
    ¬ game.toControlledObservedGame.HasEventClockPublicPerfectRecall := by
  intro hrecall
  have heq := hrecall initial (atSecond false) rfl
  change [()] = [(), ()] at heq
  simp at heq

/-- The public stage of the two-decision tree. -/
inductive PublicStage
  | first
  | second
  | terminal
  deriving DecidableEq

/-- Public stage as a function of the current endpoint. -/
def publicStage : State → PublicStage
  | .root => .first
  | .second _ => .second
  | .terminal _ => .terminal

/-- A payoff-free presentation with perfectly remembered public stages but
an information state that forgets the player's first action. -/
def publicRecallGame : ControlledObservedGame Unit where
  base := base.toControlledGame
  Observation := fun _ => PublicStage
  PublicObservation := PublicStage
  observe := fun _ history => publicStage history.1
  publicObserve := fun history => publicStage history.1
  publicOf := fun _ stage => stage
  observe_public := by simp
  InfoState := fun _ => Stage
  infoObserve := fun _ stage =>
    match stage with
    | .first => .first
    | .second => .second
  infoAt := by
    intro history _i hmover _hnonterminal
    generalize hstate : history.1 = state at hmover
    cases state with
    | root => exact .first
    | second first => exact .second
    | terminal first => simp [base] at hmover
  infoAt_observe := by
    intro history i hmover _hnonterminal
    generalize hstate : history.1 = state at hmover ⊢
    cases state with
    | root => rfl
    | second first => rfl
    | terminal first => simp [base] at hmover
  InfoAction := fun _ stage => StageAction stage
  actionEquiv := by
    intro history _i hmover _hnonterminal
    generalize hstate : history.1 = state at hmover ⊢
    cases state with
    | root =>
        exact Equiv.refl Bool
    | second first =>
        exact Equiv.refl Unit
    | terminal first =>
        simp [base] at hmover

/-- Current public stage factors the complete public-stage sequence. -/
def publicRecallCertificate :
    publicRecallGame.PublicRecallCertificate where
  rememberedPublicSignals
    | .first => [.first]
    | .second => [.first, .second]
    | .terminal => [.first, .second, .terminal]
  rememberedPublicSignals_publicObserve := by
    intro history
    rcases history with ⟨state, path⟩
    induction path with
    | nil =>
        rfl
    | @snoc state path action ih =>
        cases state with
        | root =>
            cases action <;>
              simpa [publicRecallGame, publicStage, next,
                ControlledObservedGame.publicSignalHistory,
                ControlledObservedGame.publicSignalHistoryPath] using
                  congrArg
                    (fun signals =>
                      signals ++ [PublicStage.second])
                    ih
        | second first =>
            cases action
            simpa [publicRecallGame, publicStage, next,
              ControlledObservedGame.publicSignalHistory,
              ControlledObservedGame.publicSignalHistoryPath] using
                congrArg
                  (fun signals =>
                    signals ++ [PublicStage.terminal])
                  ih
        | terminal first =>
            exact action.elim

/-- Public recall holds in the payoff-free staged presentation. -/
theorem publicPerfectRecall :
    publicRecallGame.HasEventClockPublicPerfectRecall :=
  publicRecallCertificate.hasEventClockPublicPerfectRecall

/-- The public-recall presentation still forgets the player's own first
action, so public recall does not imply classic recall. -/
theorem publicRecallGame_not_hasPerfectRecall :
    ¬ publicRecallGame.HasPerfectRecall () := by
  intro hrecall
  have heq :=
    hrecall
      (atSecond false) (atSecond true)
      rfl (atSecond_decision false)
      rfl (atSecond_decision true) rfl
  change
    [publicRecallGame.personalDecisionAt () initial rfl false] =
      [publicRecallGame.personalDecisionAt () initial rfl true] at heq
  injection heq with hchoice
  have hbit :=
    congrArg
      (fun decision =>
        match decision with
        | ⟨⟨Stage.first, _⟩, choice⟩ => choice
        | ⟨⟨Stage.second, _⟩, _⟩ => false)
      hchoice
  change false = true at hbit
  exact Bool.noConfusion hbit

end ForgetOwn

end Examples.RecallHierarchy
