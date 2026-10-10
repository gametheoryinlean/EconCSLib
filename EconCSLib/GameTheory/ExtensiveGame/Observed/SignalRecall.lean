/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Observed.PerfectRecall

/-!
# Payoff-aware compatibility for private and public signal recall

Signal histories, recall predicates, and factorization certificates are
implemented once on `ControlledObservedGame`.  This module keeps the
historical `ObservedGame` names as definitional payoff-forgetting adapters.
-/

namespace ExtensiveGame.ObservedGame

variable {N U : Type*} {G : ObservedGame N U}

/-- Compatibility spelling for the private-signal path extractor. -/
abbrev signalHistoryPath
    (G : ObservedGame N U) (i : N) :
    {state : G.base.State} →
      G.base.toArena.History G.base.init state →
        List (G.Observation i) :=
  G.toControlledObservedGame.signalHistoryPath i

/-- Private signals along a complete history. -/
abbrev signalHistory
    (G : ObservedGame N U) (i : N)
    (history : G.base.toArena.HistoryFrom G.base.init) :
    List (G.Observation i) :=
  G.toControlledObservedGame.signalHistory i history

@[simp]
theorem signalHistory_nil
    (G : ObservedGame N U) (i : N) :
    G.signalHistory i
        (Arena.HistoryFrom.nil G.base.toArena G.base.init) =
      [G.observe i
        (Arena.HistoryFrom.nil G.base.toArena G.base.init)] :=
  G.toControlledObservedGame.signalHistory_nil i

@[simp]
theorem signalHistory_snoc
    (G : ObservedGame N U) (i : N)
    {state : G.base.State}
    (path : G.base.toArena.History G.base.init state)
    (action : G.base.Action state) :
    G.signalHistory i
        ⟨G.base.next state action, path.snoc action⟩ =
      G.signalHistory i ⟨state, path⟩ ++
        [G.observe i
          ⟨G.base.next state action, path.snoc action⟩] :=
  G.toControlledObservedGame.signalHistory_snoc i path action

/-- A private-signal history has one more coordinate than its action
history. -/
theorem signalHistory_length
    (G : ObservedGame N U) (i : N)
    (history : G.base.toArena.HistoryFrom G.base.init) :
    (G.signalHistory i history).length =
      history.2.length + 1 :=
  G.toControlledObservedGame.signalHistory_length i history

/-- Compatibility spelling for the public-signal path extractor. -/
abbrev publicSignalHistoryPath
    (G : ObservedGame N U) :
    {state : G.base.State} →
      G.base.toArena.History G.base.init state →
        List G.PublicObservation :=
  G.toControlledObservedGame.publicSignalHistoryPath

/-- Public signals along a complete history. -/
abbrev publicSignalHistory
    (G : ObservedGame N U)
    (history : G.base.toArena.HistoryFrom G.base.init) :
    List G.PublicObservation :=
  G.toControlledObservedGame.publicSignalHistory history

@[simp]
theorem publicSignalHistory_nil
    (G : ObservedGame N U) :
    G.publicSignalHistory
        (Arena.HistoryFrom.nil G.base.toArena G.base.init) =
      [G.publicObserve
        (Arena.HistoryFrom.nil G.base.toArena G.base.init)] :=
  G.toControlledObservedGame.publicSignalHistory_nil

@[simp]
theorem publicSignalHistory_snoc
    (G : ObservedGame N U)
    {state : G.base.State}
    (path : G.base.toArena.History G.base.init state)
    (action : G.base.Action state) :
    G.publicSignalHistory
        ⟨G.base.next state action, path.snoc action⟩ =
      G.publicSignalHistory ⟨state, path⟩ ++
        [G.publicObserve
          ⟨G.base.next state action, path.snoc action⟩] :=
  G.toControlledObservedGame.publicSignalHistory_snoc path action

/-- A public-signal history has one more coordinate than its action
history. -/
theorem publicSignalHistory_length
    (G : ObservedGame N U)
    (history : G.base.toArena.HistoryFrom G.base.init) :
    (G.publicSignalHistory history).length =
      history.2.length + 1 :=
  G.toControlledObservedGame.publicSignalHistory_length history

/-- Payoff-aware spelling for event-clock private-signal perfect recall. -/
abbrev HasEventClockSignalPerfectRecall
    (G : ObservedGame N U) (i : N) : Prop :=
  G.toControlledObservedGame.HasEventClockSignalPerfectRecall i

/-- Every player has private-signal recall. -/
abbrev EventClockSignalPerfectRecall
    (G : ObservedGame N U) : Prop :=
  G.toControlledObservedGame.EventClockSignalPerfectRecall

/-- Payoff-aware spelling for event-clock public-signal recall. -/
abbrev HasEventClockPublicPerfectRecall
    (G : ObservedGame N U) : Prop :=
  G.toControlledObservedGame.HasEventClockPublicPerfectRecall

/-- Singleton decision information implies private-signal recall. -/
theorem HasSingletonInformation.hasEventClockSignalPerfectRecall
    {i : N}
    (hinformation : G.HasSingletonInformation i) :
    G.HasEventClockSignalPerfectRecall i :=
  ControlledObservedGame.HasSingletonInformation.hasEventClockSignalPerfectRecall
    hinformation

/-- Perfect information implies private-signal recall for every player. -/
theorem PerfectInformation.eventClockSignalPerfectRecall
    (hinformation : G.PerfectInformation) :
    G.EventClockSignalPerfectRecall :=
  ControlledObservedGame.PerfectInformation.eventClockSignalPerfectRecall
    hinformation

/-- Signal recall rules out absent-mindedness. -/
theorem HasEventClockSignalPerfectRecall.hasNoAbsentMindedness
    {i : N}
    (hrecall : G.HasEventClockSignalPerfectRecall i) :
    G.HasNoAbsentMindedness i :=
  ControlledObservedGame.HasEventClockSignalPerfectRecall.hasNoAbsentMindedness
    hrecall

/-- Playerwise signal recall implies global no absent-mindedness. -/
theorem EventClockSignalPerfectRecall.noAbsentMindedness
    (hrecall : G.EventClockSignalPerfectRecall) :
    G.NoAbsentMindedness :=
  ControlledObservedGame.EventClockSignalPerfectRecall.noAbsentMindedness
    hrecall

/-- Compatibility spelling for a private-signal factorization certificate. -/
abbrev SignalRecallCertificate
    (G : ObservedGame N U) :=
  G.toControlledObservedGame.SignalRecallCertificate

namespace SignalRecallCertificate

/-- A private-signal factorization certificate proves signal recall. -/
theorem eventClockSignalPerfectRecall
    (certificate : G.SignalRecallCertificate) :
    G.EventClockSignalPerfectRecall :=
  ControlledObservedGame.SignalRecallCertificate.eventClockSignalPerfectRecall
    certificate

end SignalRecallCertificate

/-- Compatibility spelling for a public-signal factorization certificate. -/
abbrev PublicRecallCertificate
    (G : ObservedGame N U) :=
  G.toControlledObservedGame.PublicRecallCertificate

namespace PublicRecallCertificate

/-- A public factorization certificate proves public recall. -/
theorem hasEventClockPublicPerfectRecall
    (certificate : G.PublicRecallCertificate) :
    G.HasEventClockPublicPerfectRecall :=
  ControlledObservedGame.PublicRecallCertificate.hasEventClockPublicPerfectRecall
    certificate

end PublicRecallCertificate

end ExtensiveGame.ObservedGame
