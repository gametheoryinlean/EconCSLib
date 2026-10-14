/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Infrastructure.Core

/-!
# Payoff-free quasistrategies

Information-consistent nonempty action permissions, refinement, pure-strategy
embedding, and complete-play compatibility. Winning predicates are deliberately
owned by `Winning.Basic` so this structural leaf has no objective dependency.
-/

namespace ExtensiveGame.ControlledObservedGame

variable {N : Type*} {G : ControlledObservedGame N}

/-! ## Quasistrategies -/

/-- A nonempty set of admissible values. -/
structure NonemptyActionSet (Action : Type*) where
  /-- Permitted values. -/
  allowed : Set Action
  /-- At least one value is permitted. -/
  nonempty : allowed.Nonempty

/-- Information-consistent nondeterministic permissions for player `i`,
indexed only by information values represented at genuine decisions. -/
def QuasiStrategy
    (G : ControlledObservedGame N) (i : N) :=
  (information : G.RepresentedInfo i) →
    NonemptyActionSet (G.InfoAction i information.1)

namespace QuasiStrategy

/-- Pointwise refinement of quasistrategy permissions. -/
def Refines {i : N}
    (narrow broad : G.QuasiStrategy i) : Prop :=
  ∀ information,
    (narrow information).allowed ⊆
      (broad information).allowed

/-- Embed a pure strategy as singleton permissions. -/
def ofPure {i : N} (strategy : G.PureStrategy i) :
    G.QuasiStrategy i :=
  fun information =>
    { allowed := {strategy information}
      nonempty := ⟨strategy information, Set.mem_singleton _⟩ }

end QuasiStrategy

/-- A complete play follows one player's quasistrategy from `current`. -/
def IsCompatibleWithQuasiStrategyFrom
    {current : G.base.History}
    (i : N) (strategy : G.QuasiStrategy i)
    (play : G.base.CompletePlayFromHistory current) : Prop :=
  ∀ (n : ℕ)
    (hnonterminal :
      ¬ G.base.isTerminal (play.historyAt n).1)
    (hmover :
      G.base.mover (play.historyAt n).1 = some i),
    let hdecision :=
      G.base.toArena.isDecision_of_not_isTerminal
        (play.historyAt n).1 hnonterminal
    let information :=
      G.representedInfoAt (play.historyAt n) i hmover hdecision
    ∃ abstractAction : G.InfoAction i information.1,
      abstractAction ∈
          (strategy information).allowed ∧
        play.historyAt (n + 1) =
          ⟨G.base.next (play.historyAt n).1
              (G.actionEquiv
                (play.historyAt n) i hmover hdecision
                abstractAction),
            (play.historyAt n).2.snoc
              (G.actionEquiv
                (play.historyAt n) i hmover hdecision
                abstractAction)⟩

/-- Root-started quasistrategy compatibility. -/
abbrev IsCompatibleWithQuasiStrategy
    (G : ControlledObservedGame N) (i : N)
    (strategy : G.QuasiStrategy i)
    (play : G.base.CompletePlay) : Prop :=
  G.IsCompatibleWithQuasiStrategyFrom i strategy play

/-- Pure compatibility is quasistrategy compatibility for singleton
permissions. -/
theorem isCompatibleWithQuasiStrategy_ofPure_iff
    {current : G.base.History}
    (i : N) (strategy : G.PureStrategy i)
    (play : G.base.CompletePlayFromHistory current) :
    G.IsCompatibleWithQuasiStrategyFrom
        i (QuasiStrategy.ofPure strategy) play ↔
      G.IsCompatibleWithPlayerStrategyFrom
        i strategy play := by
  constructor
  · intro h n hterminal hmover
    rcases h n hterminal hmover with
      ⟨action, hallowed, hnext⟩
    let hdecision :=
      G.base.toArena.isDecision_of_not_isTerminal
        (play.historyAt n).1 hterminal
    let information :=
      G.representedInfoAt (play.historyAt n) i hmover hdecision
    have ha :
        action =
          strategy information := by
      simpa [QuasiStrategy.ofPure] using hallowed
    subst action
    exact hnext
  · intro h n hterminal hmover
    let hdecision :=
      G.base.toArena.isDecision_of_not_isTerminal
        (play.historyAt n).1 hterminal
    let information :=
      G.representedInfoAt (play.historyAt n) i hmover hdecision
    exact
      ⟨strategy information,
        Set.mem_singleton _,
        h n hterminal hmover⟩

end ExtensiveGame.ControlledObservedGame
