/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Interface.Winning

/-!
# Pathwise versus profile-based winning

This regression proves that pathwise robust winning and winning against every
pure opponent profile differ in imperfect-information presentations.

Player `1` moves twice at the same information state. Every pure strategy for
player `1` must choose the same Boolean action on both visits. A merely legal
path may choose `false` and then `true`, however. Player `0` wins exactly on
paths compatible with some pure strategy of player `1`; consequently player
`0` wins against every pure profile but not against every locally compatible
path.
-/

namespace WinningSemantics

inductive State
  | root
  | after (first : Bool)
  | terminal (first second : Bool)
  deriving DecidableEq

def Action : State → Type
  | .root => Bool
  | .after _ => Bool
  | .terminal _ _ => Empty

def next : (state : State) → Action state → State
  | .root, first => .after first
  | .after first, second => .terminal first second

def arena : Arena where
  State := State
  Action := Action
  next := next

def base : ExtensiveGame (Fin 2) Unit where
  toArena := arena
  init := .root
  mover
    | .root => some 1
    | .after _ => some 1
    | .terminal _ _ => none
  payoff := fun _ _ => ()

/-- Both visits controlled by player `1` share one information state. -/
def game : ExtensiveGame.ObservedGame (Fin 2) Unit where
  base := base
  Observation := fun _ => Unit
  PublicObservation := Unit
  observe := fun _ _ => ()
  publicObserve := fun _ => ()
  publicOf := fun _ _ => ()
  observe_public := by simp
  InfoState := fun _ => Unit
  infoObserve := fun _ _ => ()
  infoAt := fun _ _ _ _ => ()
  infoAt_observe := by simp
  InfoAction := fun _ _ => Bool
  actionEquiv := by
    intro history i hmover _hnonterminal
    generalize hstate : history.1 = state at hmover ⊢
    cases state with
    | root =>
        exact Equiv.refl Bool
    | after first =>
        exact Equiv.refl Bool
    | terminal first second =>
        simp [base] at hmover

theorem terminal_terminal (first second : Bool) :
    arena.IsTerminal (.terminal first second) := by
  change IsEmpty Empty
  infer_instance

theorem not_terminal_root :
    ¬ arena.IsTerminal .root :=
  fun hterminal => hterminal.false false

theorem not_terminal_after (first : Bool) :
    ¬ arena.IsTerminal (.after first) :=
  fun hterminal => hterminal.false false

local instance terminalDecidable
    (state : game.base.State) :
    Decidable (game.base.isTerminal state) :=
  match state with
  | .root => isFalse not_terminal_root
  | .after first => isFalse (not_terminal_after first)
  | .terminal first second => isTrue (terminal_terminal first second)

local instance arenaTerminalDecidable
    (state : arena.State) :
    Decidable (arena.IsTerminal state) :=
  terminalDecidable state

example : decide (game.base.isTerminal .root) = false ∧
    decide (arena.IsTerminal (.after false)) = false ∧
    decide (arena.IsTerminal (.terminal false true)) = true := by
  native_decide

theorem noChance : base.NoChance := by
  intro state hnonterminal
  cases state with
  | root =>
      exact ⟨1, rfl⟩
  | after first =>
      exact ⟨1, rfl⟩
  | terminal first second =>
      exact (hnonterminal (terminal_terminal first second)).elim

/-- Reachable no-chance certificate consumed by strategic execution. -/
theorem noChanceOnHistories : base.NoChanceOnHistories :=
  noChance.noChanceOnHistories

def zeroStrategy : game.PureStrategy 0 :=
  fun _ => false

/-- Player `0` wins a path exactly when it is consistent with some single
pure contingent plan of player `1`. -/
def winning :
    arena.WinningCondition .root (Fin 2) :=
  fun i =>
    if i = 0 then
      {play | ∃ strategy : game.PureStrategy 1,
        game.IsCompatibleWithPlayerStrategy
          1 strategy play}
    else
      Set.univ

/-- Against every pure profile, the opponent's own component witnesses that
the generated play is in player `0`'s winning set. -/
theorem zero_strategic :
    game.HasStrategicWinningStrategy
      noChanceOnHistories winning 0 zeroStrategy := by
  constructor
  · exact ⟨fun _ _ => false, rfl⟩
  · intro profile _hprofile
    change ∃ strategy : game.PureStrategy 1,
      game.IsCompatibleWithPlayerStrategy 1 strategy
        ((profile.toHistoryPolicy game noChanceOnHistories).completePlay)
    exact
      ⟨profile 1,
        profile.completePlay_isCompatibleWithPlayerStrategy
          noChanceOnHistories 1⟩

def initial : arena.HistoryFrom .root :=
  Arena.HistoryFrom.nil arena .root

/-- The sole represented decision-information coordinate of player `1`. -/
def oneInformation : game.RepresentedInfo 1 :=
  game.representedInfoAt initial 1 rfl ⟨false⟩

@[simp]
theorem representedInfo_one_eq
    (information : game.RepresentedInfo 1) :
    information = oneInformation := by
  apply Subtype.ext
  change information.1 = ()
  cases information.1
  rfl

def afterFalse : arena.HistoryFrom .root :=
  ⟨.after false, initial.2.snoc false⟩

def terminalFalseTrue : arena.HistoryFrom .root :=
  ⟨.terminal false true, afterFalse.2.snoc true⟩

/-- A legal path on which the opponent makes different choices at the two
visits to its shared information state. -/
def inconsistentPlay : arena.CompletePlayFrom .root :=
  Arena.CompletePlayFromHistory.prependChild
    (Arena.IsChildFrom.snoc initial false)
    (Arena.CompletePlayFromHistory.prependChild
      (Arena.IsChildFrom.snoc afterFalse true)
      (Arena.CompletePlayFromHistory.stutter
        terminalFalseTrue
        (terminal_terminal false true)))

theorem mover_ne_zero (state : State) :
    base.mover state ≠ some 0 := by
  cases state <;> simp [base]

/-- Since player `0` never moves, the inconsistent path is locally compatible
with its strategy. -/
theorem inconsistent_compatible :
    game.IsCompatibleWithPlayerStrategy
      0 zeroStrategy inconsistentPlay := by
  intro n _hnonterminal hmover
  exact (mover_ne_zero _ hmover).elim

/-- The same player-`0` strategy is not pathwise winning: the locally legal
inconsistent path cannot be generated by any information-consistent opponent
strategy. -/
theorem zero_not_pathwise :
    ¬ game.HasPathwiseWinningStrategy
      winning 0 zeroStrategy := by
  intro hwinning
  have hwins :=
    hwinning inconsistentPlay inconsistent_compatible
  change ∃ strategy : game.PureStrategy 1,
    game.IsCompatibleWithPlayerStrategy
      1 strategy inconsistentPlay at hwins
  rcases hwins with ⟨strategy, hcompatible⟩
  have hzero := hcompatible 0 not_terminal_root rfl
  have hone := hcompatible 1 (not_terminal_after false) rfl
  have hzeroState := congrArg Sigma.fst hzero
  have honeState := congrArg Sigma.fst hone
  simp only [ExtensiveGame.ObservedGame.PureStrategy.actionAt, game] at hzeroState honeState
  change State.after false =
    State.after (strategy oneInformation) at hzeroState
  change State.terminal false true =
    State.terminal false (strategy oneInformation) at honeState
  have hchosenFalse : strategy oneInformation = false := by
    injection hzeroState with h
    exact h.symm
  have hchosenTrue : strategy oneInformation = true := by
    injection honeState with _ h
    exact h.symm
  rw [hchosenFalse] at hchosenTrue
  contradiction

end WinningSemantics
