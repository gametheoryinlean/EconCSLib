/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Observed.Game
import EconCSLib.GameTheory.ExtensiveGame.Winning.Basic

/-!
# Payoff-aware winning-strategy compatibility

The objective and payoff-free pathwise-winning definitions are owned by
`Winning.Basic`.  This module retains the legacy `ObservedGame` strategy
surface and its profile-based bridges.
-/

namespace ExtensiveGame.ObservedGame

variable {N U : Type*} {G : ObservedGame N U}

/-- A complete play from `current` is compatible with one player's pure
strategy when every controlled coordinate takes the prescribed action. -/
def IsCompatibleWithPlayerStrategyFrom
    {current :
      G.base.toArena.HistoryFrom G.base.init}
    (i : N) (strategy : G.PureStrategy i)
    (play :
      G.base.toArena.CompletePlayFromHistory current) : Prop :=
  ∀ (n : ℕ)
    (hnonterminal :
      ¬ G.base.isTerminal (play.historyAt n).1)
    (hmover :
      G.base.mover (play.historyAt n).1 = some i),
    play.historyAt (n + 1) =
      ⟨G.base.next (play.historyAt n).1
          (ObservedGame.PureStrategy.actionAt G strategy
            (play.historyAt n) hmover
            (G.base.toArena.isDecision_of_not_isTerminal
              (play.historyAt n).1 hnonterminal)),
        (play.historyAt n).2.snoc
          (ObservedGame.PureStrategy.actionAt G strategy
            (play.historyAt n) hmover
            (G.base.toArena.isDecision_of_not_isTerminal
              (play.historyAt n).1 hnonterminal))⟩

/-- Root-started compatibility with one observed-game pure strategy. -/
abbrev IsCompatibleWithPlayerStrategy
    (G : ObservedGame N U) (i : N)
    (strategy : G.PureStrategy i)
    (play :
    G.base.toArena.CompletePlayFrom G.base.init) : Prop :=
  G.IsCompatibleWithPlayerStrategyFrom i strategy play

/-- The no-chance complete play is compatible with every profile component. -/
theorem PureProfile.completePlay_isCompatibleWithPlayerStrategy
    [(state : G.base.State) →
      Decidable (G.base.isTerminal state)]
    (profile : G.PureProfile)
    (hNoChance : G.base.NoChanceOnHistories) (i : N) :
    G.IsCompatibleWithPlayerStrategy i (profile i)
      ((profile.toHistoryPolicy G hNoChance).completePlay) := by
  intro n hnonterminal hmover
  change
    Arena.stoppedHistory
        (profile.toHistoryPolicy G hNoChance) (n + 1) =
      ⟨G.base.next
          (Arena.stoppedHistory
            (profile.toHistoryPolicy G hNoChance) n).1
            (ObservedGame.PureStrategy.actionAt G (profile i)
              (Arena.stoppedHistory
                (profile.toHistoryPolicy G hNoChance) n)
            hmover
            (G.base.toArena.isDecision_of_not_isTerminal _
              hnonterminal)),
        (Arena.stoppedHistory
            (profile.toHistoryPolicy G hNoChance) n).2.snoc
            (ObservedGame.PureStrategy.actionAt G (profile i)
              (Arena.stoppedHistory
                (profile.toHistoryPolicy G hNoChance) n)
            hmover
            (G.base.toArena.isDecision_of_not_isTerminal _
              hnonterminal))⟩
  rw [Arena.stoppedHistory,
    Arena.stoppedHistoryFrom_add
      (profile.toHistoryPolicy G hNoChance)
      (Arena.HistoryFrom.nil G.base.toArena G.base.init) n 1]
  rw [Arena.stoppedHistoryFrom_succ_of_not_terminal
    (profile.toHistoryPolicy G hNoChance)
    (Arena.stoppedHistoryFrom
      (profile.toHistoryPolicy G hNoChance)
      (Arena.HistoryFrom.nil G.base.toArena G.base.init) n)
    0 hnonterminal]
  rw [Arena.stoppedHistoryFrom_zero]
  simp only [Arena.stoppedHistory]
  have haction :
      profile.toHistoryPolicy G hNoChance
          (Arena.stoppedHistoryFrom
            (profile.toHistoryPolicy G hNoChance)
            (Arena.HistoryFrom.nil
              G.base.toArena G.base.init) n)
          hnonterminal =
        ObservedGame.PureStrategy.actionAt G (profile i)
          (Arena.stoppedHistoryFrom
            (profile.toHistoryPolicy G hNoChance)
            (Arena.HistoryFrom.nil
              G.base.toArena G.base.init) n)
          hmover
          (G.base.toArena.isDecision_of_not_isTerminal _
            hnonterminal) :=
    profile.toHistoryPolicy_of_mover
      G hNoChance _ hnonterminal i hmover
  rw [haction]

/-- A pathwise robust pure winning strategy on a payoff-aware compatibility
carrier. -/
def HasPathwiseWinningStrategy
    (G : ObservedGame N U)
    (W :
      G.base.toArena.WinningCondition G.base.init N)
    (i : N) (strategy : G.PureStrategy i) : Prop :=
  ∀ play : G.base.toArena.CompletePlayFrom G.base.init,
    G.IsCompatibleWithPlayerStrategy i strategy play →
      play ∈ W i

/-- The selected strategy extends to at least one complete pure profile. -/
def HasPureProfileExtension
    (G : ObservedGame N U)
    (i : N) (strategy : G.PureStrategy i) : Prop :=
  ∃ profile : G.PureProfile, profile i = strategy

/-- Inhabited profiles extend every selected component strategy. -/
theorem hasPureProfileExtension_of_nonempty_pureProfile
    (hprofile : Nonempty G.PureProfile)
    (i : N) (strategy : G.PureStrategy i) :
    G.HasPureProfileExtension i strategy := by
  classical
  rcases hprofile with ⟨profile⟩
  exact
    ⟨Function.update profile i strategy,
      Function.update_self i strategy profile⟩

/-- Profile-based strategic winning in a no-chance game. -/
def HasStrategicWinningStrategy
    (G : ObservedGame N U)
    [(state : G.base.State) →
      Decidable (G.base.isTerminal state)]
    (hNoChance : G.base.NoChanceOnHistories)
    (W :
      G.base.toArena.WinningCondition G.base.init N)
    (i : N) (strategy : G.PureStrategy i) : Prop :=
  G.HasPureProfileExtension i strategy ∧
    ∀ profile : G.PureProfile,
      profile i = strategy →
        (profile.toHistoryPolicy G hNoChance).completePlay ∈ W i

/-- Pathwise winning implies profile-based winning when the component extends. -/
theorem HasPathwiseWinningStrategy.hasStrategicWinningStrategy
    [(state : G.base.State) →
      Decidable (G.base.isTerminal state)]
    {W :
      G.base.toArena.WinningCondition G.base.init N}
    {i : N} {strategy : G.PureStrategy i}
    (hwinning :
      G.HasPathwiseWinningStrategy W i strategy)
    (hNoChance : G.base.NoChanceOnHistories)
    (hextends :
      G.HasPureProfileExtension i strategy) :
    G.HasStrategicWinningStrategy hNoChance W i strategy := by
  refine ⟨hextends, ?_⟩
  intro profile hprofile
  apply hwinning
  have hcompatible :=
    profile.completePlay_isCompatibleWithPlayerStrategy
      hNoChance i
  simpa [hprofile] using hcompatible

/-- Every locally compatible play is generated by some extending pure
profile. -/
def EveryCompatiblePlayRealizableByPureProfile
    (G : ObservedGame N U)
    [(state : G.base.State) →
      Decidable (G.base.isTerminal state)]
    (hNoChance : G.base.NoChanceOnHistories)
    (i : N) (strategy : G.PureStrategy i) : Prop :=
  ∀ play : G.base.toArena.CompletePlayFrom G.base.init,
    G.IsCompatibleWithPlayerStrategy i strategy play →
      ∃ profile : G.PureProfile,
        profile i = strategy ∧
          (profile.toHistoryPolicy G hNoChance).completePlay = play

/-- Strategic winning implies pathwise winning under a realizability
certificate. -/
theorem HasStrategicWinningStrategy.hasPathwiseWinningStrategy
    [(state : G.base.State) →
      Decidable (G.base.isTerminal state)]
    {W :
      G.base.toArena.WinningCondition G.base.init N}
    {i : N} {strategy : G.PureStrategy i}
    {hNoChance : G.base.NoChanceOnHistories}
    (hwinning :
      G.HasStrategicWinningStrategy hNoChance W i strategy)
    (hrealizable :
      G.EveryCompatiblePlayRealizableByPureProfile
        hNoChance i strategy) :
    G.HasPathwiseWinningStrategy W i strategy := by
  intro play hcompatible
  rcases hrealizable play hcompatible with
    ⟨profile, hprofile, hplay⟩
  rw [← hplay]
  exact hwinning.2 profile hprofile

end ExtensiveGame.ObservedGame
