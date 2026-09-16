/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Interface.Winning

/-!
# A two-step imperfect-information game with no pure winner

This finite logical game uses the payoff-free `ControlledObservedGame`.
Player `0` chooses a hidden Boolean and player `1`, who observes no private or
public signal about that choice, guesses a Boolean. Player `0` wins on a
mismatch and player `1` wins on a match.

Every pure strategy of player `0` is defeated by the matching reply, while
every pure strategy of player `1` is defeated by the opposite hidden bit.
Thus the winning condition is total and exclusive, but neither player has a
pure pathwise winning strategy. This is the intended negative boundary:
totality is not determinacy, and finite length alone does not justify a
perfect-information determinacy theorem.
-/

namespace Examples.TwoStepImperfectNoWinner

open ExtensiveGame

/-- Root, hidden-bit state, and terminal guess state. -/
inductive State
  | root
  | hidden (bit : Bool)
  | terminal (bit guess : Bool)
  deriving DecidableEq

/-- Both decisions are Boolean; terminal states have no actions. -/
def Action : State → Type
  | .root => Bool
  | .hidden _ => Bool
  | .terminal _ _ => Empty

/-- First store the hidden bit, then store the guess. -/
def next : (state : State) → Action state → State
  | .root, bit => .hidden bit
  | .hidden bit, guess => .terminal bit guess

/-- The underlying deterministic arena. -/
def arena : Arena where
  State := State
  Action := Action
  next := next

/-- Payoff-free control: player `0` chooses, then player `1` guesses. -/
def base : ControlledGame (Fin 2) where
  toArena := arena
  init := .root
  mover
    | .root => some 0
    | .hidden _ => some 1
    | .terminal _ _ => none

/-- At each decision state, the abstract Boolean action is the concrete
Boolean action. -/
def baseActionEquiv (state : State) (i : Fin 2)
    (hmover : base.mover state = some i)
    (_hdecision : base.toArena.IsDecision state) :
    Bool ≃ base.Action state := by
  cases state with
  | root =>
      exact Equiv.refl Bool
  | hidden bit =>
      exact Equiv.refl Bool
  | terminal bit guess =>
      simp [base] at hmover

/-- Both players receive only a trivial signal and have one decision
information state. In particular player `1` cannot observe the hidden bit. -/
def game : ControlledObservedGame (Fin 2) where
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
  actionEquiv := fun history i hmover hdecision =>
    baseActionEquiv history.1 i hmover hdecision

/-- The initial empty history. -/
def initial : arena.HistoryFrom .root :=
  Arena.HistoryFrom.nil arena .root

/-- The sole represented decision-information coordinate of player `0`. -/
def zeroInformation : game.RepresentedInfo 0 :=
  game.representedInfoAt initial 0 rfl ⟨false⟩

/-- History after choosing one hidden bit. -/
def afterHidden (bit : Bool) :
    arena.HistoryFrom .root :=
  ⟨.hidden bit, initial.2.snoc bit⟩

/-- The sole represented decision-information coordinate of player `1`. -/
def oneInformation : game.RepresentedInfo 1 :=
  game.representedInfoAt (afterHidden false) 1 rfl ⟨false⟩

/-- Terminal history after a bit and guess. -/
def afterGuess (bit guess : Bool) :
    arena.HistoryFrom .root :=
  ⟨.terminal bit guess,
    (afterHidden bit).2.snoc guess⟩

/-- Terminal states really have no legal action. -/
theorem terminal_isTerminal (bit guess : Bool) :
    arena.IsTerminal (.terminal bit guess) := by
  change IsEmpty Empty
  infer_instance

/-- The complete two-step play with the indicated hidden bit and guess. -/
def play (bit guess : Bool) :
    arena.CompletePlayFrom .root :=
  Arena.CompletePlayFromHistory.prependChild
    (Arena.IsChildFrom.snoc initial bit)
    (Arena.CompletePlayFromHistory.prependChild
      (Arena.IsChildFrom.snoc (afterHidden bit) guess)
      (Arena.CompletePlayFromHistory.stutter
        (afterGuess bit guess)
        (terminal_isTerminal bit guess)))

@[simp]
theorem play_at_zero (bit guess : Bool) :
    (play bit guess).historyAt 0 = initial :=
  rfl

@[simp]
theorem play_at_one (bit guess : Bool) :
    (play bit guess).historyAt 1 = afterHidden bit :=
  rfl

@[simp]
theorem play_at_two (bit guess : Bool) :
    (play bit guess).historyAt 2 = afterGuess bit guess :=
  rfl

/-- Read the hidden-bit component of a terminal state; the default is
irrelevant because every play has terminated by coordinate two. -/
def hiddenBitAt : State → Bool
  | .terminal bit _guess => bit
  | _ => false

/-- Read the guess component of a terminal state; the default is irrelevant
because every play has terminated by coordinate two. -/
def guessAt : State → Bool
  | .terminal _bit guess => guess
  | _ => false

/-- Match/mismatch winning condition read from the terminal coordinate. -/
def winning : base.WinningCondition :=
  fun i =>
    {path |
      if i = 0 then
        hiddenBitAt (path.historyAt 2).1 ≠
          guessAt (path.historyAt 2).1
      else
        hiddenBitAt (path.historyAt 2).1 =
          guessAt (path.historyAt 2).1}

/-- A concrete two-step play is won by player `0` exactly on mismatch. -/
@[simp]
theorem play_mem_zero_iff (bit guess : Bool) :
    play bit guess ∈ winning 0 ↔ bit ≠ guess := by
  change
    (if (0 : Fin 2) = 0 then
      hiddenBitAt ((play bit guess).historyAt 2).1 ≠
        guessAt ((play bit guess).historyAt 2).1
    else
      hiddenBitAt ((play bit guess).historyAt 2).1 =
        guessAt ((play bit guess).historyAt 2).1) ↔ _
  cases bit <;> cases guess <;>
    simp [afterGuess, hiddenBitAt, guessAt]

/-- A concrete two-step play is won by player `1` exactly on a match. -/
@[simp]
theorem play_mem_one_iff (bit guess : Bool) :
    play bit guess ∈ winning 1 ↔ bit = guess := by
  change
    (if (1 : Fin 2) = 0 then
      hiddenBitAt ((play bit guess).historyAt 2).1 ≠
        guessAt ((play bit guess).historyAt 2).1
    else
      hiddenBitAt ((play bit guess).historyAt 2).1 =
        guessAt ((play bit guess).historyAt 2).1) ↔ _
  cases bit <;> cases guess <;>
    simp [afterGuess, hiddenBitAt, guessAt]

/-- The play using player `0`'s chosen bit is compatible with that strategy,
regardless of player `1`'s reply. -/
theorem play_compatible_zero
    (strategy : game.PureStrategy 0)
    (guess : Bool) :
    game.IsCompatibleWithPlayerStrategy
      0 strategy (play (strategy zeroInformation) guess) := by
  intro n hnonterminal hmover
  cases n with
  | zero =>
      simp [ControlledObservedGame.PureStrategy.actionAt, game, initial,
        afterHidden, base, arena, next, baseActionEquiv,
        Arena.HistoryFrom.nil]
      constructor <;> rfl
  | succ n =>
      cases n with
      | zero =>
          change
            (some 1 : Option (Fin 2)) = some 0
            at hmover
          simp at hmover
      | succ n =>
          change
            (none : Option (Fin 2)) = some 0
            at hmover
          simp at hmover

/-- The play using player `1`'s guess is compatible with that strategy,
regardless of player `0`'s hidden bit. -/
theorem play_compatible_one
    (strategy : game.PureStrategy 1)
    (bit : Bool) :
    game.IsCompatibleWithPlayerStrategy
      1 strategy (play bit (strategy oneInformation)) := by
  intro n hnonterminal hmover
  cases n with
  | zero =>
      change
        (some 0 : Option (Fin 2)) = some 1
        at hmover
      simp at hmover
  | succ n =>
      cases n with
      | zero =>
          simp [ControlledObservedGame.PureStrategy.actionAt, game, initial,
            afterHidden, afterGuess, base, arena, next, baseActionEquiv,
            Arena.HistoryFrom.nil]
          constructor <;> rfl
      | succ n =>
          change
            (none : Option (Fin 2)) = some 1
            at hmover
          simp at hmover

/-- Player `0` has no pure pathwise winning strategy: player `1` can match
the chosen hidden bit. -/
theorem no_pure_winner_zero :
    ¬ ∃ strategy : game.PureStrategy 0,
      game.HasPathwiseWinningStrategy
        winning 0 strategy := by
  rintro ⟨strategy, hwinning⟩
  have hwins :=
    hwinning
      (play (strategy zeroInformation) (strategy zeroInformation))
      (play_compatible_zero strategy (strategy zeroInformation))
  exact (play_mem_zero_iff
    (strategy zeroInformation) (strategy zeroInformation)).mp hwins rfl

/-- Player `1` has no pure pathwise winning strategy: player `0` can choose
the opposite hidden bit. -/
theorem no_pure_winner_one :
    ¬ ∃ strategy : game.PureStrategy 1,
      game.HasPathwiseWinningStrategy
        winning 1 strategy := by
  rintro ⟨strategy, hwinning⟩
  let bit := !(strategy oneInformation)
  have hwins :=
    hwinning
      (play bit (strategy oneInformation))
      (play_compatible_one strategy bit)
  have heq :=
    (play_mem_one_iff bit (strategy oneInformation)).mp hwins
  cases hguess : strategy oneInformation <;>
    simp [bit, hguess] at heq

/-- Neither player has a pure pathwise winning strategy. -/
theorem no_pure_winner :
    (¬ ∃ strategy : game.PureStrategy 0,
      game.HasPathwiseWinningStrategy winning 0 strategy) ∧
    (¬ ∃ strategy : game.PureStrategy 1,
      game.HasPathwiseWinningStrategy winning 1 strategy) :=
  ⟨no_pure_winner_zero, no_pure_winner_one⟩

/-- Match versus mismatch is an explicit complementary two-player objective
on every complete play, independently of reachability details. -/
theorem winning_zeroSum :
    winning.IsTwoPlayerZeroSum := by
  intro path
  generalize hhidden :
      hiddenBitAt (path.historyAt 2).1 = hidden
  generalize hguess :
      guessAt (path.historyAt 2).1 = guess
  cases hidden <;> cases guess <;>
    simp [winning, hhidden, hguess]

/-- Every complete play is won by one of the two players. -/
theorem winning_total :
    winning.IsTotal :=
  winning_zeroSum.isTotal

/-- No complete play is won by both distinct players. -/
theorem winning_exclusive :
    winning.IsExclusive :=
  winning_zeroSum.isExclusive

/-- This total, exclusive finite logical game is not pure pathwise
determined. -/
theorem not_determined :
    ¬ game.IsTwoPlayerDetermined winning := by
  intro hdetermined
  rcases hdetermined with hzero | hone
  · exact no_pure_winner_zero hzero
  · exact no_pure_winner_one hone

end Examples.TwoStepImperfectNoWinner
