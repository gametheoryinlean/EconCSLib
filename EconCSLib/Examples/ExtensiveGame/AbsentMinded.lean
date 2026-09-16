/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Observed.DeferredSampling.Realization
import EconCSLib.GameTheory.ExtensiveGame.Observed.SignalRecall

/-!
# EconCSLib.Examples.ExtensiveGame.AbsentMinded

Regression for the no-absent-mindedness boundary documented in
`docs/design/efg-general-foundations-2-strategy.md`.

`ObservedGame.HasNoAbsentMindedness` is the hypothesis that a player never
revisits one of their decision information states along a single complete
history.  It is exactly the freshness premise consumed by
`ExtensiveGame.ObservedGame.FutureDecisionKeysAvailable.afterPlayer`: after a
player step erases the current decision key from the available set, no-absent-
mindedness is what guarantees the erased key cannot recur on any continuation.

This module builds a minimal finite `ObservedGame` that **is** absent-minded and
shows the failure explicitly.

## The game

Three collinear world states `s0 → s1 → s2`.  Player `0` moves at both `s0` and
`s1`, and every player observation and decision information state is trivial
(a single element).  Thus player `0` faces the *same* decision information state
at `s0` and again at `s1`, on one history.

## Main results

* `Examples.AbsentMinded.infoState_recurs` — the single player-`0` information
  state recurs along the history `s0 → s1`.
* `firstDecision_isLawfulSubgameRoot` and
  `secondDecision_not_isLawfulSubgameRoot` — the whole game remains a lawful
  subgame by convention, while the later proper root is rejected because its
  information set crosses the continuation boundary.
* `Examples.AbsentMinded.not_hasNoAbsentMindedness` and
  `not_noAbsentMindedness` — `HasNoAbsentMindedness`/`NoAbsentMindedness` fail.
* `not_eventClockSignalPerfectRecall` — event-clock signal recall fails as a consequence, without
  conflating it with classic perfect recall.
* `Examples.AbsentMinded.futureDecisionKeysAvailable_firstDecision` — the
  non-freshness premises are genuinely satisfied before the first move.
* `Examples.AbsentMinded.afterPlayerConclusionFails` — the conclusion that
  `afterPlayer` would produce is *false* here: erasing the current decision key
  drops a key that is still required later.  This is precisely why the
  `NoAbsentMindedness` premise of `afterPlayer` is indispensable and
  unavailable for this game.
* `Examples.AbsentMinded.afterPlayer_premise_necessity` — all the relevant
  premises and the failed erased-key conclusion are packaged into one
  regression theorem; it demonstrates unavailability of the
  no-absent-mindedness premise, not falsity of `afterPlayer`.
-/

namespace Examples.AbsentMinded

open ExtensiveGame

/-- Three collinear world states; player `0` acts at `s0` and `s1`. -/
inductive Rung
  | s0
  | s1
  | s2

/-- Legal actions: one action at each of `s0`, `s1`; `s2` is terminal. -/
def rungAction : Rung → Type
  | .s0 => Unit
  | .s1 => Unit
  | .s2 => PEmpty

/-- The deterministic transition `s0 → s1 → s2`. -/
def rungNext : (r : Rung) → rungAction r → Rung
  | .s0, _ => .s1
  | .s1, _ => .s2
  | .s2, a => nomatch a

/-- Player `0` moves at `s0` and `s1`; `s2` is terminal. -/
def rungMover : Rung → Option (Fin 1)
  | .s0 => some 0
  | .s1 => some 0
  | .s2 => none

/-- The base extensive game on the three collinear states. -/
def base : ExtensiveGame (Fin 1) ℤ where
  State := Rung
  Action := rungAction
  next := rungNext
  init := .s0
  mover := rungMover
  payoff := fun _ _ => 0

/-- The abstract-action equivalence at a player-controlled state.  Only `s0` and
`s1` are player controlled, and both carry a single action, matching the trivial
information action `Unit`. -/
def rungActionEquiv :
    (i : Fin 1) → (r : Rung) → rungMover r = some i → (Unit ≃ rungAction r)
  | _, .s0, _ => Equiv.refl Unit
  | _, .s1, _ => Equiv.refl Unit
  | _, .s2, h => absurd h (by simp [rungMover])

/-- A minimal absent-minded observed game: every observation and decision
information state is trivial, so player `0`'s information at `s0` and `s1`
coincide. -/
def absentMindedGame : ObservedGame (Fin 1) ℤ where
  base := base
  Observation := fun _ => Unit
  PublicObservation := Unit
  observe := fun _ _ => ()
  publicObserve := fun _ => ()
  publicOf := fun _ _ => ()
  observe_public := fun _ _ => rfl
  InfoState := fun _ => Unit
  infoObserve := fun _ _ => ()
  infoAt := fun _ _ _ _ => ()
  infoAt_observe := fun _ _ _ _ => rfl
  InfoAction := fun _ _ => Unit
  actionEquiv := fun history i hmover _ =>
    rungActionEquiv i history.1 hmover

/-- The complete history ending at player `0`'s first decision (`s0`). -/
def firstDecision :
    absentMindedGame.base.toArena.HistoryFrom absentMindedGame.base.init :=
  ⟨Rung.s0, Arena.History.nil⟩

/-- Player `0`'s action at `s0`. -/
def stepAction : absentMindedGame.base.Action Rung.s0 := ()

/-- The complete history ending at player `0`'s second decision (`s1`), reached
by taking the single action at `s0`. -/
def secondDecision :
    absentMindedGame.base.toArena.HistoryFrom absentMindedGame.base.init :=
  ⟨Rung.s1, (Arena.History.nil).snoc stepAction⟩

/-- The first decision is genuinely nonterminal. -/
theorem firstDecision_nonterminal :
    ¬ absentMindedGame.base.isTerminal firstDecision.1 := by
  simp [absentMindedGame, base, firstDecision,
    Arena.IsTerminal, rungAction]

/-- The second decision is genuinely nonterminal. -/
theorem secondDecision_nonterminal :
    ¬ absentMindedGame.base.isTerminal secondDecision.1 := by
  simp [absentMindedGame, base, secondDecision,
    Arena.IsTerminal, rungAction]

/-- The first endpoint has an available action. -/
theorem firstDecision_isDecision :
    absentMindedGame.base.toArena.IsDecision firstDecision.1 :=
  absentMindedGame.base.toArena.isDecision_of_not_isTerminal
    firstDecision.1 firstDecision_nonterminal

/-- The second endpoint has an available action. -/
theorem secondDecision_isDecision :
    absentMindedGame.base.toArena.IsDecision secondDecision.1 :=
  absentMindedGame.base.toArena.isDecision_of_not_isTerminal
    secondDecision.1 secondDecision_nonterminal

/-- The single player-`0` decision key. -/
def currentKey : absentMindedGame.DecisionKey :=
  ⟨0, absentMindedGame.representedInfoAt firstDecision 0 rfl
    firstDecision_isDecision⟩

local instance : DecidableEq absentMindedGame.DecisionKey :=
  inferInstanceAs (DecidableEq (Σ _i : Fin 1, {_information : Unit // _}))

-- Erasing the repeated key uses executable equality on the finite fields.
example : ({currentKey} : Finset absentMindedGame.DecisionKey).erase
    ⟨0, absentMindedGame.representedInfoAt secondDecision 0 rfl
      secondDecision_isDecision⟩ = ∅ := by
  native_decide

/-- The availability premise of `FutureDecisionKeysAvailable.afterPlayer` is
satisfied at the first decision: this game has a single decision key, so the
singleton `{currentKey}` already covers every future decision.

Together with the failure after erasure below, this exposes
`NoAbsentMindedness` as the missing hypothesis and prevents the false
generalization that key erasure preserves future availability in every
observed game. -/
theorem futureDecisionKeysAvailable_firstDecision :
    absentMindedGame.FutureDecisionKeysAvailable firstDecision {currentKey} := by
  intro finish suffix i hmover hnonterminal
  refine Finset.mem_singleton.mpr ?_
  have hi : i = 0 := Subsingleton.elim i 0
  subst hi
  rfl

/-- The very same player-`0` decision information state occurs at both `s0` and
`s1` along one complete history: the game is absent-minded.

This recurrence exhibits the failure of the no-absent-mindedness hypothesis
and prevents treating a decision information state as automatically fresh at
successive decision points. -/
theorem infoState_recurs :
    absentMindedGame.infoAt firstDecision 0 rfl
        firstDecision_isDecision =
      absentMindedGame.infoAt secondDecision 0 rfl
        secondDecision_isDecision := rfl

/-- The whole game is a lawful subgame even though its initial information
state recurs later. The initial-root convention is essential for general
imperfect-recall presentations. -/
theorem firstDecision_isLawfulSubgameRoot :
    absentMindedGame.IsLawfulSubgameRoot firstDecision := by
  simpa [firstDecision, absentMindedGame, base] using
    absentMindedGame.init_isLawfulSubgameRoot

/-- The later decision history is not the initial empty history. -/
theorem secondDecision_ne_initial :
    secondDecision ≠
      Arena.HistoryFrom.nil
        absentMindedGame.base.toArena absentMindedGame.base.init := by
  intro heq
  have hstate := congrArg Sigma.fst heq
  change Rung.s1 = Rung.s0 at hstate
  exact Rung.noConfusion hstate

/-- The later proper root is not lawful: it shares its decision information
state with the initial history, which lies outside the later continuation. -/
theorem secondDecision_not_isLawfulSubgameRoot :
    ¬ absentMindedGame.IsLawfulSubgameRoot secondDecision := by
  intro hlawful
  have heq :=
    hlawful.root_information_singleton
      secondDecision_ne_initial
      0 rfl secondDecision_isDecision
      firstDecision rfl firstDecision_isDecision
      infoState_recurs.symm
  exact secondDecision_ne_initial (by
    simpa [firstDecision, absentMindedGame, base] using heq.symm)

/-- **N-3.** No-absent-mindedness fails for player `0`: replaying the single
action from `s0` returns to the identical information state at `s1`.

This is the local missing hypothesis of `afterPlayer`; it prevents the false
generalization that every observed game satisfies
`HasNoAbsentMindedness`. -/
theorem not_hasNoAbsentMindedness :
    ¬ absentMindedGame.HasNoAbsentMindedness 0 := by
  intro h
  exact h firstDecision rfl stepAction Rung.s1 Arena.History.nil
    rfl secondDecision_isDecision rfl

/-- Global no-absent-mindedness also fails.

This records that the global `NoAbsentMindedness` premise needed by
`FutureDecisionKeysAvailable.afterPlayer` is unavailable and prevents silently
generalizing the theorem after deleting that premise. -/
theorem not_noAbsentMindedness :
    ¬ absentMindedGame.NoAbsentMindedness :=
  fun h => not_hasNoAbsentMindedness (h 0)

/-- The absent-minded presentation cannot satisfy signal perfect recall,
because signal recall would rule out recurrence of the same decision
information state along one play. -/
theorem not_eventClockSignalPerfectRecall :
    ¬ absentMindedGame.EventClockSignalPerfectRecall :=
  fun h =>
    not_noAbsentMindedness h.noAbsentMindedness

/-- The freshness premise of `FutureDecisionKeysAvailable.afterPlayer` is
unavailable here.  Starting from the current player decision at `s0` with only
its own key available, a player step would (by `afterPlayer`) claim the erased
set `{currentKey}.erase currentKey` still covers every future decision.  But the
identical key `currentKey` is required again at `s1`, so that claim is false.
Only `NoAbsentMindedness` — which this game lacks — rules this out. -/
theorem afterPlayerConclusionFails :
    ¬ absentMindedGame.FutureDecisionKeysAvailable
        secondDecision
        (({currentKey} : Finset absentMindedGame.DecisionKey).erase currentKey) := by
  intro havail
  have hmem := havail Arena.History.nil 0 rfl
    secondDecision_nonterminal
  rw [Finset.mem_erase] at hmem
  exact hmem.1 rfl

/-- **N-3, premise necessity.** Every hypothesis of
`FutureDecisionKeysAvailable.afterPlayer` other than no-absent-mindedness holds
at `firstDecision`, the decidable-key instance is available, and yet the
conclusion `afterPlayer` would produce is false. Removing the
no-absent-mindedness premise therefore invalidates that generalization.

This says nothing against `afterPlayer` itself, whose no-absent-mindedness
hypothesis this game simply fails to satisfy. -/
theorem afterPlayer_premise_necessity :
    absentMindedGame.FutureDecisionKeysAvailable firstDecision {currentKey} ∧
      absentMindedGame.base.mover firstDecision.1 = some 0 ∧
      ¬ absentMindedGame.NoAbsentMindedness ∧
      ¬ absentMindedGame.FutureDecisionKeysAvailable
          ⟨absentMindedGame.base.next firstDecision.1 stepAction,
            firstDecision.2.snoc stepAction⟩
          (({currentKey} : Finset absentMindedGame.DecisionKey).erase
            currentKey) :=
  ⟨futureDecisionKeysAvailable_firstDecision, rfl, not_noAbsentMindedness,
    afterPlayerConclusionFails⟩

end Examples.AbsentMinded
