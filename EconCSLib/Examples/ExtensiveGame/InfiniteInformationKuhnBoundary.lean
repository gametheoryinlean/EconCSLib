/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Interface.Equilibrium.Discrete

/-!
# Bounded Kuhn realization with infinite declared information

This one-player game has one represented root information state but declares
`ℕ` as its raw information carrier. A direct recall certificate gives
finite-rational mixed-to-behavioral equality at every finite fuel. The sole
represented coordinate is still finite, so this example does not separate
the theorem from `FiniteKuhnHypotheses`, which counts represented coordinates.
-/

namespace Examples.InfiniteInformationKuhnBoundary

open ExtensiveGame

/-- Root and terminal endpoints. -/
inductive State
  | root
  | terminal

/-- Two root actions and no terminal action. -/
def action : State → Type
  | .root => Bool
  | .terminal => Empty

def next : (state : State) → action state → State
  | .root, _ => .terminal
  | .terminal, impossible => nomatch impossible

def mover : State → Option Unit
  | .root => some ()
  | .terminal => none

/-- One-step endpoint-payoff game. -/
def base : ExtensiveGame Unit Unit where
  State := State
  Action := action
  next := next
  init := .root
  mover := mover
  payoff := fun _ _ => ()

/-- Only information state `0` is represented, while all natural numbers are
raw information values; strategies use only represented coordinates. -/
def observed : ObservedGame Unit Unit where
  base := base
  Observation := fun _ => Unit
  PublicObservation := Unit
  observe := fun _ _ => ()
  publicObserve := fun _ => ()
  publicOf := fun _ _ => ()
  observe_public := fun _ _ => rfl
  InfoState := fun _ => ℕ
  infoObserve := fun _ _ => ()
  infoAt := fun _history _player _hmover _hnonterminal => 0
  infoAt_observe := fun _ _ _ _ => rfl
  InfoAction := fun _ _information => Bool
  actionEquiv := by
    intro history player hmover _hnonterminal
    cases player
    cases hstate : history.1 with
    | root =>
        change Bool ≃ Bool
        exact Equiv.refl Bool
    | terminal =>
        change mover history.1 = some () at hmover
        rw [hstate] at hmover
        exact (Option.some_ne_none () hmover.symm).elim

/-- No chance-controlled history exists. -/
def game : ObservedChanceGame Unit Unit where
  observed := observed
  chanceKernel := by
    intro history hchance
    cases hstate : history.1 with
    | root =>
        have hmover := hchance.1
        change mover history.1 = none at hmover
        rw [hstate] at hmover
        exact (Option.some_ne_none () hmover).elim
    | terminal =>
        apply (hchance.2 ?_).elim
        rw [hstate]
        exact ⟨Empty.elim⟩

local instance terminalDecidable :
    (state : game.observed.base.State) →
      Decidable (game.observed.base.isTerminal state) :=
  fun state => match state with
    | .root => isFalse (fun h => h.false false)
    | .terminal => isTrue ⟨Empty.elim⟩

local instance observedTerminalDecidable :
    (state : observed.base.State) →
      Decidable (observed.base.isTerminal state) :=
  terminalDecidable

example : decide (game.observed.base.isTerminal .root) = false ∧
    decide (observed.base.isTerminal .terminal) = true := by
  decide +kernel

/-- Every represented decision is the root and has no prior personal
decision. -/
def recallCertificate : observed.RecallCertificate where
  remembered := fun _player _information => []
  remembered_infoAt := by
    intro player history hmover _hnonterminal
    cases player
    rcases history with ⟨state, path⟩
    cases path with
    | nil =>
        rfl
    | @snoc previous path previousAction =>
        cases previous with
        | root =>
            change mover (next .root previousAction) = some () at hmover
            simp [next, mover] at hmover
        | terminal =>
            exact Empty.elim previousAction

/-- The raw information carrier is infinite. This says nothing about
finiteness of the represented decision carrier used by `FiniteKuhnHypotheses`. -/
theorem infoState_not_finite :
    ¬ Finite (observed.InfoState ()) := by
  change ¬ Finite ℕ
  exact not_finite_iff_infinite.mpr inferInstance

/-- A finite rational mixed law over the represented contingent table. -/
def mixedProfile : observed.MixedProfile :=
  fun _player => FiniteLaw.pure (fun _information => false)

local instance actionDecidable
    (i : Unit) (information : observed.RepresentedInfo i) :
    DecidableEq (observed.InfoAction i information.1) := by
  cases i
  change DecidableEq Bool
  infer_instance

local instance gameActionDecidable
    (i : Unit) (information : game.observed.RepresentedInfo i) :
    DecidableEq (game.observed.InfoAction i information.1) := by
  cases i
  change DecidableEq Bool
  infer_instance

/-- Empty absolute root history. -/
def root : observed.base.History :=
  Arena.HistoryFrom.nil base.toArena base.init

/-- The finite-law theorem applies at every bounded horizon despite the
infinite raw information carrier.  The caller supplies the behavioral
assessment used only at zero-mass personal histories. -/
theorem bounded_history_realization
    (offPath : observed.BehavioralProfile)
    (fuel : ℕ) :
    (game.mixedStoppedHistoryLawFrom
      mixedProfile root fuel).Equivalent
      (observed.base.toArena.stochasticHistoryLawFrom
        (ObservedChanceGame.BehavioralProfile.toHistoryPolicy game
          (recallCertificate.behavioralizeMixedProfileFrom
            observed root mixedProfile offPath))
        root fuel) :=
  game.finiteLawMixedToBehavioral_boundedHistoryLaw
    recallCertificate mixedProfile offPath root fuel

end Examples.InfiniteInformationKuhnBoundary
