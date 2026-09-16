/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Interface.Compilation.Discrete

/-!
# Discrete compilation import boundary

The finite reference compilers and `FiniteLaw`-valued FOSG serialization reuse
discrete equilibrium without importing measurable-kernel execution.
-/

#check GameTree.Kuhn_exists_occurrencePureSPE
#check ExtensiveGame.ObservedChanceGame.finiteKuhn_isNash_iff
#check StochasticGameTree.toObservedChanceGame
#check StochasticGameTree.stochasticHistoryLawFrom_map_payoff
#check FiniteImperfectGame.ObservedChanceCompiler.toObservedChanceGame
#check ExtensiveGame.FOSG.Sequentialization.observedChanceGameCore
#check ExtensiveGame.FOSG.Sequentialization.observedChanceGame
#check ExtensiveGame.FOSG.Sequentialization.observedChanceGame_eq_core
#check ExtensiveGame.FOSG.Sequentialization.rootPresentation
#check ExtensiveGame.FOSG.Sequentialization.FallbackHistoryPolicy
#check ExtensiveGame.FOSG.Sequentialization.MacroPolicyData
#check ExtensiveGame.FOSG.Sequentialization.macroPolicy
#check ExtensiveGame.FOSG.Sequentialization.weakSerialization

namespace Examples.ExtensiveGame.DiscreteCompilationImportBoundary

open ExtensiveGame
open ExtensiveGame.FOSG.Sequentialization

/-- A terminal one-state FOSG used to execute the synthetic-root policy. -/
private def terminalFOSG : ExtensiveGame.FOSG (Fin 1) Nat where
  WorldState := Unit
  PlayerAction := fun _ _ => Empty
  init := FiniteLaw.pure ()
  transition := fun _ action => nomatch action 0
  Observation := fun _ => Unit
  PublicObservation := Unit
  observe := fun _ _ _ _ => ()
  publicObserve := fun _ _ _ => ()
  publicOf := fun _ _ => ()
  observe_public := by intros; rfl
  isTerminal := fun _ => True
  terminal_iff := by
    intro world
    constructor
    · intro _
      exact ⟨fun action => nomatch action 0⟩
    · intro _
      trivial
  payoff := fun _ _ => 0

private instance terminalFOSG_terminalDecidable :
    (world : terminalFOSG.WorldState) →
      Decidable (terminalFOSG.isTerminal world) :=
  fun _ => isTrue trivial

private theorem terminalFOSG_historyState_eq_initial
    (state : terminalFOSG.HistoryState) :
    state =
      ⟨(), ExtensiveGame.FOSG.History.initial
        (G := terminalFOSG) ()⟩ := by
  rcases state with ⟨world, history⟩
  induction history with
  | initial world => cases world; rfl
  | snoc history action nextWorld ih => exact (action 0).elim

private def terminalFOSG_historyStateDecidableEq :
    DecidableEq terminalFOSG.HistoryState :=
  fun left right =>
    isTrue
      ((terminalFOSG_historyState_eq_initial left).trans
        (terminalFOSG_historyState_eq_initial right).symm)

private def terminalFallbackPolicy :
    (game terminalFOSG (fun _ => 0)).toArena.HistoryPolicy
      (game terminalFOSG (fun _ => 0)).init :=
  fun history hnonterminal => by
    cases hstate : history.1 with
    | root => exact ()
    | terminal source hterminal =>
        exfalso
        apply hnonterminal
        rw [hstate]
        exact ⟨fun action => nomatch action⟩
    | player source hsource count hcount collected =>
        exact (hsource trivial).elim
    | chance source hsource action =>
        exact (hsource trivial).elim

private def terminalFallback :
    FallbackHistoryPolicy terminalFOSG (fun _ => 0) where
  policy := terminalFallbackPolicy
  historyDecidableEq := terminalFOSG_historyStateDecidableEq

private def terminalRootHistory :
    (game terminalFOSG (fun _ => 0)).toArena.HistoryFrom
      (game terminalFOSG (fun _ => 0)).init :=
  Arena.HistoryFrom.nil
    (game terminalFOSG (fun _ => 0)).toArena
    (game terminalFOSG (fun _ => 0)).init

example :
    ((initialPolicy terminalFOSG (fun _ => 0) terminalFallback)
        terminalRootHistory
        (root_not_terminal terminalFOSG (fun _ => 0))).atoms.length = 1 := by
  native_decide

end Examples.ExtensiveGame.DiscreteCompilationImportBoundary

/--
error: Unknown constant `StochasticGameTree.fairCoinGame`
-/
#guard_msgs in
#check StochasticGameTree.fairCoinGame

/--
error: Unknown identifier `Examples.ImperfectInformation.tiny`
-/
#guard_msgs in
#check Examples.ImperfectInformation.tiny

/--
error: Unknown constant `FiniteImperfectGame.actionAt_same_info_label`
-/
#guard_msgs in
#check FiniteImperfectGame.actionAt_same_info_label

/--
error: Unknown constant `Arena.pathLaw`
-/
#guard_msgs in
#check Arena.pathLaw

/--
error: Unknown identifier `MeasurableKernelArena`
-/
#guard_msgs in
#check MeasurableKernelArena

/--
error: Unknown identifier `ProbabilityTheory.Kernel`
-/
#guard_msgs in
#check ProbabilityTheory.Kernel
