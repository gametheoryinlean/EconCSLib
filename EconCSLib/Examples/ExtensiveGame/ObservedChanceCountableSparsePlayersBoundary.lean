/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Simulation.Presentation.Chance.Countable

/-!
# Countable observed semantics with an uncountable player identifier type

This regression guards the cardinality-minimal boundary of an effective
countable observed-chance presentation.

The ambient player type is `Unit ⊕ ℝ`, hence uncountable. Only the distinguished
left player ever moves. Every real-indexed unused player nevertheless has an
uncountable `ℝ` information fiber, and every such information point has an
uncountable `ℝ` action fiber.

Those declared points are unreachable, so the reachable player-information
carrier is still a singleton. Histories and history/actions have explicit
encoders and partial decoders. Analytic kernels are supplied separately, and
their existing compilation certificate gives exact one-step compatibility.
Unused player identifiers, information points, and actions are never
enumerated or used to invent fallback values.
-/

open MeasureTheory ProbabilityTheory

namespace Examples.ObservedChanceCountableSparsePlayersBoundary

open ExtensiveGame
open MeasurableKernelArena

/-- An uncountable ambient identifier type with one distinguished active
player. -/
abbrev Player := Unit ⊕ ℝ

/-- The sole player who occurs as a mover. -/
def activePlayer : Player :=
  .inl ()

/-- A one-decision game state space. -/
inductive Node
  | decision
  | terminal

/-- The decision node has one action and the terminal node has none. -/
def nodeAction : Node → Type
  | .decision => Unit
  | .terminal => Empty

/-- The unique decision action reaches the terminal node. -/
def nodeNext : (state : Node) → nodeAction state → Node
  | .decision, _ => .terminal
  | .terminal, action => nomatch action

/-- Only the distinguished left player moves. -/
def nodeMover : Node → Option Player
  | .decision => some activePlayer
  | .terminal => none

/-- The underlying one-decision extensive game. -/
def base : ExtensiveGame Player Unit where
  State := Node
  Action := nodeAction
  next := nodeNext
  init := .decision
  mover := nodeMover
  payoff := fun _ _ => ()

/-- The active player has one information point; every unused real-indexed
player has an uncountable declared information fiber. -/
def sparseInfoState : Player → Type
  | .inl _ => Unit
  | .inr _ => ℝ

/-- Every unused information point also has an uncountable declared action
fiber, despite never being queried by execution. -/
def sparseInfoAction :
    (i : Player) → sparseInfoState i → Type
  | .inl _, _ => Unit
  | .inr _, _ => ℝ

/-- Recover the unique sparse information state at any player-labelled
history. -/
def sparseInformationAt
    (history : base.toArena.HistoryFrom base.init)
    (i : Player)
    (hmover : base.mover history.1 = some i)
    (_hdecision : base.toArena.IsDecision history.1) :
    sparseInfoState i := by
  change nodeMover history.1 = some i at hmover
  cases hstate : history.1 with
  | decision =>
      rw [hstate] at hmover
      simp only [nodeMover, Option.some.injEq] at hmover
      subst i
      exact ()
  | terminal =>
      rw [hstate] at hmover
      exact (Option.some_ne_none i hmover.symm).elim

/-- The sparse abstract action is exactly the unique legal concrete action at
the only player-controlled history. -/
def sparseActionEquiv
    (history : base.toArena.HistoryFrom base.init)
    (i : Player)
    (hmover : base.mover history.1 = some i)
    (hdecision : base.toArena.IsDecision history.1) :
    sparseInfoAction i
        (sparseInformationAt history i hmover hdecision) ≃
      base.Action history.1 := by
  change nodeMover history.1 = some i at hmover
  cases hstate : history.1 with
  | decision =>
      rw [hstate] at hmover
      simp only [nodeMover, Option.some.injEq] at hmover
      subst i
      change Unit ≃ Unit
      exact Equiv.refl Unit
  | terminal =>
      rw [hstate] at hmover
      exact (Option.some_ne_none i hmover.symm).elim

/-- The observed game with uncountably many unused player identifiers. -/
def observed : ObservedGame Player Unit where
  base := base
  Observation := fun _ => Unit
  PublicObservation := Unit
  observe := fun _ _ => ()
  publicObserve := fun _ => ()
  publicOf := fun _ _ => ()
  observe_public := fun _ _ => rfl
  InfoState := sparseInfoState
  infoObserve := fun _ _ => ()
  infoAt := sparseInformationAt
  infoAt_observe := fun _ _ _ _ => rfl
  InfoAction := sparseInfoAction
  actionEquiv := sparseActionEquiv

/-- The one-decision game has no chance nodes. -/
theorem noChance :
    observed.base.NoChance := by
  intro state hnonterminal
  cases state with
  | decision =>
      exact ⟨activePlayer, rfl⟩
  | terminal =>
      exact
        (hnonterminal
          (show IsEmpty (observed.base.Action Node.terminal) from
            ⟨Empty.elim⟩)).elim

/-- The sparse-player observed game through the chance-aware API. -/
def game : ObservedChanceGame Player Unit :=
  { observed := observed
    chanceKernel := by
      intro history hchance
      cases hstate : history.1 with
      | decision =>
          have hmover := hchance.1
          change nodeMover history.1 = none at hmover
          rw [hstate] at hmover
          exact (Option.some_ne_none activePlayer hmover).elim
      | terminal =>
          apply (hchance.2 ?_).elim
          rw [hstate]
          exact
            (show IsEmpty
                (observed.base.Action Node.terminal) from
              ⟨Empty.elim⟩) }

/-- The initial complete history. -/
def initialHistory :
    game.observed.base.toArena.HistoryFrom game.observed.base.init :=
  Arena.HistoryFrom.nil
    game.observed.base.toArena
    game.observed.base.init

/-- The unique terminal complete history. -/
def terminalHistory :
    game.observed.base.toArena.HistoryFrom game.observed.base.init :=
  ⟨Node.terminal, initialHistory.2.snoc ()⟩

/-- Executable terminal decisions for the two-node model. -/
instance terminalDecidable
    (state : game.observed.base.State) :
    Decidable (game.observed.base.isTerminal state) := by
  cases state with
  | decision => exact isFalse fun hterminal => hterminal.false ()
  | terminal => exact isTrue ⟨Empty.elim⟩

/-- Every complete history is either the initial or terminal history. -/
theorem history_classify
    (history :
      game.observed.base.toArena.HistoryFrom
        game.observed.base.init) :
    history = initialHistory ∨ history = terminalHistory := by
  rcases history with ⟨state, path⟩
  refine Arena.History.rec
    (motive := fun state path =>
      (⟨state, path⟩ :
        game.observed.base.toArena.HistoryFrom
          game.observed.base.init) =
          initialHistory ∨
        (⟨state, path⟩ :
          game.observed.base.toArena.HistoryFrom
            game.observed.base.init) =
          terminalHistory)
    ?_ ?_ path
  · exact Or.inl rfl
  · intro state path action ih
    rcases ih with hinitial | hterminal
    · cases hinitial
      cases action
      exact Or.inr rfl
    · cases hterminal
      exact Empty.elim action

/-- A two-point cover of complete histories. -/
def historyCover :
    Fin 2 →
      game.observed.base.toArena.HistoryFrom
        game.observed.base.init
  | 0 => initialHistory
  | 1 => terminalHistory

theorem historyCover_surjective :
    Function.Surjective historyCover := by
  intro history
  rcases history_classify history with hinitial | hterminal
  · exact ⟨0, hinitial.symm⟩
  · exact ⟨1, hterminal.symm⟩

/-- An explicit encoder/decoder for complete histories. -/
instance historyEncoding :
    Encodable
      (game.observed.base.toArena.HistoryFrom
        game.observed.base.init) where
  encode history := match history.1 with
    | .decision => 0
    | .terminal => 1
  decode
    | 0 => some initialHistory
    | 1 => some terminalHistory
    | _ => none
  encodek history := by
    rcases history_classify history with hinitial | hterminal
    · subst history; rfl
    · subst history; rfl

/-- A singleton cover of the total complete-history/local-action carrier. The
terminal history contributes no element. -/
def completeHistoryActionCover :
    Unit →
      ObservedChanceGame.CompleteHistoryAction game :=
  fun _ => ⟨initialHistory, ()⟩

theorem completeHistoryActionCover_surjective :
    Function.Surjective completeHistoryActionCover := by
  intro historyAction
  rcases historyAction with ⟨history, action⟩
  rcases history_classify history with hinitial | hterminal
  · subst history
    change Unit at action
    cases action
    exact ⟨(), rfl⟩
  · subst history
    change Empty at action
    exact Empty.elim action

/-- The action-bundle decoder has one value and fails at every other code. -/
instance completeHistoryActionEncoding :
    Encodable
      (ObservedChanceGame.CompleteHistoryAction game) where
  encode _ := 0
  decode
    | 0 => some (completeHistoryActionCover ())
    | _ => none
  encodek historyAction := by
    obtain ⟨value, hvalue⟩ :=
      completeHistoryActionCover_surjective historyAction
    cases value
    cases hvalue
    rfl

/-- The ambient player identifier type is genuinely not countable. -/
theorem player_not_countable :
    ¬ Countable Player := by
  intro hcountable
  letI : Countable Player := hcountable
  have hinjective :
      Function.Injective
        (fun value : ℝ => (Sum.inr value : Player)) :=
    Sum.inr_injective
  have hreal : Countable ℝ :=
    hinjective.countable
  exact (not_countable (α := ℝ)) hreal

/-- Each unused player has an uncountable declared information fiber. -/
theorem unused_information_not_countable
    (identifier : ℝ) :
    ¬ Countable
      (game.observed.InfoState
        (Sum.inr identifier : Player)) := by
  change ¬ Countable ℝ
  exact not_countable

/-- Each unreachable information point of an unused player has an uncountable
declared action fiber. -/
theorem unused_action_not_countable
    (identifier information : ℝ) :
    ¬ Countable
      (game.observed.InfoAction
        (Sum.inr identifier : Player)
        information) := by
  change ¬ Countable ℝ
  exact not_countable

/-- The total original player-information carrier is uncountable, confirming
that the constructor now counts only its reachable subtype. -/
theorem player_information_not_countable :
    ¬ Countable
      (ObservedChanceGame.PlayerInformationPoint game) := by
  intro hcountable
  letI :
      Countable
        (ObservedChanceGame.PlayerInformationPoint game) :=
    hcountable
  let injection :
      ℝ → ObservedChanceGame.PlayerInformationPoint game :=
    fun information =>
      ⟨(Sum.inr 0 : Player), information⟩
  have hinjective : Function.Injective injection := by
    intro information₁ information₂ heq
    exact eq_of_heq (Sigma.mk.inj_iff.mp heq).2
  exact
    (not_countable (α := ℝ))
      hinjective.countable

/-- The total original dependent information-action carrier is likewise
uncountable, so neither of the former player-side countability hypotheses is
available. -/
theorem player_information_action_not_countable :
    ¬ Countable
      (ObservedChanceGame.PlayerInformationAction game) := by
  intro hcountable
  letI :
      Countable
        (ObservedChanceGame.PlayerInformationAction game) :=
    hcountable
  let injection :
      ℝ → ObservedChanceGame.PlayerInformationAction game :=
    fun action => by
      change
        Σ information : (Σ i : Player, sparseInfoState i),
          sparseInfoAction information.1 information.2
      exact
        ⟨⟨(Sum.inr 0 : Player), (0 : ℝ)⟩, action⟩
  have hinjective : Function.Injective injection := by
    intro action₁ action₂ heq
    exact eq_of_heq (Sigma.mk.inj_iff.mp heq).2
  exact
    (not_countable (α := ℝ))
      hinjective.countable

/-- The unique behavioral profile at the sole inhabited information point. -/
def profile :
    game.observed.BehavioralProfile := by
  intro i information
  rcases information with ⟨information, _hwitness⟩
  change sparseInfoState i at information
  change FiniteLaw (sparseInfoAction i information)
  cases i with
  | inl value =>
      cases value
      cases information
      exact FiniteLaw.pure ()
  | inr value =>
      exfalso
      rcases _hwitness with ⟨witness⟩
      have hmover := witness.mover
      change nodeMover witness.history.1 = some (.inr value) at hmover
      cases hstate : witness.history.1 <;>
        simp [nodeMover, activePlayer, hstate] at hmover

/-- The canonical reachable player point. -/
private def activeInformation :
    ObservedChanceGame.ReachablePlayerInformation game :=
  ObservedChanceGame.reachablePlayerInformationAt game initialHistory
    activePlayer rfl (fun hterminal => hterminal.false ())

/-- The tagged-information encoder does not inspect any real-valued unused
player data. Its decoder explicitly enumerates the terminal and active tags. -/
instance taggedInformationEncoding :
    Encodable (ObservedChanceGame.CountableInformation game) where
  encode
    | .terminal => 0
    | .player _ => 1
    | .chance _ _ => 2
  decode
    | 0 => some .terminal
    | 1 => some (.player activeInformation)
    | _ => none
  encodek information := by
    cases information with
    | terminal => rfl
    | player information =>
        rcases information with
          ⟨⟨i, information⟩, ⟨history, hmover, hdecision, _hinformation⟩⟩
        rcases history_classify history with hinitial | hterminal
        · subst history
          have hi : i = activePlayer := (Option.some.inj hmover).symm
          subst i
          change Unit at information
          cases information
          rfl
        · subst history
          rcases hdecision with ⟨action⟩
          exact Empty.elim action
    | chance history hchance =>
        cases hstate : history.1 with
        | decision =>
            have hmover := hchance.1
            change nodeMover history.1 = none at hmover
            rw [hstate] at hmover
            exact (Option.some_ne_none activePlayer hmover).elim
        | terminal =>
            apply (hchance.2 ?_).elim
            rw [hstate]
            exact ⟨Empty.elim⟩

local instance : DecidableEq (ObservedChanceGame.CountableInformation game) :=
  Encodable.decidableEqOfEncodable _

/-- Reachability is decided by the player tag, without equality tests or an
enumeration of the unused real-valued player identifiers. -/
private def reachableDecision
    (information : ObservedChanceGame.PlayerInformationPoint game) :
    Decidable (ObservedChanceGame.IsReachablePlayerInformation game information) := by
  rcases information with ⟨i, information⟩
  cases i with
  | inl value =>
      cases value
      change Unit at information
      cases information
      exact isTrue ⟨initialHistory, rfl, ⟨()⟩, rfl⟩
  | inr value =>
      exact isFalse (by
        rintro ⟨history, hmover, _hdecision, _hinformation⟩
        change nodeMover history.1 = some (.inr value) at hmover
        cases hstate : history.1 <;>
          simp [nodeMover, activePlayer, hstate] at hmover)

/-- Missing information produces explicit lookup failure, not a terminal tag. -/
example :
    (ObservedChanceGame.CountablePresentation.informationOfPlayerInformation
      game reachableDecision ⟨(.inr 0 : Player), (0 : ℝ)⟩).isNone = true := by
  native_decide

/-- Matching realization executes using equality from the explicit encoding. -/
example :
    (ObservedChanceGame.CountablePresentation.realizedAction game initialHistory
      (fun hterminal => hterminal.false ())
      (ObservedChanceGame.CountablePresentation.playerAction
        game activeInformation ())).isSome = true := by
  native_decide

/-- Native execution uses the explicit encoder and terminal decision. -/
example :
    Encodable.encode
      (ObservedChanceGame.CountablePresentation.informationAtHistory
        game initialHistory) = 1 ∧
    Encodable.encode
      (ObservedChanceGame.CountablePresentation.informationAtHistory
        game terminalHistory) = 0 := by
  native_decide

/-- The one-element action enumeration has explicit lookup failure. -/
example :
    (Encodable.decode
      (α := ObservedChanceGame.CompleteHistoryAction game) 1).isNone = true := by
  native_decide

variable (presentation : game.AnalyticPresentation)

/-- The canonical tagged information carrier is countable even though the
ambient player type and the total original information carrier are not.
This instance is derived from the explicit encoder above, not from a chosen
equivalence or a countability proof. -/
theorem tagged_information_countable :
    Countable (ObservedChanceGame.CountableInformation game) :=
  inferInstance

/-- Compilation is still exactly the original concrete history-action kernel
at every event prefix. -/
theorem compiled_kernel_exact
    (time : ℕ)
    (events : game.AnalyticHistoryArena.EventPrefix time) :
    (presentation.toPolicy profile).toEventHistoryActionPolicy.kernel
        time events =
      (ObservedChanceGame.BehavioralProfile.toHistoryKernelPolicy
        game profile).toMeasurable.kernel
        (MeasurableKernelArena.latestEventState time events) :=
  presentation.compiled_kernel profile time events

end Examples.ObservedChanceCountableSparsePlayersBoundary
