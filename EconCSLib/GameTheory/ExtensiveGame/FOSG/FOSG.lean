/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Execution.Discrete.KernelArena
import EconCSLib.GameTheory.ExtensiveGame.Relations.Discrete.KernelWeakSimulation
import EconCSLib.GameTheory.ExtensiveGame.Observed.Chance
import EconCSLib.Math.Probability.FiniteLaw.Product

/-!
# EconCSLib.GameTheory.ExtensiveGame.FOSG.FOSG

A compact factored-observation stochastic-game (FOSG) interface.

One macro step consists of a simultaneous joint action followed by a normalized
world-state transition kernel.  Every player receives a private observation,
and each private observation determines the public observation.  Realized
histories are retained explicitly, so two trajectories ending in the same
world state need not have the same private or public view.

`historyKernelArena` is the FOSG-style augmented representation: its states are
complete realized histories and its transitions append one stochastic macro
step.  It is designed to be compared with a turn-taking observed EFG through a
probabilistic weak/stuttering serialization witness.

## Main definitions

* `FOSG` — simultaneous joint actions, stochastic transitions, observations,
  terminality, and payoff.
* `FOSG.History` and `HistoryState` — realized, history-augmented macro states.
* `FOSG.historyKernelArena` — normalized stochastic dynamics on augmented
  histories.
* `FOSG.privateObservations` and `publicObservations` — accumulated views.
* `FOSG.DecisionModel` — information-indexed simultaneous player actions.
* `FOSG.DecisionModel.BehavioralProfile` — independently randomized,
  information-indexed action profiles.
* `FOSG.WeakSerialization` — a chance-consistent, coupling-based
  weak/stuttering implementation by an observed EFG.

## Main results

* `privateObservations_map_publicOf` — private histories determine the public
  history.
* `publicObservations_eq_of_privateObservations_eq` — equality of one player's
  private view implies equality of public views.
* `DecisionModel.jointActionLaw_map_apply` — every behavioral player's
  concrete action marginal is preserved by the independent joint law.
-/

namespace ExtensiveGame

universe uN uU uS uA uO uP

/-- A factored-observation stochastic game.

Terminality is required to agree with emptiness of the simultaneous joint
action type.  This makes the induced `KernelArena` terminal convention agree
with the deterministic `Arena` convention. -/
structure FOSG (N : Type uN) (U : Type uU) where
  /-- Hidden world state. -/
  WorldState : Type uS
  /-- Player `i`'s legal action at a world state. -/
  PlayerAction : N → WorldState → Type uA
  /-- Normalized initial world-state law. -/
  init : FiniteLaw WorldState
  /-- Normalized next-world law after a simultaneous joint action. -/
  transition :
    (world : WorldState) →
      ((i : N) → PlayerAction i world) →
      FiniteLaw WorldState
  /-- Player-specific private signal type. -/
  Observation : N → Type uO
  /-- Public signal type. -/
  PublicObservation : Type uP
  /-- Private signal emitted by one realized macro transition. -/
  observe :
    (i : N) → (world : WorldState) →
      ((j : N) → PlayerAction j world) →
      WorldState → Observation i
  /-- Public signal emitted by one realized macro transition. -/
  publicObserve :
    (world : WorldState) →
      ((j : N) → PlayerAction j world) →
      WorldState → PublicObservation
  /-- Forget the private part of a signal. -/
  publicOf : (i : N) → Observation i → PublicObservation
  /-- Every private signal refines the public signal. -/
  observe_public :
    ∀ (i : N) (world : WorldState)
      (action : (j : N) → PlayerAction j world)
      (nextWorld : WorldState),
      publicOf i (observe i world action nextWorld) =
        publicObserve world action nextWorld
  /-- Explicit terminal predicate at world states. -/
  isTerminal : WorldState → Prop
  /-- Terminality is exactly absence of a simultaneous joint action. -/
  terminal_iff :
    ∀ world,
      isTerminal world ↔
        IsEmpty ((i : N) → PlayerAction i world)
  /-- Payoff vector, meaningful at terminal world states. -/
  payoff : WorldState → N → U

namespace FOSG

variable {N : Type uN} {U : Type uU}

/-- A simultaneous joint action. -/
abbrev JointAction (G : FOSG N U) (world : G.WorldState) : Type _ :=
  (i : N) → G.PlayerAction i world

/-- A realized FOSG history, indexed by its final world state.

The constructors retain realized zero-probability trajectories as syntactic
histories too; the positive atoms of the `FiniteLaw`s
`initialHistoryKernel` and `historyKernelArena.next` identify the
positive-probability ones. -/
inductive History (G : FOSG N U) : G.WorldState → Type _
  | initial (world : G.WorldState) : History G world
  | snoc {world : G.WorldState}
      (history : History G world)
      (action : G.JointAction world)
      (nextWorld : G.WorldState) :
      History G nextWorld

/-- A complete realized FOSG history bundled with its final world state. -/
abbrev HistoryState (G : FOSG N U) :=
  Σ world : G.WorldState, G.History world

/-- The normalized law of initial augmented histories. -/
def initialHistoryKernel (G : FOSG N U) :
    FiniteLaw G.HistoryState :=
  G.init.map fun world => ⟨world, History.initial world⟩

/-- The history-augmented stochastic macro Arena of a FOSG. -/
def historyKernelArena (G : FOSG N U) : KernelArena where
  State := G.HistoryState
  Action := fun history => G.JointAction history.1
  next := fun history action =>
    (G.transition history.1 action).map fun nextWorld =>
      ⟨nextWorld, History.snoc history.2 action nextWorld⟩

/-- The accumulated private observation history of player `i`. -/
def privateObservations (G : FOSG N U) (i : N) :
    {world : G.WorldState} →
      G.History world → List (G.Observation i)
  | _, .initial _ => []
  | _, .snoc history action nextWorld =>
      G.privateObservations i history ++
        [G.observe i _ action nextWorld]

/-- The accumulated public observation history. -/
def publicObservations (G : FOSG N U) :
    {world : G.WorldState} →
      G.History world → List G.PublicObservation
  | _, .initial _ => []
  | _, .snoc history action nextWorld =>
      G.publicObservations history ++
        [G.publicObserve _ action nextWorld]

/-- Mapping every private signal to its public component gives exactly the
public observation history. -/
theorem privateObservations_map_publicOf (G : FOSG N U) (i : N)
    {world : G.WorldState} (history : G.History world) :
    (G.privateObservations i history).map (G.publicOf i) =
      G.publicObservations history := by
  induction history with
  | initial world =>
      simp [privateObservations, publicObservations]
  | @snoc world history action nextWorld ih =>
      simp [privateObservations, publicObservations, ih,
        G.observe_public i world action nextWorld]

/-- If one player's complete private observation histories agree, then the
public histories agree. -/
theorem publicObservations_eq_of_privateObservations_eq
    (G : FOSG N U) (i : N)
    {world₁ world₂ : G.WorldState}
    (history₁ : G.History world₁) (history₂ : G.History world₂)
    (hprivate :
      G.privateObservations i history₁ =
        G.privateObservations i history₂) :
    G.publicObservations history₁ =
      G.publicObservations history₂ := by
  rw [← G.privateObservations_map_publicOf i history₁,
    ← G.privateObservations_map_publicOf i history₂, hprivate]

/-! ### Information-indexed simultaneous decisions -/

/-- Information and legal-action data for simultaneous FOSG decisions.

The raw `FOSG.PlayerAction i world` type may depend on hidden world state.
A sequential compiler must not expose that state merely to make an action
well-typed.  `DecisionModel` supplies the required game-bound interface:
players choose from an abstract action type indexed only by their information
state, together with an equivalence to the concrete legal action at every
nonterminal realized history.

This is the FOSG counterpart of the decision-information fields in
`ObservedGame`. -/
structure DecisionModel (G : FOSG N U) where
  /-- Player `i`'s simultaneous-decision information-state type. -/
  InfoState : N → Type*
  /-- The complete private observation history represented by an information
  state. -/
  infoObserve :
    (i : N) → InfoState i → List (G.Observation i)
  /-- The information state at a nonterminal realized history. -/
  infoAt :
    (history : G.HistoryState) →
      ¬ G.isTerminal history.1 →
      (i : N) → InfoState i
  /-- Decision information projects to the player's complete private
  observation history.  The information state may retain additional memory;
  injectivity is not required. -/
  infoAt_observe :
    ∀ (history : G.HistoryState)
      (hnonterminal : ¬ G.isTerminal history.1) (i : N),
      infoObserve i (infoAt history hnonterminal i) =
        G.privateObservations i history.2
  /-- Abstract action type at one simultaneous-decision information state. -/
  InfoAction : (i : N) → InfoState i → Type*
  /-- Abstract information actions are exactly the concrete legal actions at
  each represented nonterminal world history. -/
  actionEquiv :
    ∀ (history : G.HistoryState)
      (hnonterminal : ¬ G.isTerminal history.1) (i : N),
      InfoAction i (infoAt history hnonterminal i) ≃
        G.PlayerAction i history.1

namespace DecisionModel

variable {G : FOSG N U}

/-- Equal FOSG decision information states force equal public observation
histories. -/
theorem publicObservations_eq_of_infoAt_eq
    (D : G.DecisionModel) (i : N)
    (history₁ history₂ : G.HistoryState)
    (hnonterminal₁ : ¬ G.isTerminal history₁.1)
    (hnonterminal₂ : ¬ G.isTerminal history₂.1)
    (hsame :
      D.infoAt history₁ hnonterminal₁ i =
        D.infoAt history₂ hnonterminal₂ i) :
    G.publicObservations history₁.2 =
      G.publicObservations history₂.2 := by
  apply G.publicObservations_eq_of_privateObservations_eq i
  calc
    G.privateObservations i history₁.2 =
        D.infoObserve i (D.infoAt history₁ hnonterminal₁ i) :=
      (D.infoAt_observe history₁ hnonterminal₁ i).symm
    _ = D.infoObserve i (D.infoAt history₂ hnonterminal₂ i) := by
      rw [hsame]
    _ = G.privateObservations i history₂.2 :=
      D.infoAt_observe history₂ hnonterminal₂ i

/-- A behavioral strategy chooses a normalized abstract-action law at every
information state of one player. -/
abbrev BehavioralStrategy (D : G.DecisionModel) (i : N) :=
  (information : D.InfoState i) → FiniteLaw (D.InfoAction i information)

/-- A profile of information-indexed behavioral strategies. -/
abbrev BehavioralProfile (D : G.DecisionModel) :=
  (i : N) → D.BehavioralStrategy i

/-- Unilateral deviation of a FOSG behavioral profile. -/
def BehavioralProfile.deviate [DecidableEq N]
    (D : G.DecisionModel)
    (profile : D.BehavioralProfile) (who : N)
    (deviation : D.BehavioralStrategy who) :
    D.BehavioralProfile :=
  Function.update profile who deviation

@[simp]
theorem BehavioralProfile.deviate_same [DecidableEq N]
    (D : G.DecisionModel)
    (profile : D.BehavioralProfile) (who : N)
    (deviation : D.BehavioralStrategy who) :
    BehavioralProfile.deviate D profile who deviation who =
      deviation := by
  simp [BehavioralProfile.deviate]

@[simp]
theorem BehavioralProfile.deviate_of_ne [DecidableEq N]
    (D : G.DecisionModel)
    (profile : D.BehavioralProfile) (who : N)
    (deviation : D.BehavioralStrategy who)
    {other : N} (hne : other ≠ who) :
    BehavioralProfile.deviate D profile who deviation other =
      profile other := by
  simp [BehavioralProfile.deviate, hne]

end DecisionModel

namespace DecisionModel

variable {k : ℕ} {G : FOSG (Fin k) U}

/-- The simultaneous joint-action law induced by an independently randomized
finite-player behavioral profile at one nonterminal augmented history.

The `DecisionModel.actionEquiv` maps each player's abstract
information-indexed action back to the concrete world-indexed action type;
`FiniteLaw.finPi` then forms their independent dependent product. -/
def jointActionLaw
    (D : G.DecisionModel)
    (profile : D.BehavioralProfile)
    (history : G.HistoryState)
    (hnonterminal : ¬ G.isTerminal history.1) :
    FiniteLaw (G.JointAction history.1) :=
  FiniteLaw.finPi k fun i =>
    (profile i (D.infoAt history hnonterminal i)).map
      (D.actionEquiv history hnonterminal i)

/-- Each player's marginal of the induced joint-action law is exactly that
player's behavioral action law transported to concrete actions. -/
theorem jointActionLaw_map_apply
    (D : G.DecisionModel)
    (profile : D.BehavioralProfile)
    (history : G.HistoryState)
    (hnonterminal : ¬ G.isTerminal history.1)
    (i : Fin k) :
    ((D.jointActionLaw profile history hnonterminal).map
        (fun jointAction => jointAction i)).Equivalent
      ((profile i (D.infoAt history hnonterminal i)).map
        (D.actionEquiv history hnonterminal i)) := by
  exact
    FiniteLaw.finPi_map_apply k
      (fun j =>
        (profile j (D.infoAt history hnonterminal j)).map
          (D.actionEquiv history hnonterminal j))
      i

/-- Compile an information-indexed finite-player behavioral profile to the
terminal-aware randomized policy of the history-augmented FOSG kernel Arena.
-/
def behavioralHistoryPolicy
    (D : G.DecisionModel)
    (profile : D.BehavioralProfile) :
    G.historyKernelArena.Policy :=
  fun history hactions =>
    have hnonterminal : ¬ G.isTerminal history.1 := by
      intro hterminal
      exact hactions ((G.terminal_iff history.1).mp hterminal)
    D.jointActionLaw profile history hnonterminal

end DecisionModel

/-- The initial augmented-history law is normalized. -/
@[simp]
theorem initialHistoryKernel_normalized (G : FOSG N U) :
    FiniteLaw.totalWeight G.initialHistoryKernel.atoms = 1 :=
  G.initialHistoryKernel.normalized

/-- Every augmented macro-transition law is normalized. -/
@[simp]
theorem historyKernelArena_next_normalized (G : FOSG N U)
    (history : G.HistoryState)
    (action : G.historyKernelArena.Action history) :
    FiniteLaw.totalWeight
      (G.historyKernelArena.next history action).atoms = 1 :=
  (G.historyKernelArena.next history action).normalized

/-- Terminality of an augmented FOSG history is exactly terminality of its
final world state. -/
theorem historyKernelArena_isTerminal_iff (G : FOSG N U)
    (history : G.HistoryState) :
    IsEmpty (G.historyKernelArena.Action history) ↔
      G.isTerminal history.1 :=
  (G.terminal_iff history.1).symm

/-- Terminal payoff represented at an augmented FOSG history.

Nonterminal histories map to `none`, so bounded execution never exposes the
arbitrary nonterminal filler value of `FOSG.payoff`. -/
def stoppedPayoffAtHistory
    (G : FOSG N U)
    [(world : G.WorldState) → Decidable (G.isTerminal world)]
    (history : G.HistoryState) :
    Option (N → U) :=
  if G.isTerminal history.1 then
    some (G.payoff history.1)
  else
    none

@[simp]
theorem stoppedPayoffAtHistory_of_terminal
    (G : FOSG N U)
    [(world : G.WorldState) → Decidable (G.isTerminal world)]
    (history : G.HistoryState)
    (hterminal : G.isTerminal history.1) :
    G.stoppedPayoffAtHistory history =
      some (G.payoff history.1) := by
  simp [stoppedPayoffAtHistory, hterminal]

@[simp]
theorem stoppedPayoffAtHistory_of_not_terminal
    (G : FOSG N U)
    [(world : G.WorldState) → Decidable (G.isTerminal world)]
    (history : G.HistoryState)
    (hnonterminal : ¬ G.isTerminal history.1) :
    G.stoppedPayoffAtHistory history = none := by
  simp [stoppedPayoffAtHistory, hnonterminal]

/-! ### Probabilistic weak serialization into an observed EFG -/

/-- A FOSG serialization by a turn-taking observed chance EFG.

Each FOSG macro action is implemented by a positive-fuel target history
policy.  `ObservedChanceGame.ChanceConsistent` forces that policy to use the
target's declared chance kernel at every chance node, while
`ProbabilisticWeakSimulation` requires an exact relation-supported coupling of
the FOSG successor law and target endpoint law.

The remaining fields preserve the observation hierarchy, terminal payoffs,
and a caller-chosen source predicate of declared continuation roots at related
macro boundaries.  The predicate is presentation data, not an intrinsic
certificate of standard EFG subgames.  This is intentionally weaker than
strict isomorphism: one FOSG macro step may serialize into several player,
administrative, and chance steps. -/
structure WeakSerialization
    (G : FOSG N U) (H : ObservedChanceGame N U)
    [(state : H.observed.base.State) →
      Decidable (H.observed.base.isTerminal state)] where
  /-- Coupling-based progressing weak simulation of augmented FOSG histories
  by complete target EFG histories. -/
  simulation :
    KernelArena.ProbabilisticWeakSimulation
      G.historyKernelArena
      H.observed.base.toArena
      H.observed.base.init
      H.ChanceConsistent
  /-- External target continuation roots used by this serialization
  certificate. This presentation is analysis metadata, not part of `H`. -/
  targetRoots : H.observed.RootPresentation
  /-- The initial FOSG history law is matched by a finite,
  chance-consistent target initialization execution. -/
  match_init :
    PSigma fun policy :
        H.observed.base.toArena.StochasticHistoryPolicy
          H.observed.base.init =>
      PSigma fun fuel : ℕ =>
        PSigma fun _hchance : H.ChanceConsistent policy =>
        FiniteLaw.RelCoupling simulation.Rel
          G.initialHistoryKernel
          (H.observed.base.toArena.stochasticHistoryLawFrom
            policy
            (Arena.HistoryFrom.nil
              H.observed.base.toArena H.observed.base.init)
            fuel)
  /-- Inject the accumulated FOSG private view into the target observation
  type.  Surjectivity is intentionally not required: synthetic root and
  administrative target observations need not represent FOSG macro
  boundaries. -/
  observationMap :
    (i : N) →
      List (G.Observation i) → H.observed.Observation i
  /-- The private-view representation loses no source information. -/
  observationMap_injective :
    ∀ i : N, Function.Injective (observationMap i)
  /-- Private observations commute with the simulation relation. -/
  map_observe :
    ∀ (i : N) (source : G.HistoryState)
      (target :
        H.observed.base.toArena.HistoryFrom H.observed.base.init),
      simulation.Rel source target →
        observationMap i
            (G.privateObservations i source.2) =
          H.observed.observe i target
  /-- Inject the accumulated FOSG public view into the target public
  observation type. -/
  publicMap :
    List G.PublicObservation → H.observed.PublicObservation
  /-- The public-view representation loses no source information. -/
  publicMap_injective :
    Function.Injective publicMap
  /-- Public observations commute with the simulation relation. -/
  map_publicObserve :
    ∀ (source : G.HistoryState)
      (target :
        H.observed.base.toArena.HistoryFrom H.observed.base.init),
      simulation.Rel source target →
        publicMap (G.publicObservations source.2) =
          H.observed.publicObserve target
  /-- The private-to-public forgetful maps commute. -/
  map_publicOf :
    ∀ (i : N) (privateView : List (G.Observation i)),
      publicMap (privateView.map (G.publicOf i)) =
        H.observed.publicOf i (observationMap i privateView)
  /-- Terminal payoff vectors agree at related macro boundaries. -/
  map_terminalPayoff :
    ∀ (source : G.HistoryState)
      (target :
        H.observed.base.toArena.HistoryFrom H.observed.base.init),
      simulation.Rel source target →
      G.isTerminal source.1 →
        H.observed.base.payoff target.1 =
          G.payoff source.1
  /-- Source-side caller-declared FOSG macro boundaries. -/
  IsDeclaredMacroRoot : G.HistoryState → Prop
  /-- Declared roots correspond at related macro boundaries. -/
  map_declaredMacroRoot :
    ∀ (source : G.HistoryState)
      (target :
        H.observed.base.toArena.HistoryFrom H.observed.base.init),
      simulation.Rel source target →
        (IsDeclaredMacroRoot source ↔
          targetRoots.IsRoot target)

namespace WeakSerialization

variable {G : FOSG N U} {H : ObservedChanceGame N U}
  [(state : H.observed.base.State) →
    Decidable (H.observed.base.isTerminal state)]

/-- Forget probability weights from a FOSG serialization and retain an
ordinary weak simulation of all positive-probability realized paths. -/
def toSupportWeakSimulation
    (S : G.WeakSerialization H) :
    G.historyKernelArena.supportArena.WeakSimulation
      (H.observed.base.toArena.unfoldFrom H.observed.base.init) :=
  S.simulation.toSupportWeakSimulation

/-- Every positive-probability FOSG macro transition is implemented by at
least one target EFG transition. -/
theorem toSupportWeakSimulation_progressing
    (S : G.WeakSerialization H) :
    S.toSupportWeakSimulation.Progressing :=
  S.simulation.toSupportWeakSimulation_progressing

/-- Related FOSG and EFG macro boundaries carry identical terminal payoff
vectors after the declared representation map. -/
theorem terminalPayoff_eq (S : G.WeakSerialization H)
    (source : G.HistoryState)
    (target :
      H.observed.base.toArena.HistoryFrom H.observed.base.init)
    (hrelated : S.simulation.Rel source target)
    (hterminal : G.isTerminal source.1) :
    H.observed.base.payoff target.1 = G.payoff source.1 :=
  S.map_terminalPayoff source target hrelated hterminal

/-- Related macro boundaries preserve caller-declared roots in both
directions. -/
theorem declaredMacroRoot_iff (S : G.WeakSerialization H)
    (source : G.HistoryState)
    (target :
      H.observed.base.toArena.HistoryFrom H.observed.base.init)
    (hrelated : S.simulation.Rel source target) :
    S.IsDeclaredMacroRoot source ↔
      S.targetRoots.IsRoot target :=
  S.map_declaredMacroRoot source target hrelated

end WeakSerialization

end FOSG

end ExtensiveGame
