/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.FOSG.Sequentialization.Trajectory

/-!
# EconCSLib.GameTheory.ExtensiveGame.FOSG.Sequentialization.Witness

Initialization laws and the complete weak-serialization witness.
-/

namespace ExtensiveGame.FOSG.Sequentialization

universe uU uSA uO uP

variable {n : ℕ} {U : Type uU}
  (G : FOSG.{0, uU, uSA, uSA, uO, uP} (Fin (n + 1)) U)

local instance witnessHistoryKernelActionEmptinessDecidable
    [(world : G.WorldState) → Decidable (G.isTerminal world)] :
    (history : G.historyKernelArena.State) →
      Decidable (IsEmpty (G.historyKernelArena.Action history)) :=
  fun history =>
    decidable_of_iff
      (G.isTerminal history.1)
      (G.historyKernelArena_isTerminal_iff history).symm

/-! ### Initial distribution and complete serialization witness -/

/-- Chance-consistent policy used only for the synthetic initial-root step.

The explicit fallback supplies player actions at histories that are unreachable
from the synthetic root during this one-step initialization. -/
def initialPolicy
    [(world : G.WorldState) → Decidable (G.isTerminal world)]
    (rootPayoff : Fin (n + 1) → U)
    (fallback : FallbackHistoryPolicy G rootPayoff) :
    (game G rootPayoff).toArena.StochasticHistoryPolicy
      (game G rootPayoff).init :=
  fun history hnonterminal => by
    cases hstate : history.1 with
    | root =>
        exact G.init
    | terminal macroHistory hterminal =>
        exfalso
        apply hnonterminal
        rw [hstate]
        exact ⟨fun action => nomatch action⟩
    | player macroHistory hmacroNonterminal count hcount collected =>
        exact FiniteLaw.pure
          (by simpa only [hstate] using fallback.policy history hnonterminal)
    | chance macroHistory hmacroNonterminal action =>
        exact G.transition macroHistory.1 action

/-- The initial policy uses exactly the compiled root and transition chance
kernels. -/
theorem initialPolicy_chanceConsistent
    [(world : G.WorldState) → Decidable (G.isTerminal world)]
    (D : G.DecisionModel)
    (rootPayoff : Fin (n + 1) → U)
    (fallback : FallbackHistoryPolicy G rootPayoff)
    (sourceDeclaredRoot : G.HistoryState → Prop) :
    (observedChanceGame G D rootPayoff sourceDeclaredRoot).ChanceConsistent
      (initialPolicy G rootPayoff fallback) := by
  intro history hnonterminal hmover
  rcases history with ⟨state, path⟩
  cases state with
  | root =>
      rfl
  | terminal macroHistory hterminal =>
      exfalso
      apply hnonterminal
      exact ⟨fun action => nomatch action⟩
  | player macroHistory hmacroNonterminal count hcount collected =>
      simp [observedChanceGameCore, game, mover] at hmover
  | chance macroHistory hmacroNonterminal action =>
      rfl

/-- The synthetic initial root is nonterminal because the initial `FiniteLaw`
has a positive atom. -/
theorem root_not_terminal
    [(world : G.WorldState) → Decidable (G.isTerminal world)]
    (rootPayoff : Fin (n + 1) → U) :
    ¬ (game G rootPayoff).isTerminal .root := by
  intro hterminal
  obtain ⟨world, _⟩ := G.init.exists_hasPositiveAtom
  exact hterminal.false world

/-- Exact one-step target law from the synthetic initial root. -/
theorem initialExecutionLaw
    [(world : G.WorldState) → Decidable (G.isTerminal world)]
    (rootPayoff : Fin (n + 1) → U)
    (fallback : FallbackHistoryPolicy G rootPayoff) :
    (game G rootPayoff).toArena.stochasticHistoryLawFrom
        (initialPolicy G rootPayoff fallback)
        (Arena.HistoryFrom.nil
          (game G rootPayoff).toArena (game G rootPayoff).init)
        1 =
      G.init.map (fun world =>
        (⟨boundary G
            ⟨world, FOSG.History.initial world⟩,
          (Arena.History.nil :
            (game G rootPayoff).toArena.History
              (game G rootPayoff).init
              (game G rootPayoff).init).snoc world⟩ :
          (game G rootPayoff).toArena.HistoryFrom
            (game G rootPayoff).init)) := by
  rw [Arena.stochasticHistoryLawFrom_succ_of_not_terminal
    (initialPolicy G rootPayoff fallback)
    (Arena.HistoryFrom.nil
      (game G rootPayoff).toArena (game G rootPayoff).init)
    0 (root_not_terminal G rootPayoff)]
  change
    G.init.bind
        (fun world =>
          FiniteLaw.pure
            (⟨boundary G
                ⟨world, FOSG.History.initial world⟩,
              (Arena.History.nil :
                (game G rootPayoff).toArena.History
                  (game G rootPayoff).init
                  (game G rootPayoff).init).snoc world⟩ :
              (game G rootPayoff).toArena.HistoryFrom
                (game G rootPayoff).init)) =
      G.init.map (fun world =>
        (⟨boundary G
            ⟨world, FOSG.History.initial world⟩,
          (Arena.History.nil :
            (game G rootPayoff).toArena.History
              (game G rootPayoff).init
              (game G rootPayoff).init).snoc world⟩ :
          (game G rootPayoff).toArena.HistoryFrom
            (game G rootPayoff).init))
  rw [FiniteLaw.map_eq_bind_pure_comp]
  rfl

/-- The genuine serialized behavioral policy and the initialization-only
policy have exactly the same one-step law from the synthetic root. -/
theorem behavioralInitialExecutionLaw
    [(world : G.WorldState) → Decidable (G.isTerminal world)]
    (D : G.DecisionModel)
    (rootPayoff : Fin (n + 1) → U)
    (fallback : FallbackHistoryPolicy G rootPayoff)
    (sourceDeclaredRoot : G.HistoryState → Prop)
    (profile : D.BehavioralProfile) :
    (game G rootPayoff).toArena.stochasticHistoryLawFrom
        (serializedBehavioralHistoryPolicy G D rootPayoff
          sourceDeclaredRoot profile)
        (Arena.HistoryFrom.nil
          (game G rootPayoff).toArena
          (game G rootPayoff).init)
        1 =
      (game G rootPayoff).toArena.stochasticHistoryLawFrom
        (initialPolicy G rootPayoff fallback)
        (Arena.HistoryFrom.nil
          (game G rootPayoff).toArena
          (game G rootPayoff).init)
        1 := by
  have hroot := root_not_terminal G rootPayoff
  rw [Arena.stochasticHistoryLawFrom_succ_of_not_terminal
    (serializedBehavioralHistoryPolicy G D rootPayoff
      sourceDeclaredRoot profile)
    (Arena.HistoryFrom.nil
      (game G rootPayoff).toArena
      (game G rootPayoff).init)
    0 hroot]
  rw [Arena.stochasticHistoryLawFrom_succ_of_not_terminal
    (initialPolicy G rootPayoff fallback)
    (Arena.HistoryFrom.nil
      (game G rootPayoff).toArena
      (game G rootPayoff).init)
    0 hroot]
  rw [serializedBehavioralHistoryPolicy_root G D rootPayoff
    sourceDeclaredRoot profile hroot]
  change G.init.bind _ = G.init.bind _
  apply congrArg (FiniteLaw.bind G.init)
  funext world
  rfl

/-- Exact coupling of the random initial augmented FOSG history and the
serialized EFG history after its synthetic root chance step. -/
def initialBoundaryCoupling
    [(world : G.WorldState) → Decidable (G.isTerminal world)]
    (rootPayoff : Fin (n + 1) → U)
    (fallback : FallbackHistoryPolicy G rootPayoff) :
    FiniteLaw.RelCoupling (Rel G)
      G.initialHistoryKernel
      ((game G rootPayoff).toArena.stochasticHistoryLawFrom
        (initialPolicy G rootPayoff fallback)
        (Arena.HistoryFrom.nil
          (game G rootPayoff).toArena
          (game G rootPayoff).init)
        1) := by
  let sourceInitial : G.WorldState → G.HistoryState :=
    fun world => ⟨world, FOSG.History.initial world⟩
  let targetInitial :
      G.WorldState →
        (game G rootPayoff).toArena.HistoryFrom
          (game G rootPayoff).init :=
    fun world =>
      ⟨boundary G (sourceInitial world),
        (Arena.History.nil :
          (game G rootPayoff).toArena.History
            (game G rootPayoff).init
            (game G rootPayoff).init).snoc world⟩
  let base :
      FiniteLaw.RelCoupling (Rel G)
        (G.init.map sourceInitial) (G.init.map targetInitial) :=
    (FiniteLaw.relCoupling_refl G.init).map
      (f := sourceInitial) (g := targetInitial)
      (S := Rel G)
      (by
        intro left right hsame
        subst right
        rfl)
  change
    FiniteLaw.RelCoupling (Rel G)
      (G.init.map sourceInitial)
      ((game G rootPayoff).toArena.stochasticHistoryLawFrom
        (initialPolicy G rootPayoff fallback)
        (Arena.HistoryFrom.nil
          (game G rootPayoff).toArena
          (game G rootPayoff).init)
        1)
  exact (initialExecutionLaw G rootPayoff fallback).symm ▸ base

/-- Source endpoint law after random initialization and at most `horizon`
FOSG macro transitions. -/
def initializedSourceStateLaw
    [(world : G.WorldState) → Decidable (G.isTerminal world)]
    (sourcePolicy : G.historyKernelArena.Policy)
    (horizon : Nat) :
    FiniteLaw G.HistoryState := by
  letI (history : G.HistoryState) :
      Decidable
        (IsEmpty (G.historyKernelArena.Action history)) :=
    decidable_of_iff
      (G.isTerminal history.1)
      (G.historyKernelArena_isTerminal_iff history).symm
  exact
    G.initialHistoryKernel.bind
      (G.historyKernelArena.stateLawFrom sourcePolicy horizon)

/-- Serialized endpoint law after its synthetic root chance step and at most
`horizon` compiled macro executions. -/
def initializedTargetStateLaw
    [(world : G.WorldState) → Decidable (G.isTerminal world)]
    (D : G.DecisionModel)
    (rootPayoff : Fin (n + 1) → U)
    (sourceDeclaredRoot : G.HistoryState → Prop)
    (data : MacroPolicyData G D rootPayoff sourceDeclaredRoot)
    [(target :
        (macroExecutionKernelArena G D rootPayoff
          sourceDeclaredRoot).State) →
      Decidable
        (IsEmpty
          ((macroExecutionKernelArena G D rootPayoff
            sourceDeclaredRoot).Action target))]
    (sourcePolicy : G.historyKernelArena.Policy)
    (horizon : Nat) :
    FiniteLaw
      ((game G rootPayoff).toArena.HistoryFrom
        (game G rootPayoff).init) :=
  ((game G rootPayoff).toArena.stochasticHistoryLawFrom
      (initialPolicy G rootPayoff data.micro)
      (Arena.HistoryFrom.nil
        (game G rootPayoff).toArena
        (game G rootPayoff).init)
      1).bind
    ((macroExecutionKernelArena G D rootPayoff
      sourceDeclaredRoot).stateLawFrom
      (serializedMacroPolicy G D rootPayoff sourceDeclaredRoot
        data sourcePolicy)
      horizon)

/-- Actual micro-step endpoint law of the genuine serialized observed-EFG
behavioral profile, including the synthetic initial chance step.

One source macro transition consumes `n + 2` target micro steps. -/
def initializedBehavioralTargetMicroStateLaw
    [(world : G.WorldState) → Decidable (G.isTerminal world)]
    (D : G.DecisionModel)
    (rootPayoff : Fin (n + 1) → U)
    (sourceDeclaredRoot : G.HistoryState → Prop)
    (profile : D.BehavioralProfile)
    (horizon : Nat) :
    FiniteLaw
      ((game G rootPayoff).toArena.HistoryFrom
        (game G rootPayoff).init) :=
  (game G rootPayoff).toArena.stochasticHistoryLawFrom
    (serializedBehavioralHistoryPolicy G D rootPayoff
      sourceDeclaredRoot profile)
    (Arena.HistoryFrom.nil
      (game G rootPayoff).toArena
      (game G rootPayoff).init)
    (1 + horizon * (n + 2))

/-- The actual initialized micro-step law of the target behavioral profile is
exactly the initialized macro-controller law. -/
theorem initializedBehavioralTargetMicroStateLaw_eq
    [(world : G.WorldState) → Decidable (G.isTerminal world)]
    (D : G.DecisionModel)
    (rootPayoff : Fin (n + 1) → U)
    (sourceDeclaredRoot : G.HistoryState → Prop)
    (data : MacroPolicyData G D rootPayoff sourceDeclaredRoot)
    [(target :
        (macroExecutionKernelArena G D rootPayoff
          sourceDeclaredRoot).State) →
      Decidable
        (IsEmpty
          ((macroExecutionKernelArena G D rootPayoff
            sourceDeclaredRoot).Action target))]
    (profile : D.BehavioralProfile)
    (horizon : Nat) :
    (initializedBehavioralTargetMicroStateLaw G D rootPayoff
        sourceDeclaredRoot profile horizon).Equivalent
      (initializedTargetStateLaw G D rootPayoff sourceDeclaredRoot
        data (D.behavioralHistoryPolicy profile) horizon) := by
  rw [initializedBehavioralTargetMicroStateLaw]
  rw [Arena.stochasticHistoryLawFrom_add]
  rw [behavioralInitialExecutionLaw G D rootPayoff
    data.micro sourceDeclaredRoot profile]
  rw [initializedTargetStateLaw]
  apply FiniteLaw.bind_congr_positive
  intro target htarget
  obtain ⟨source, _, hrelated⟩ :=
    FiniteLaw.RelCoupling.exists_left_of_hasPositiveAtom_right
      (initialBoundaryCoupling G rootPayoff data.micro) htarget
  exact
    serializedBehavioralMicroStateLaw_eq_macro G D rootPayoff
      sourceDeclaredRoot data profile hrelated horizon

/-- Full finite-horizon endpoint coupling, including the random initial world
and all compiled macro executions. -/
theorem initializedStateLawCoupling
    [(world : G.WorldState) → Decidable (G.isTerminal world)]
    (D : G.DecisionModel)
    (rootPayoff : Fin (n + 1) → U)
    (sourceDeclaredRoot : G.HistoryState → Prop)
    (data : MacroPolicyData G D rootPayoff sourceDeclaredRoot)
    [(target :
        (macroExecutionKernelArena G D rootPayoff
          sourceDeclaredRoot).State) →
      Decidable
        (IsEmpty
          ((macroExecutionKernelArena G D rootPayoff
            sourceDeclaredRoot).Action target))]
    (sourcePolicy : G.historyKernelArena.Policy)
    (horizon : Nat) :
    Nonempty (FiniteLaw.RelCoupling (Rel G)
      (initializedSourceStateLaw G sourcePolicy horizon)
      (initializedTargetStateLaw G D rootPayoff sourceDeclaredRoot
        data sourcePolicy horizon)) := by
  unfold initializedSourceStateLaw
  exact ⟨
    (initialBoundaryCoupling G rootPayoff data.micro).bind
      (fun _ _ hrelated =>
        (serializedMacroPolicy_match G D rootPayoff sourceDeclaredRoot
          data sourcePolicy).stateLawCoupling hrelated horizon)⟩

/-- Exact equality of complete initialized finite-horizon optional
terminal-payoff laws. -/
theorem initializedPayoffLaw_eq
    [(world : G.WorldState) → Decidable (G.isTerminal world)]
    (D : G.DecisionModel)
    (rootPayoff : Fin (n + 1) → U)
    (sourceDeclaredRoot : G.HistoryState → Prop)
    (data : MacroPolicyData G D rootPayoff sourceDeclaredRoot)
    [(target :
        (macroExecutionKernelArena G D rootPayoff
          sourceDeclaredRoot).State) →
      Decidable
        (IsEmpty
          ((macroExecutionKernelArena G D rootPayoff
            sourceDeclaredRoot).Action target))]
    (sourcePolicy : G.historyKernelArena.Policy)
    (horizon : Nat) :
    ((initializedSourceStateLaw G sourcePolicy horizon).map
        G.stoppedPayoffAtHistory).Equivalent
      ((initializedTargetStateLaw G D rootPayoff sourceDeclaredRoot
        data sourcePolicy horizon).map
          (serializedStoppedPayoffAtHistory G rootPayoff)) := by
  obtain ⟨coupling⟩ :=
    initializedStateLawCoupling G D rootPayoff sourceDeclaredRoot
      data sourcePolicy horizon
  exact
    coupling.map_eq
        (fun sourceState targetHistory hrelated =>
          (stoppedPayoff_eq_of_rel G rootPayoff sourceState
            targetHistory hrelated).symm)

/-- Every scalar or structured utility computed from the optional terminal
payoff has the same initialized finite-horizon law in both representations.

Consequently any expectation functional defined on this common FiniteLaw yields
equal expected utility without further simulation reasoning. -/
theorem initializedUtilityLaw_eq
    [(world : G.WorldState) → Decidable (G.isTerminal world)]
    (D : G.DecisionModel)
    (rootPayoff : Fin (n + 1) → U)
    (sourceDeclaredRoot : G.HistoryState → Prop)
    (data : MacroPolicyData G D rootPayoff sourceDeclaredRoot)
    [(target :
        (macroExecutionKernelArena G D rootPayoff
          sourceDeclaredRoot).State) →
      Decidable
        (IsEmpty
          ((macroExecutionKernelArena G D rootPayoff
            sourceDeclaredRoot).Action target))]
    (sourcePolicy : G.historyKernelArena.Policy)
    (horizon : Nat)
    {V : Type*}
    (utility : Option (Fin (n + 1) → U) → V) :
    ((initializedSourceStateLaw G sourcePolicy horizon).map
        (fun state => utility (G.stoppedPayoffAtHistory state))).Equivalent
      ((initializedTargetStateLaw G D rootPayoff sourceDeclaredRoot
        data sourcePolicy horizon).map
          (fun history =>
            utility
              (serializedStoppedPayoffAtHistory
                G rootPayoff history))) := by
  obtain ⟨coupling⟩ :=
    initializedStateLawCoupling G D rootPayoff sourceDeclaredRoot
      data sourcePolicy horizon
  exact
    coupling.map_eq
        (fun sourceState targetHistory hrelated =>
          congrArg utility
            (stoppedPayoff_eq_of_rel G rootPayoff sourceState
              targetHistory hrelated).symm)

/-- Information-indexed behavioral profiles preserve every initialized
finite-horizon derived-utility law under serialization. -/
theorem initializedBehavioralUtilityLaw_eq
    [(world : G.WorldState) → Decidable (G.isTerminal world)]
    (D : G.DecisionModel)
    (rootPayoff : Fin (n + 1) → U)
    (sourceDeclaredRoot : G.HistoryState → Prop)
    (data : MacroPolicyData G D rootPayoff sourceDeclaredRoot)
    [(target :
        (macroExecutionKernelArena G D rootPayoff
          sourceDeclaredRoot).State) →
      Decidable
        (IsEmpty
          ((macroExecutionKernelArena G D rootPayoff
            sourceDeclaredRoot).Action target))]
    (profile : D.BehavioralProfile)
    (horizon : Nat)
    {V : Type*}
    (utility : Option (Fin (n + 1) → U) → V) :
    ((initializedSourceStateLaw G
        (D.behavioralHistoryPolicy profile) horizon).map
          (fun state =>
            utility (G.stoppedPayoffAtHistory state))).Equivalent
      ((initializedTargetStateLaw G D rootPayoff sourceDeclaredRoot
        data (D.behavioralHistoryPolicy profile) horizon).map
          (fun history =>
            utility
              (serializedStoppedPayoffAtHistory
                G rootPayoff history))) :=
  initializedUtilityLaw_eq G D rootPayoff sourceDeclaredRoot
    data (D.behavioralHistoryPolicy profile) horizon utility

/-- Source behavioral play and genuine target observed-EFG behavioral play
have exactly the same initialized finite-horizon optional terminal-payoff law.
-/
theorem initializedBehavioralMicroPayoffLaw_eq
    [(world : G.WorldState) → Decidable (G.isTerminal world)]
    (D : G.DecisionModel)
    (rootPayoff : Fin (n + 1) → U)
    (sourceDeclaredRoot : G.HistoryState → Prop)
    (data : MacroPolicyData G D rootPayoff sourceDeclaredRoot)
    [(target :
        (macroExecutionKernelArena G D rootPayoff
          sourceDeclaredRoot).State) →
      Decidable
        (IsEmpty
          ((macroExecutionKernelArena G D rootPayoff
            sourceDeclaredRoot).Action target))]
    (profile : D.BehavioralProfile)
    (horizon : Nat) :
    ((initializedSourceStateLaw G
        (D.behavioralHistoryPolicy profile) horizon).map
          G.stoppedPayoffAtHistory).Equivalent
      ((initializedBehavioralTargetMicroStateLaw G D rootPayoff
        sourceDeclaredRoot profile horizon).map
          (serializedStoppedPayoffAtHistory G rootPayoff)) := by
  exact
    (initializedPayoffLaw_eq G D rootPayoff sourceDeclaredRoot
      data (D.behavioralHistoryPolicy profile) horizon).trans
        ((initializedBehavioralTargetMicroStateLaw_eq G D rootPayoff
          sourceDeclaredRoot data profile horizon).map
            (serializedStoppedPayoffAtHistory G rootPayoff)).symm

/-- Every utility computed from the optional terminal payoff has the same law
under source behavioral play and genuine target micro-step behavioral play. -/
theorem initializedBehavioralMicroUtilityLaw_eq
    [(world : G.WorldState) → Decidable (G.isTerminal world)]
    (D : G.DecisionModel)
    (rootPayoff : Fin (n + 1) → U)
    (sourceDeclaredRoot : G.HistoryState → Prop)
    (data : MacroPolicyData G D rootPayoff sourceDeclaredRoot)
    [(target :
        (macroExecutionKernelArena G D rootPayoff
          sourceDeclaredRoot).State) →
      Decidable
        (IsEmpty
          ((macroExecutionKernelArena G D rootPayoff
            sourceDeclaredRoot).Action target))]
    (profile : D.BehavioralProfile)
    (horizon : Nat)
    {V : Type*}
    (utility : Option (Fin (n + 1) → U) → V) :
    ((initializedSourceStateLaw G
        (D.behavioralHistoryPolicy profile) horizon).map
          (fun state =>
            utility (G.stoppedPayoffAtHistory state))).Equivalent
      ((initializedBehavioralTargetMicroStateLaw G D rootPayoff
        sourceDeclaredRoot profile horizon).map
          (fun history =>
            utility
              (serializedStoppedPayoffAtHistory
                G rootPayoff history))) := by
  exact
    (initializedBehavioralUtilityLaw_eq G D rootPayoff
      sourceDeclaredRoot data profile horizon utility).trans
        ((initializedBehavioralTargetMicroStateLaw_eq G D rootPayoff
          sourceDeclaredRoot data profile horizon).map
            (fun history => utility
              (serializedStoppedPayoffAtHistory
                G rootPayoff history))).symm


end ExtensiveGame.FOSG.Sequentialization
