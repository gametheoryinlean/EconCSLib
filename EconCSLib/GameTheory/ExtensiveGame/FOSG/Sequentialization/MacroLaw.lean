/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.FOSG.Sequentialization.Policy

/-!
# EconCSLib.GameTheory.ExtensiveGame.FOSG.Sequentialization.MacroLaw

One-step macro-boundary laws and the exact kernel simulation.
-/

namespace ExtensiveGame.FOSG.Sequentialization

universe uU uSA uO uP

variable {n : ℕ} {U : Type uU}
  (G : FOSG.{0, uU, uSA, uSA, uO, uP} (Fin (n + 1)) U)

/-! ### Exact one-macro-step execution law -/

/-- Relation between an augmented FOSG macro state and a serialized EFG
complete history at its corresponding macro boundary. -/
def Rel
    [(world : G.WorldState) → Decidable (G.isTerminal world)]
    (source : G.HistoryState)
    (target :
      (arena G).HistoryFrom (State.root : State G)) : Prop :=
  target.1 = boundary G source

/-- A serialized macro-boundary history is related to at most one augmented
FOSG history state. -/
theorem Rel.left_unique
    [(world : G.WorldState) → Decidable (G.isTerminal world)]
    {source₁ source₂ : G.HistoryState}
    {target :
      (arena G).HistoryFrom (State.root : State G)}
    (h₁ : Rel G source₁ target)
    (h₂ : Rel G source₂ target) :
    source₁ = source₂ :=
  boundary_injective G (h₁.symm.trans h₂)

/-- At a related nonterminal macro boundary, the genuine serialized
observed-EFG behavioral policy has exactly the mixture of canonical macro
execution laws induced by the source behavioral joint-action FiniteLaw.

This is the missing micro/macro realization equation: no quotient of
probabilities and no support-only approximation is used. -/
theorem serializedBehavioralExecution_eq_jointActionLaw_bind_macro
    [(world : G.WorldState) → Decidable (G.isTerminal world)]
    (D : G.DecisionModel)
    (rootPayoff : Fin (n + 1) → U)
    (fallback : FallbackHistoryPolicy G rootPayoff)
    (sourceDeclaredRoot : G.HistoryState → Prop)
    (profile : D.BehavioralProfile)
    (source : G.HistoryState)
    (hsource : ¬ G.isTerminal source.1)
    (target :
      (game G rootPayoff).toArena.HistoryFrom
        (game G rootPayoff).init)
    (hrelated : Rel G source target) :
    ((game G rootPayoff).toArena.stochasticHistoryLawFrom
        (serializedBehavioralHistoryPolicy G D rootPayoff
          sourceDeclaredRoot profile)
        target (n + 2)).Equivalent
      ((D.jointActionLaw profile source hsource).bind
        (fun jointAction =>
          (game G rootPayoff).toArena.stochasticHistoryLawFrom
            (macroPolicy G rootPayoff fallback source jointAction)
            target (n + 2))) := by
  have htargetState :
      target.1 =
        .player source hsource 0 (Nat.zero_lt_succ n)
          (PartialAction.empty G source.1) := by
    exact
      hrelated.trans
        (boundary_of_not_terminal G source hsource)
  let startHistory :
      (game G rootPayoff).toArena.History
        (game G rootPayoff).init
        (.player source hsource 0 (Nat.zero_lt_succ n)
          (PartialAction.empty G source.1)) :=
    htargetState ▸ target.2
  let start :
      (game G rootPayoff).toArena.HistoryFrom
        (game G rootPayoff).init :=
    ⟨.player source hsource 0 (Nat.zero_lt_succ n)
        (PartialAction.empty G source.1),
      startHistory⟩
  have htargetEq : target = start := by
    apply Sigma.ext htargetState
    exact (eqRec_heq htargetState target.2).symm
  rw [htargetEq]
  simpa only [jointActionLaw_eq_finPi] using
    behavioralPlayerExecution_eq_finPiFrom_bind_macro G D rootPayoff fallback
      sourceDeclaredRoot profile source hsource
      (n + 1) 0 (Nat.zero_lt_succ n) (by omega)
      (PartialAction.empty G source.1) startHistory

/-- Exact target endpoint law for one serialized FOSG macro action.

The theorem returns the concrete target endpoint map because it depends on the
incoming target history.  The target stochastic execution is exactly the
source transition kernel pushed through this map, and every resulting endpoint
is the macro boundary corresponding to the appended FOSG history. -/
theorem exists_macroExecutionLaw
    [(world : G.WorldState) → Decidable (G.isTerminal world)]
    (rootPayoff : Fin (n + 1) → U)
    (fallback : FallbackHistoryPolicy G rootPayoff)
    (source : G.HistoryState)
    (jointAction : G.JointAction source.1)
    (target :
      (game G rootPayoff).toArena.HistoryFrom
        (game G rootPayoff).init)
    (hrelated : Rel G source target) :
    ∃ targetEndpoint :
        G.WorldState →
          (game G rootPayoff).toArena.HistoryFrom
            (game G rootPayoff).init,
      (game G rootPayoff).toArena.stochasticHistoryLawFrom
          (macroPolicy G rootPayoff fallback source jointAction)
          target (n + 2) =
        (G.transition source.1 jointAction).map targetEndpoint ∧
      ∀ nextWorld,
        (targetEndpoint nextWorld).1 =
          boundary G
            ⟨nextWorld,
              FOSG.History.snoc source.2 jointAction nextWorld⟩ := by
  have hnonterminal : ¬ G.isTerminal source.1 := by
    intro hterminal
    exact ((G.terminal_iff source.1).mp hterminal).false jointAction
  have hboundary :
      boundary G source =
        playerState G source hnonterminal jointAction 0
          (Nat.zero_lt_succ n) :=
    boundary_eq_playerState G source hnonterminal jointAction
  have htargetState :
      target.1 =
        playerState G source hnonterminal jointAction 0
          (Nat.zero_lt_succ n) :=
    hrelated.trans hboundary
  let startHistory :
      (game G rootPayoff).toArena.History
        (game G rootPayoff).init
        (playerState G source hnonterminal jointAction 0
          (Nat.zero_lt_succ n)) :=
    htargetState ▸ target.2
  let start :
      (game G rootPayoff).toArena.HistoryFrom
        (game G rootPayoff).init :=
    ⟨playerState G source hnonterminal jointAction 0
        (Nat.zero_lt_succ n),
      startHistory⟩
  have htargetEq : target = start := by
    apply Sigma.ext htargetState
    exact (eqRec_heq htargetState target.2).symm
  let deterministic :=
    macroDeterministicPolicy G rootPayoff fallback source jointAction
  let stochastic :=
    macroPolicy G rootPayoff fallback source jointAction
  let chanceHistory :
      (game G rootPayoff).toArena.HistoryFrom
        (game G rootPayoff).init :=
    (game G rootPayoff).toArena.stoppedHistoryFrom
      deterministic start (n + 1)
  have hchanceState :
      chanceHistory.1 =
        chanceState G source hnonterminal jointAction := by
    exact stoppedHistoryFrom_playerPrefix_fst G rootPayoff fallback source
      hnonterminal jointAction 0 (Nat.zero_lt_succ n) startHistory
  let chancePath :
      (game G rootPayoff).toArena.History
        (game G rootPayoff).init
        (chanceState G source hnonterminal jointAction) :=
    hchanceState ▸ chanceHistory.2
  have hchanceHistoryEq :
      chanceHistory =
        (⟨chanceState G source hnonterminal jointAction,
            chancePath⟩ :
          (game G rootPayoff).toArena.HistoryFrom
            (game G rootPayoff).init) := by
    apply Sigma.ext hchanceState
    exact (eqRec_heq hchanceState chanceHistory.2).symm
  let targetEndpoint :
      G.WorldState →
        (game G rootPayoff).toArena.HistoryFrom
          (game G rootPayoff).init :=
    fun nextWorld =>
      ⟨boundary G
          ⟨nextWorld,
            FOSG.History.snoc source.2 jointAction nextWorld⟩,
        chancePath.snoc nextWorld⟩
  refine ⟨targetEndpoint, ?_, ?_⟩
  · rw [htargetEq]
    have hpure :=
      macroPolicy_isPureFor_playerPrefix G rootPayoff fallback source
        hnonterminal jointAction 0 (Nat.zero_lt_succ n) startHistory
    have hprefix :
        (game G rootPayoff).toArena.stochasticHistoryLawFrom
            stochastic start (n + 1) =
          FiniteLaw.pure chanceHistory := by
      exact
        Arena.stochasticHistoryLawFrom_eq_pure_stoppedHistoryFrom
          stochastic deterministic start (n + 1) hpure
    have hadd :
        n + 2 = (n + 1) + 1 := by omega
    rw [hadd]
    rw [Arena.stochasticHistoryLawFrom_add
      stochastic start (n + 1) 1]
    rw [hprefix, FiniteLaw.pure_bind]
    rw [hchanceHistoryEq]
    have hchanceNonterminal :=
      chanceState_not_terminal G rootPayoff source hnonterminal
        jointAction
    rw [Arena.stochasticHistoryLawFrom_succ_of_not_terminal
      stochastic
      ⟨chanceState G source hnonterminal jointAction, chancePath⟩
      0 hchanceNonterminal]
    change
      (G.transition source.1 jointAction).bind
          (fun nextWorld => FiniteLaw.pure (targetEndpoint nextWorld)) =
        (G.transition source.1 jointAction).map targetEndpoint
    rw [FiniteLaw.map_eq_bind_pure_comp]
    rfl
  · intro nextWorld
    rfl

/-- Serializer macro boundaries are terminal exactly when their FOSG macro
states are terminal. -/
theorem boundary_isTerminal_iff
    [(world : G.WorldState) → Decidable (G.isTerminal world)]
    (rootPayoff : Fin (n + 1) → U)
    (source : G.HistoryState) :
    (game G rootPayoff).isTerminal (boundary G source) ↔
      G.isTerminal source.1 := by
  by_cases hterminal : G.isTerminal source.1
  · rw [boundary_of_terminal G source hterminal]
    constructor
    · intro _
      exact hterminal
    · intro _
      exact ⟨fun action => nomatch action⟩
  · rw [boundary_of_not_terminal G source hterminal]
    constructor
    · intro hserializedTerminal
      have hnotEmptyJoint :
          ¬ IsEmpty (G.JointAction source.1) := by
        intro hempty
        exact hterminal ((G.terminal_iff source.1).mpr hempty)
      obtain ⟨jointAction⟩ :=
        not_isEmpty_iff.mp hnotEmptyJoint
      exact False.elim
        (hserializedTerminal.false
          (jointAction (0 : Fin (n + 1))))
    · intro h
      exact (hterminal h).elim

/-- The macro policy uses the compiled observed EFG's declared chance kernel
at every chance history. -/
theorem macroPolicy_chanceConsistent
    [(world : G.WorldState) → Decidable (G.isTerminal world)]
    (D : G.DecisionModel)
    (rootPayoff : Fin (n + 1) → U)
    (fallback : FallbackHistoryPolicy G rootPayoff)
    (sourceDeclaredRoot : G.HistoryState → Prop)
    (source : G.HistoryState)
    (jointAction : G.JointAction source.1) :
    (observedChanceGame G D rootPayoff sourceDeclaredRoot).ChanceConsistent
      (macroPolicy G rootPayoff fallback source jointAction) := by
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

/-- The concrete compiler's coupling-based probabilistic weak simulation. -/
def probabilisticWeakSimulation
    [(world : G.WorldState) → Decidable (G.isTerminal world)]
    (D : G.DecisionModel)
    (rootPayoff : Fin (n + 1) → U)
    (fallback : FallbackHistoryPolicy G rootPayoff)
    (sourceDeclaredRoot : G.HistoryState → Prop) :
    KernelArena.ProbabilisticWeakSimulation
      G.historyKernelArena
      (game G rootPayoff).toArena
      (game G rootPayoff).init
      (observedChanceGame G D rootPayoff
        sourceDeclaredRoot).ChanceConsistent where
  Rel := Rel G
  match_action := by
    intro source target hrelated jointAction
    have hnonterminal : ¬ G.isTerminal source.1 := by
      intro hterminal
      exact ((G.terminal_iff source.1).mp hterminal).false jointAction
    have hboundary :
        boundary G source =
          playerState G source hnonterminal jointAction 0
            (Nat.zero_lt_succ n) :=
      boundary_eq_playerState G source hnonterminal jointAction
    have htargetState :
        target.1 =
          playerState G source hnonterminal jointAction 0
            (Nat.zero_lt_succ n) :=
      hrelated.trans hboundary
    let startHistory :
        (game G rootPayoff).toArena.History
          (game G rootPayoff).init
          (playerState G source hnonterminal jointAction 0
            (Nat.zero_lt_succ n)) :=
      htargetState ▸ target.2
    let start :
        (game G rootPayoff).toArena.HistoryFrom
          (game G rootPayoff).init :=
      ⟨playerState G source hnonterminal jointAction 0
          (Nat.zero_lt_succ n), startHistory⟩
    have htargetEq : target = start := by
      apply Sigma.ext htargetState
      exact (eqRec_heq htargetState target.2).symm
    let deterministic :=
      macroDeterministicPolicy G rootPayoff fallback source jointAction
    let stochastic :=
      macroPolicy G rootPayoff fallback source jointAction
    let chanceHistory :
        (game G rootPayoff).toArena.HistoryFrom
          (game G rootPayoff).init :=
      (game G rootPayoff).toArena.stoppedHistoryFrom
        deterministic start (n + 1)
    have hchanceState :
        chanceHistory.1 =
          chanceState G source hnonterminal jointAction :=
      stoppedHistoryFrom_playerPrefix_fst G rootPayoff fallback source
        hnonterminal jointAction 0 (Nat.zero_lt_succ n) startHistory
    let chancePath :
        (game G rootPayoff).toArena.History
          (game G rootPayoff).init
          (chanceState G source hnonterminal jointAction) :=
      hchanceState ▸ chanceHistory.2
    have hchanceHistoryEq :
        chanceHistory =
          (⟨chanceState G source hnonterminal jointAction,
              chancePath⟩ :
            (game G rootPayoff).toArena.HistoryFrom
              (game G rootPayoff).init) := by
      apply Sigma.ext hchanceState
      exact (eqRec_heq hchanceState chanceHistory.2).symm
    let targetEndpoint :
        G.WorldState →
          (game G rootPayoff).toArena.HistoryFrom
            (game G rootPayoff).init :=
      fun nextWorld =>
        ⟨boundary G
            ⟨nextWorld,
              FOSG.History.snoc source.2 jointAction nextWorld⟩,
          chancePath.snoc nextWorld⟩
    have htargetLaw :
        (game G rootPayoff).toArena.stochasticHistoryLawFrom
            stochastic target (n + 2) =
          (G.transition source.1 jointAction).map targetEndpoint := by
      rw [htargetEq]
      have hpure :=
        macroPolicy_isPureFor_playerPrefix G rootPayoff fallback source
          hnonterminal jointAction 0 (Nat.zero_lt_succ n) startHistory
      have hprefix :
          (game G rootPayoff).toArena.stochasticHistoryLawFrom
              stochastic start (n + 1) =
            FiniteLaw.pure chanceHistory :=
        Arena.stochasticHistoryLawFrom_eq_pure_stoppedHistoryFrom
          stochastic deterministic start (n + 1) hpure
      have hadd : n + 2 = (n + 1) + 1 := by omega
      rw [hadd]
      rw [Arena.stochasticHistoryLawFrom_add
        stochastic start (n + 1) 1]
      rw [hprefix, FiniteLaw.pure_bind]
      rw [hchanceHistoryEq]
      have hchanceNonterminal :=
        chanceState_not_terminal G rootPayoff source hnonterminal
          jointAction
      rw [Arena.stochasticHistoryLawFrom_succ_of_not_terminal
        stochastic
        ⟨chanceState G source hnonterminal jointAction, chancePath⟩
        0 hchanceNonterminal]
      change
        (G.transition source.1 jointAction).bind
            (fun nextWorld => FiniteLaw.pure (targetEndpoint nextWorld)) =
          (G.transition source.1 jointAction).map targetEndpoint
      rw [FiniteLaw.map_eq_bind_pure_comp]
      rfl
    let sourceEndpoint : G.WorldState → G.HistoryState :=
      fun nextWorld =>
        ⟨nextWorld,
          FOSG.History.snoc source.2 jointAction nextWorld⟩
    have hcoupling :
        FiniteLaw.RelCoupling (Rel G)
          (G.historyKernelArena.next source jointAction)
          ((game G rootPayoff).toArena.stochasticHistoryLawFrom
            stochastic target (n + 2)) := by
      change
        FiniteLaw.RelCoupling (Rel G)
          ((G.transition source.1 jointAction).map sourceEndpoint)
          ((game G rootPayoff).toArena.stochasticHistoryLawFrom
            stochastic target (n + 2))
      let base :
          FiniteLaw.RelCoupling (Rel G)
            ((G.transition source.1 jointAction).map sourceEndpoint)
            ((G.transition source.1 jointAction).map targetEndpoint) :=
        (FiniteLaw.relCoupling_refl
          (G.transition source.1 jointAction)).map
            (fun _ _ hsame => hsame ▸ rfl)
      exact htargetLaw.symm ▸ base
    refine
      ⟨stochastic,
        n + 2, by omega,
        macroPolicy_chanceConsistent G D rootPayoff fallback sourceDeclaredRoot
          source jointAction,
        hcoupling⟩
  terminal_iff := by
    intro source target hrelated
    calc
      IsEmpty (G.historyKernelArena.Action source) ↔
          G.isTerminal source.1 :=
        G.historyKernelArena_isTerminal_iff source
      _ ↔ (game G rootPayoff).isTerminal (boundary G source) :=
        (boundary_isTerminal_iff G rootPayoff source).symm
      _ ↔ (game G rootPayoff).isTerminal target.1 := by
        rw [hrelated]

/-- The compiled EFG viewed as a stochastic arena of admissible macro
executions.

An action packages a positive-length chance-consistent serialized policy and
its micro-step horizon.  The transition kernel is its exact endpoint law. -/
def macroExecutionKernelArena
    [(world : G.WorldState) → Decidable (G.isTerminal world)]
    (D : G.DecisionModel)
    (rootPayoff : Fin (n + 1) → U)
    (sourceDeclaredRoot : G.HistoryState → Prop) :
    KernelArena :=
  KernelArena.executionKernelArena
    (game G rootPayoff).toArena
    (game G rootPayoff).init
    (observedChanceGame G D rootPayoff
      sourceDeclaredRoot).ChanceConsistent

/-- The positive serialized execution implementing one concrete FOSG joint
action from a related macro boundary. -/
def macroExecutionAction
    [(world : G.WorldState) → Decidable (G.isTerminal world)]
    (D : G.DecisionModel)
    (rootPayoff : Fin (n + 1) → U)
    (fallback : FallbackHistoryPolicy G rootPayoff)
    (sourceDeclaredRoot : G.HistoryState → Prop)
    (source : G.HistoryState)
    (jointAction : G.JointAction source.1)
    (target :
      (game G rootPayoff).toArena.HistoryFrom
        (game G rootPayoff).init)
    (htarget :
      ¬ (game G rootPayoff).isTerminal target.1) :
    (macroExecutionKernelArena G D rootPayoff
      sourceDeclaredRoot).Action target where
  nonterminal := htarget
  policy := macroPolicy G rootPayoff fallback source jointAction
  fuel := n + 2
  positive := by omega
  admissible :=
    macroPolicy_chanceConsistent G D rootPayoff fallback sourceDeclaredRoot
      source jointAction

/-- Nonemptiness of the compiled macro-action type certifies that its
underlying serialized boundary is nonterminal. -/
def macroTargetNonterminal
    [(world : G.WorldState) → Decidable (G.isTerminal world)]
    (D : G.DecisionModel)
    (rootPayoff : Fin (n + 1) → U)
    (sourceDeclaredRoot : G.HistoryState → Prop)
    (target :
      (macroExecutionKernelArena G D rootPayoff
        sourceDeclaredRoot).State)
    (htarget :
      ¬ IsEmpty
        ((macroExecutionKernelArena G D rootPayoff
          sourceDeclaredRoot).Action target)) :
    ¬ (game G rootPayoff).isTerminal target.1 := by
  intro hterminal
  apply htarget
  exact ⟨fun execution => execution.nonterminal hterminal⟩

/-- Runtime inputs needed to totalize the macro-policy compiler.

The resolver returns a relation witness as data at genuine macro boundaries.
The explicit fallback macro policy handles unrelated target states. -/
structure MacroPolicyData
    [(world : G.WorldState) → Decidable (G.isTerminal world)]
    (D : G.DecisionModel)
    (rootPayoff : Fin (n + 1) → U)
    (sourceDeclaredRoot : G.HistoryState → Prop) where
  micro : FallbackHistoryPolicy G rootPayoff
  resolve :
    (target :
      (macroExecutionKernelArena G D rootPayoff
        sourceDeclaredRoot).State) →
      Option {source : G.HistoryState // Rel G source target}
  resolve_complete :
    ∀ (source : G.HistoryState)
      (target :
        (macroExecutionKernelArena G D rootPayoff
          sourceDeclaredRoot).State),
      Rel G source target →
        ∃ resolved, resolve target = some resolved
  fallback :
    (macroExecutionKernelArena G D rootPayoff
      sourceDeclaredRoot).Policy

/-- Compile a randomized FOSG macro policy using an explicit boundary
resolver and fallback policy. -/
def serializedMacroPolicy
    [(world : G.WorldState) → Decidable (G.isTerminal world)]
    (D : G.DecisionModel)
    (rootPayoff : Fin (n + 1) → U)
    (sourceDeclaredRoot : G.HistoryState → Prop)
    (data : MacroPolicyData G D rootPayoff sourceDeclaredRoot)
    (sourcePolicy : G.historyKernelArena.Policy) :
    (macroExecutionKernelArena G D rootPayoff
      sourceDeclaredRoot).Policy :=
  fun target htarget =>
    match hresolve : data.resolve target with
    | some resolved =>
      let source := resolved.1
      let hrelated : Rel G source target := resolved.2
      have hsource :
          ¬ IsEmpty (G.historyKernelArena.Action source) := by
        intro hterminal
        exact
          (macroTargetNonterminal G D rootPayoff sourceDeclaredRoot
            target htarget)
            (((probabilisticWeakSimulation G D rootPayoff data.micro
              sourceDeclaredRoot).terminal_iff hrelated).mp hterminal)
      (sourcePolicy source hsource).map fun jointAction =>
        macroExecutionAction G D rootPayoff data.micro sourceDeclaredRoot
          source jointAction target
            (macroTargetNonterminal G D rootPayoff
              sourceDeclaredRoot target htarget)
    | none => data.fallback target htarget

/-- At a related boundary, the compiled macro policy is exactly the
pushforward of the source joint-action law through canonical serialized
executions. -/
theorem serializedMacroPolicy_eq_map
    [(world : G.WorldState) → Decidable (G.isTerminal world)]
    (D : G.DecisionModel)
    (rootPayoff : Fin (n + 1) → U)
    (sourceDeclaredRoot : G.HistoryState → Prop)
    (data : MacroPolicyData G D rootPayoff sourceDeclaredRoot)
    (sourcePolicy : G.historyKernelArena.Policy)
    {source : G.HistoryState}
    {target :
      (game G rootPayoff).toArena.HistoryFrom
        (game G rootPayoff).init}
    (hrelated : Rel G source target)
    (hsource :
      ¬ IsEmpty (G.historyKernelArena.Action source))
    (htarget :
      ¬ IsEmpty
        ((macroExecutionKernelArena G D rootPayoff
          sourceDeclaredRoot).Action target)) :
    serializedMacroPolicy G D rootPayoff sourceDeclaredRoot data
        sourcePolicy target htarget =
      (sourcePolicy source hsource).map fun jointAction =>
        macroExecutionAction G D rootPayoff data.micro sourceDeclaredRoot
          source jointAction target
            (macroTargetNonterminal G D rootPayoff
              sourceDeclaredRoot target htarget) := by
  obtain ⟨resolved, hresolve⟩ :=
    data.resolve_complete source target hrelated
  rcases resolved with ⟨chosen, hchosenRelated⟩
  have hchosen : chosen = source :=
    Rel.left_unique G hchosenRelated hrelated
  subst chosen
  unfold serializedMacroPolicy
  rw [hresolve]


end ExtensiveGame.FOSG.Sequentialization
