/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.FOSG.Sequentialization.Witness

/-!
# EconCSLib.GameTheory.ExtensiveGame.FOSG.Sequentialization.Equilibrium

Finite-horizon behavioral Nash and macro-Nash on presentation-designated continuations transfer.
-/

namespace ExtensiveGame.FOSG.Sequentialization

universe uU uSA uO uP

variable {n : ℕ} {U : Type uU}
  (G : FOSG.{0, uU, uSA, uSA, uO, uP} (Fin (n + 1)) U)

/-! ### Finite-horizon behavioral equilibrium transfer -/

/-- The initialized finite-horizon FOSG behavioral game form.

An outcome is the complete FiniteLaw of optional terminal payoffs: `none` records
that the finite horizon ended before termination. Expected utility, risk
measures, and distributional preferences can all be supplied externally. -/
def sourceBehavioralGameForm
    [(world : G.WorldState) → Decidable (G.isTerminal world)]
    (D : G.DecisionModel)
    (horizon : Nat) :
    GameForm (Fin (n + 1)) where
  Strategy := D.BehavioralStrategy
  Outcome := (Option (Fin (n + 1) → U) → ℚ) → ℚ
  outcome profile :=
    fun value => (initializedSourceStateLaw G
      (D.behavioralHistoryPolicy profile) horizon).map
        G.stoppedPayoffAtHistory |>.expectRat value

/-- The initialized finite-horizon behavioral game form of the genuinely
micro-executed serialized observed EFG. -/
def serializedBehavioralGameForm
    [(world : G.WorldState) → Decidable (G.isTerminal world)]
    (D : G.DecisionModel)
    (rootPayoff : Fin (n + 1) → U)
    (sourceDeclaredRoot : G.HistoryState → Prop)
    (horizon : Nat) :
    GameForm (Fin (n + 1)) where
  Strategy :=
    (observedChanceGame G D rootPayoff
      sourceDeclaredRoot).observed.BehavioralStrategy
  Outcome := (Option (Fin (n + 1) → U) → ℚ) → ℚ
  outcome profile :=
    fun value => (((game G rootPayoff).toArena.stochasticHistoryLawFrom
      (ObservedChanceGame.BehavioralProfile.toHistoryPolicy
        (observedChanceGame G D rootPayoff sourceDeclaredRoot)
        profile)
      (Arena.HistoryFrom.nil
        (game G rootPayoff).toArena
        (game G rootPayoff).init)
      (1 + horizon * (n + 2))).map
      (serializedStoppedPayoffAtHistory G rootPayoff)).expectRat value

/-- Exact finite-horizon game-form isomorphism between FOSG behavioral play
and genuine serialized observed-EFG behavioral play. -/
def behavioralGameFormIso
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
    (certificate :
      BehavioralStrategyEquivalence G D rootPayoff sourceDeclaredRoot)
    (horizon : Nat) :
    (sourceBehavioralGameForm G D horizon).Iso
      (serializedBehavioralGameForm G D rootPayoff
        sourceDeclaredRoot horizon) where
  strategyEquiv := certificate.strategyEquiv
  outcomeEquiv := Equiv.refl _
  map_outcome := by
    intro profile
    have hprofile :
        (fun i => certificate.strategyEquiv i (profile i)) =
          serializedObservedBehavioralProfile G D rootPayoff
            sourceDeclaredRoot profile := by
      funext i information
      exact certificate.strategyEquiv_apply i (profile i) information
    change
      (fun value =>
        ((initializedSourceStateLaw G
          (D.behavioralHistoryPolicy profile) horizon).map
            G.stoppedPayoffAtHistory).expectRat value) =
      (fun value =>
        (((game G rootPayoff).toArena.stochasticHistoryLawFrom
          (ObservedChanceGame.BehavioralProfile.toHistoryPolicy
            (observedChanceGame G D rootPayoff sourceDeclaredRoot)
            (fun i => certificate.strategyEquiv i (profile i)))
          (Arena.HistoryFrom.nil
            (game G rootPayoff).toArena
            (game G rootPayoff).init)
          (1 + horizon * (n + 2))).map
            (serializedStoppedPayoffAtHistory G rootPayoff)).expectRat value)
    rw [hprofile]
    funext value
    exact
      initializedBehavioralMicroPayoffLaw_eq G D rootPayoff
        sourceDeclaredRoot data profile horizon value

/-- Finite-horizon behavioral Nash equilibrium transfers in both directions
between the FOSG and its genuinely micro-executed serialized observed EFG.

The utility functional may inspect the entire optional terminal-payoff
distribution; an expected-utility interpretation is one specialization. -/
theorem behavioralIsNash_iff
    [(world : G.WorldState) → Decidable (G.isTerminal world)]
    [DecidableEq (Fin (n + 1))]
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
    (certificate :
      BehavioralStrategyEquivalence G D rootPayoff sourceDeclaredRoot)
    (horizon : Nat)
    {V : Type*} [Preorder V]
    (utility :
      ((Option (Fin (n + 1) → U) → ℚ) → ℚ) →
        Fin (n + 1) → V)
    (profile : D.BehavioralProfile) :
    (sourceBehavioralGameForm G D horizon).IsNash
        utility profile ↔
      (serializedBehavioralGameForm G D rootPayoff
        sourceDeclaredRoot horizon).IsNash
          utility
          ((behavioralGameFormIso G D rootPayoff
            sourceDeclaredRoot data certificate horizon).mapProfile profile) := by
  exact
    (behavioralGameFormIso G D rootPayoff
      sourceDeclaredRoot data certificate horizon).isNash_iff
        (by
          intro outcome i
          rfl)
        profile

/-- Terminality decision instance specialized to the compiled observed chance
game. -/
instance instObservedDecidableIsTerminal
    [(world : G.WorldState) → Decidable (G.isTerminal world)]
    (D : G.DecisionModel)
    (rootPayoff : Fin (n + 1) → U)
    (sourceDeclaredRoot : G.HistoryState → Prop) :
    (state :
      (observedChanceGame G D rootPayoff
        sourceDeclaredRoot).observed.base.State) →
      Decidable
        ((observedChanceGame G D rootPayoff
          sourceDeclaredRoot).observed.base.isTerminal state) :=
  instDecidableIsTerminal G rootPayoff

/-- The concrete finite-player sequential compiler satisfies the complete
`FOSG.WeakSerialization` interface. -/
def weakSerialization
    [(world : G.WorldState) → Decidable (G.isTerminal world)]
    (D : G.DecisionModel)
    (rootPayoff : Fin (n + 1) → U)
    (fallback : FallbackHistoryPolicy G rootPayoff)
    (sourceDeclaredRoot : G.HistoryState → Prop) :
    G.WeakSerialization
      (observedChanceGame G D rootPayoff sourceDeclaredRoot) where
  simulation :=
    probabilisticWeakSimulation G D rootPayoff fallback sourceDeclaredRoot
  targetRoots :=
    rootPresentation G D rootPayoff sourceDeclaredRoot
  match_init := by
    refine
      ⟨initialPolicy G rootPayoff fallback, 1,
        initialPolicy_chanceConsistent G D rootPayoff
          fallback sourceDeclaredRoot,
        initialBoundaryCoupling G rootPayoff fallback⟩
  observationMap := fun _ privateObservation => some privateObservation
  observationMap_injective := by
    intro i left right heq
    exact Option.some.inj heq
  map_observe := by
    intro i source target hrelated
    change
      some (G.privateObservations i source.2) =
        privateView G i target.1
    change Rel G source target at hrelated
    rw [hrelated]
    by_cases hterminal : G.isTerminal source.1
    · simp [boundary, hterminal, privateView]
    · simp [boundary, hterminal, privateView]
  publicMap := some
  publicMap_injective := by
    intro left right heq
    exact Option.some.inj heq
  map_publicObserve := by
    intro source target hrelated
    change
      some (G.publicObservations source.2) =
        publicView G target.1
    change Rel G source target at hrelated
    rw [hrelated]
    by_cases hterminal : G.isTerminal source.1
    · simp [boundary, hterminal, publicView]
    · simp [boundary, hterminal, publicView]
  map_publicOf := by
    intro i privateObservation
    rfl
  map_terminalPayoff := by
    intro source target hrelated hterminal
    rw [hrelated]
    simp [observedChanceGameCore, game, boundary, hterminal]
  IsDeclaredMacroRoot := sourceDeclaredRoot
  map_declaredMacroRoot := by
    intro source target hrelated
    change
      sourceDeclaredRoot source ↔
        isDesignatedContinuationRoot G sourceDeclaredRoot target.1
    change Rel G source target at hrelated
    rw [hrelated]
    by_cases hterminal : G.isTerminal source.1
    · simp [isDesignatedContinuationRoot, boundary, hterminal]
    · simp [isDesignatedContinuationRoot, boundary, hterminal]

/-- The concrete sequential compiler gives a progressing weak simulation on
all positive-probability realized paths. -/
theorem weakSerialization_progressing
    [(world : G.WorldState) → Decidable (G.isTerminal world)]
    (D : G.DecisionModel)
    (rootPayoff : Fin (n + 1) → U)
    (fallback : FallbackHistoryPolicy G rootPayoff)
    (sourceDeclaredRoot : G.HistoryState → Prop) :
    (weakSerialization G D rootPayoff fallback
      sourceDeclaredRoot).toSupportWeakSimulation.Progressing :=
  (weakSerialization G D rootPayoff
    fallback sourceDeclaredRoot).toSupportWeakSimulation_progressing

end ExtensiveGame.FOSG.Sequentialization
