/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.FOSG.Sequentialization.Equilibrium
import EconCSLib.GameTheory.ExtensiveGame.FOSG.FOSGBehavioralSerialization

/-!
# EconCSLib.GameTheory.ExtensiveGame.FOSG.FOSGContinuation

Continuation-family semantics for finite-player FOSG sequentialization.

`FOSGSequentialization` proves exact initialized finite-horizon behavioral
Nash transfer and exact coupling from every related macro boundary.  This
module upgrades those local facts to a subgame theorem.  It defines:

* the source payoff-law continuation family on augmented FOSG histories;
* the target payoff-law continuation family on genuine serialized EFG
  histories at related macro boundaries;
* a relational-root `ContinuationGameForm.Simulation` between them;
* finite-macro-horizon behavioral Nash on presentation-designated continuations and its two-way transfer theorem.

The root correspondence remains relational.  This is important: weak
serialization relates an augmented macro history to any genuine target
history reaching its serialized boundary.  No arbitrary canonical target
history is selected merely to fit a function-shaped morphism.

The weakness is only temporal and structural.  At every related macro root,
the source executes `horizon` simultaneous steps while the target executes
`horizon * (n + 2)` genuine micro steps.  Their optional terminal-payoff
finite laws are semantically equivalent exactly: `none` denotes horizon
exhaustion before termination. Strategy compilation is an equivalence, the caller-declared
macro roots correspond exactly, and finite-horizon behavioral Nash on those
declared roots therefore transfers in both directions through the generic
continuation simulation theorem.

The synthetic randomized initialization root is handled by the existing
initialized game-form isomorphism.  `IsSourceBehavioralMacroNashOnDeclaredContinuations` and
`IsSerializedBehavioralMacroNashOnDeclaredContinuations` combine initial-root Nash with continuation
Nash at every proper caller-declared macro root.  This module does not by
itself certify that those roots are standard EFG subgames.

## Main definitions

* `sourceBehavioralMacroContinuationFamily`.
* `serializedBehavioralMacroContinuationFamily`.
* `behavioralMacroContinuationSimulation`.
* `IsSourceBehavioralMacroNashOnDeclaredContinuations`.
* `IsSerializedBehavioralMacroNashOnDeclaredContinuations`.

## Main results

* `serializedBehavioralMicroPayoffLawFrom_eq`.
* `behavioralMacroContinuationSimulation_sourceRootTotal` and
  `behavioralMacroContinuationSimulation_targetRootTotal`.
* `behavioralMacroNashOnDeclaredRoots_iff`.
* `behavioralMacroNashOnDeclaredContinuations_iff`.
-/

namespace ExtensiveGame.FOSG.Sequentialization

universe uU uV uSA uO uP

variable {n : ℕ} {U : Type uU}
  (G : FOSG.{0, uU, uSA, uSA, uO, uP} (Fin (n + 1)) U)

local instance continuationHistoryKernelActionEmptinessDecidable
    [(world : G.WorldState) → Decidable (G.isTerminal world)] :
    (history : G.historyKernelArena.State) →
      Decidable (IsEmpty (G.historyKernelArena.Action history)) :=
  fun history =>
    decidable_of_iff
      (G.isTerminal history.1)
      (G.historyKernelArena_isTerminal_iff history).symm

/-! ### Exact payoff laws from related macro roots -/

/-- Source optional terminal-payoff law after at most `horizon` FOSG macro
transitions from one augmented history. -/
def sourceBehavioralMacroPayoffLawFrom
    [(world : G.WorldState) →
      Decidable (G.isTerminal world)]
    (D : G.DecisionModel)
    (profile : D.BehavioralProfile)
    (source : G.HistoryState)
    (horizon : ℕ) :
    FiniteLaw (Option (Fin (n + 1) → U)) :=
  G.behavioralPayoffLawFrom D profile source horizon

/-- Genuine serialized micro-step optional terminal-payoff law from one
complete target history.

One source macro transition consumes exactly `n + 2` target micro steps. -/
def serializedBehavioralMicroPayoffLawFrom
    [(world : G.WorldState) →
      Decidable (G.isTerminal world)]
    (D : G.DecisionModel)
    (rootPayoff : Fin (n + 1) → U)
    (sourceDeclaredRoot : G.HistoryState → Prop)
    (profile :
      (observedChanceGame G D rootPayoff
        sourceDeclaredRoot).observed.BehavioralProfile)
    (target :
      (game G rootPayoff).toArena.HistoryFrom
        (game G rootPayoff).init)
    (horizon : ℕ) :
    FiniteLaw (Option (Fin (n + 1) → U)) :=
  ((game G rootPayoff).toArena.stochasticHistoryLawFrom
      (ObservedChanceGame.BehavioralProfile.toHistoryPolicy
        (observedChanceGame G D rootPayoff
          sourceDeclaredRoot)
        profile)
      target (horizon * (n + 2))).map
    (serializedStoppedPayoffAtHistory G rootPayoff)

/-- From every related macro boundary, source behavioral execution and genuine
serialized micro execution have the same optional terminal-payoff law. -/
theorem serializedBehavioralMicroPayoffLawFrom_eq
    [(world : G.WorldState) →
      Decidable (G.isTerminal world)]
    (D : G.DecisionModel)
    (rootPayoff : Fin (n + 1) → U)
    (sourceDeclaredRoot : G.HistoryState → Prop)
    (data : MacroPolicyData G D rootPayoff sourceDeclaredRoot)
    [(targetState :
        (macroExecutionKernelArena G D rootPayoff
          sourceDeclaredRoot).State) →
      Decidable
        (IsEmpty
          ((macroExecutionKernelArena G D rootPayoff
            sourceDeclaredRoot).Action targetState))]
    (profile : D.BehavioralProfile)
    (source : G.HistoryState)
    (target :
      (game G rootPayoff).toArena.HistoryFrom
        (game G rootPayoff).init)
    (hrelated : Rel G source target)
    (horizon : ℕ) :
    (sourceBehavioralMacroPayoffLawFrom
        G D profile source horizon).Equivalent
      (serializedBehavioralMicroPayoffLawFrom
        G D rootPayoff sourceDeclaredRoot
        (serializedObservedBehavioralProfile
          G D rootPayoff sourceDeclaredRoot profile)
        target horizon) := by
  letI sourceTerminalDecision :
      (history : G.HistoryState) →
        Decidable
          (IsEmpty (G.historyKernelArena.Action history)) :=
    fun history =>
      decidable_of_iff
        (G.isTerminal history.1)
        (G.historyKernelArena_isTerminal_iff history).symm
  unfold sourceBehavioralMacroPayoffLawFrom
  unfold serializedBehavioralMicroPayoffLawFrom
  unfold FOSG.behavioralPayoffLawFrom
  change
    ((@KernelArena.stateLawFrom G.historyKernelArena
        sourceTerminalDecision
        (D.behavioralHistoryPolicy profile)
        horizon source).map
          G.stoppedPayoffAtHistory).Equivalent
      (((game G rootPayoff).toArena.stochasticHistoryLawFrom
        (serializedBehavioralHistoryPolicy
          G D rootPayoff sourceDeclaredRoot profile)
        target (horizon * (n + 2))).map
          (serializedStoppedPayoffAtHistory G rootPayoff))
  have hmicro :=
    (serializedBehavioralMicroStateLaw_eq_macro
      G D rootPayoff sourceDeclaredRoot data profile hrelated horizon).map
        (serializedStoppedPayoffAtHistory G rootPayoff)
  exact
    (serializedMacroPayoffLaw_eq
      G D rootPayoff sourceDeclaredRoot data
      (D.behavioralHistoryPolicy profile)
      hrelated horizon).trans hmicro.symm

/-! ### Continuation families and relational simulation -/

/-- Finite-macro-horizon continuation semantics of the augmented FOSG. -/
def sourceBehavioralMacroContinuationFamily
    [(world : G.WorldState) →
      Decidable (G.isTerminal world)]
    (D : G.DecisionModel)
    (sourceDeclaredRoot : G.HistoryState → Prop)
    (horizon : ℕ) :
    ContinuationGameForm (Fin (n + 1)) where
  Strategy := D.BehavioralStrategy
  Root := G.HistoryState
  IsDeclaredRoot := sourceDeclaredRoot
  Outcome := (Option (Fin (n + 1) → U) → ℚ) → ℚ
  outcome := fun source profile =>
    (sourceBehavioralMacroPayoffLawFrom
      G D profile source horizon).expectRat

/-- A genuine serialized history is an admissible proper declared macro root
when it is related to a caller-declared augmented FOSG history.

This excludes only the synthetic initialization root, whose random initial
world is represented by the separate initialized game form. -/
def IsSerializedDeclaredMacroRoot
    [(world : G.WorldState) →
      Decidable (G.isTerminal world)]
    (rootPayoff : Fin (n + 1) → U)
    (sourceDeclaredRoot : G.HistoryState → Prop)
    (target :
      (game G rootPayoff).toArena.HistoryFrom
        (game G rootPayoff).init) : Prop :=
  ∃ source : G.HistoryState,
    sourceDeclaredRoot source ∧
      Rel G source target

/-- Related declared macro roots are exactly the roots in the serialized
EFG's explicit external presentation other than the synthetic
random-initialization root. -/
theorem isSerializedDeclaredMacroRoot_iff
    [(world : G.WorldState) →
      Decidable (G.isTerminal world)]
    (D : G.DecisionModel)
    (rootPayoff : Fin (n + 1) → U)
    (sourceDeclaredRoot : G.HistoryState → Prop)
    (target :
      (game G rootPayoff).toArena.HistoryFrom
        (game G rootPayoff).init) :
    IsSerializedDeclaredMacroRoot
        G rootPayoff sourceDeclaredRoot target ↔
      (rootPresentation G D rootPayoff
        sourceDeclaredRoot).IsRoot target ∧
        target.1 ≠ State.root := by
  constructor
  · rintro ⟨source, hsourceRoot, hrelated⟩
    constructor
    · change
        isDesignatedContinuationRoot
          G sourceDeclaredRoot target.1
      rw [hrelated]
      by_cases hterminal : G.isTerminal source.1
      · simp [isDesignatedContinuationRoot, boundary, hterminal,
          hsourceRoot]
      · simp [isDesignatedContinuationRoot, boundary, hterminal,
          hsourceRoot]
    · intro hroot
      rw [hrelated] at hroot
      by_cases hterminal :
          G.isTerminal source.1
      · simp [boundary, hterminal] at hroot
      · simp [boundary, hterminal] at hroot
  · rintro ⟨htargetRoot, hnotRoot⟩
    change
      isDesignatedContinuationRoot
        G sourceDeclaredRoot target.1 at htargetRoot
    cases hstate : target.1 with
    | root =>
        exact (hnotRoot hstate).elim
    | terminal source hterminal =>
        have hrelated :
            Rel G source target := by
          change target.1 = boundary G source
          rw [hstate,
            boundary_of_terminal
              G source hterminal]
        have hsourceRoot :
            sourceDeclaredRoot source := by
          simpa [isDesignatedContinuationRoot, hstate] using
            htargetRoot
        exact
          ⟨source, hsourceRoot, hrelated⟩
    | player source hnonterminal count
        hcount collected =>
        have hdata :
            count = 0 ∧
              sourceDeclaredRoot source := by
          simpa [isDesignatedContinuationRoot, hstate] using
            htargetRoot
        obtain ⟨hcountZero, hsourceRoot⟩ :=
          hdata
        subst count
        have hcollected :
            collected =
              PartialAction.empty G source.1 := by
          funext i hi
          omega
        have hrelated :
            Rel G source target := by
          change target.1 = boundary G source
          rw [hstate,
            boundary_of_not_terminal
              G source hnonterminal]
          congr
        exact
          ⟨source, hsourceRoot, hrelated⟩
    | chance source hnonterminal action =>
        have : False := by
          simp [isDesignatedContinuationRoot, hstate] at htargetRoot
        exact this.elim

/-- Finite-macro-horizon continuation semantics of genuine serialized EFG
micro execution at proper macro boundaries. -/
def serializedBehavioralMacroContinuationFamily
    [(world : G.WorldState) →
      Decidable (G.isTerminal world)]
    (D : G.DecisionModel)
    (rootPayoff : Fin (n + 1) → U)
    (sourceDeclaredRoot : G.HistoryState → Prop)
    (horizon : ℕ) :
    ContinuationGameForm (Fin (n + 1)) where
  Strategy :=
    (observedChanceGame G D rootPayoff
      sourceDeclaredRoot).observed.BehavioralStrategy
  Root :=
    (game G rootPayoff).toArena.HistoryFrom
      (game G rootPayoff).init
  IsDeclaredRoot :=
    IsSerializedDeclaredMacroRoot
      G rootPayoff sourceDeclaredRoot
  Outcome := (Option (Fin (n + 1) → U) → ℚ) → ℚ
  outcome := fun target profile =>
    (serializedBehavioralMicroPayoffLawFrom
      G D rootPayoff sourceDeclaredRoot
      profile target horizon).expectRat

/-- The weak serializer induces a relational-root continuation simulation
with exact payoff-law semantics. -/
def behavioralMacroContinuationSimulation
    [(world : G.WorldState) →
      Decidable (G.isTerminal world)]
    (D : G.DecisionModel)
    (rootPayoff : Fin (n + 1) → U)
    (sourceDeclaredRoot : G.HistoryState → Prop)
    (data : MacroPolicyData G D rootPayoff sourceDeclaredRoot)
    [(targetState :
        (macroExecutionKernelArena G D rootPayoff
          sourceDeclaredRoot).State) →
      Decidable
        (IsEmpty
          ((macroExecutionKernelArena G D rootPayoff
            sourceDeclaredRoot).Action targetState))]
    (horizon : ℕ) :
    (sourceBehavioralMacroContinuationFamily
      G D sourceDeclaredRoot horizon).Simulation
      (serializedBehavioralMacroContinuationFamily
        G D rootPayoff sourceDeclaredRoot horizon) where
  RootRel := Rel G
  strategyMap := fun i strategy =>
    serializedObservedBehavioralStrategy G D rootPayoff
      sourceDeclaredRoot i strategy
  outcomeMap := id
  map_declaredRoot := by
    intro source target hrelated
    constructor
    · intro hsource
      exact ⟨source, hsource, hrelated⟩
    · rintro ⟨otherSource, hotherRoot,
        hotherRelated⟩
      have hsame :
          otherSource = source :=
        Rel.left_unique G
          hotherRelated hrelated
      simpa [hsame] using hotherRoot
  map_outcome := by
    intro source target hrelated profile
    funext value
    exact
      serializedBehavioralMicroPayoffLawFrom_eq
        G D rootPayoff sourceDeclaredRoot data
        profile source target hrelated horizon value

/-- Every syntactic augmented FOSG history has at least one genuine serialized
target history reaching its macro boundary. -/
theorem exists_relatedTargetHistory
    [(world : G.WorldState) →
      Decidable (G.isTerminal world)]
    (rootPayoff : Fin (n + 1) → U)
    (fallback : FallbackHistoryPolicy G rootPayoff)
    (source : G.HistoryState) :
    ∃ target :
        (game G rootPayoff).toArena.HistoryFrom
          (game G rootPayoff).init,
      Rel G source target := by
  rcases source with ⟨world, history⟩
  induction history with
  | initial world =>
      let source :
          G.HistoryState :=
        ⟨world, FOSG.History.initial world⟩
      let target :
          (game G rootPayoff).toArena.HistoryFrom
            (game G rootPayoff).init :=
        ⟨boundary G source,
          (Arena.History.nil :
            (game G rootPayoff).toArena.History
              (game G rootPayoff).init
              (game G rootPayoff).init).snoc world⟩
      exact ⟨target, rfl⟩
  | @snoc world history jointAction nextWorld ih =>
      let source :
          G.HistoryState :=
        ⟨world, history⟩
      obtain ⟨target, hrelated⟩ := ih
      obtain
          ⟨targetEndpoint, htargetLaw,
            htargetBoundary⟩ :=
        exists_macroExecutionLaw
          G rootPayoff fallback source jointAction
          target hrelated
      exact
        ⟨targetEndpoint nextWorld,
          htargetBoundary nextWorld⟩

/-! ### Instantiation of the reusable behavioral bridge -/

/-- The concrete finite-player sequential compiler realizes the generic
behavioral semantics of a weak FOSG serialization.

The playerwise equivalence is supplied explicitly because the source may
contain unrepresented information coordinates.  The target laws execute the
genuine serialized micro game: one
initial chance step followed by `n + 2` micro steps per source macro step. -/
def behavioralWeakSerializationBridge
    [(world : G.WorldState) →
      Decidable (G.isTerminal world)]
    (D : G.DecisionModel)
    (rootPayoff : Fin (n + 1) → U)
    (sourceDeclaredRoot : G.HistoryState → Prop)
    (data : MacroPolicyData G D rootPayoff sourceDeclaredRoot)
    [(targetState :
        (macroExecutionKernelArena G D rootPayoff
          sourceDeclaredRoot).State) →
      Decidable
        (IsEmpty
          ((macroExecutionKernelArena G D rootPayoff
            sourceDeclaredRoot).Action targetState))]
    (certificate :
      BehavioralStrategyEquivalence G D rootPayoff sourceDeclaredRoot) :
    (weakSerialization
      G D rootPayoff data.micro sourceDeclaredRoot).BehavioralBridge D where
  strategyEquiv := certificate.strategyEquiv
  targetPayoffLawFrom :=
    serializedBehavioralMicroPayoffLawFrom
      G D rootPayoff sourceDeclaredRoot
  map_payoffLawFrom := by
    intro source target hrelated profile horizon
    have hprofile :
        (fun i => certificate.strategyEquiv i (profile i)) =
          serializedObservedBehavioralProfile G D rootPayoff
            sourceDeclaredRoot profile := by
      funext i information
      exact certificate.strategyEquiv_apply i (profile i) information
    rw [hprofile]
    exact
      (serializedBehavioralMicroPayoffLawFrom_eq
        G D rootPayoff sourceDeclaredRoot data
        profile source target hrelated horizon).symm
  sourceRootTotal := by
    intro source hsourceRoot
    exact
      exists_relatedTargetHistory
        G rootPayoff data.micro source
  targetInitialPayoffLaw := fun profile horizon =>
    ((game G rootPayoff).toArena.stochasticHistoryLawFrom
        (ObservedChanceGame.BehavioralProfile.toHistoryPolicy
          (observedChanceGame
            G D rootPayoff sourceDeclaredRoot)
          profile)
        (Arena.HistoryFrom.nil
          (game G rootPayoff).toArena
          (game G rootPayoff).init)
        (1 + horizon * (n + 2))).map
      (serializedStoppedPayoffAtHistory G rootPayoff)
  map_initialPayoffLaw := by
    intro profile horizon
    have hprofile :
        (fun i => certificate.strategyEquiv i (profile i)) =
          serializedObservedBehavioralProfile G D rootPayoff
            sourceDeclaredRoot profile := by
      funext i information
      exact certificate.strategyEquiv_apply i (profile i) information
    rw [hprofile]
    change
      ((initializedBehavioralTargetMicroStateLaw G D rootPayoff
          sourceDeclaredRoot profile horizon).map
        (serializedStoppedPayoffAtHistory G rootPayoff)).Equivalent
      ((initializedSourceStateLaw G
          (D.behavioralHistoryPolicy profile) horizon).map
        G.stoppedPayoffAtHistory)
    exact
      (initializedBehavioralMicroPayoffLaw_eq
        G D rootPayoff sourceDeclaredRoot data
        profile horizon).symm

/-- The macro continuation simulation covers every admissible source root. -/
theorem behavioralMacroContinuationSimulation_sourceRootTotal
    [(world : G.WorldState) →
      Decidable (G.isTerminal world)]
    (D : G.DecisionModel)
    (rootPayoff : Fin (n + 1) → U)
    (sourceDeclaredRoot : G.HistoryState → Prop)
    (data : MacroPolicyData G D rootPayoff sourceDeclaredRoot)
    [(targetState :
        (macroExecutionKernelArena G D rootPayoff
          sourceDeclaredRoot).State) →
      Decidable
        (IsEmpty
          ((macroExecutionKernelArena G D rootPayoff
            sourceDeclaredRoot).Action targetState))]
    (horizon : ℕ) :
    (behavioralMacroContinuationSimulation
      G D rootPayoff sourceDeclaredRoot data
      horizon).SourceRootTotal := by
  intro source hsource
  exact
    exists_relatedTargetHistory
      G rootPayoff data.micro source

/-- The target continuation-root predicate records exactly the witness needed
for target-root coverage. -/
theorem behavioralMacroContinuationSimulation_targetRootTotal
    [(world : G.WorldState) →
      Decidable (G.isTerminal world)]
    (D : G.DecisionModel)
    (rootPayoff : Fin (n + 1) → U)
    (sourceDeclaredRoot : G.HistoryState → Prop)
    (data : MacroPolicyData G D rootPayoff sourceDeclaredRoot)
    [(targetState :
        (macroExecutionKernelArena G D rootPayoff
          sourceDeclaredRoot).State) →
      Decidable
        (IsEmpty
          ((macroExecutionKernelArena G D rootPayoff
            sourceDeclaredRoot).Action targetState))]
    (horizon : ℕ) :
    (behavioralMacroContinuationSimulation
      G D rootPayoff sourceDeclaredRoot data
      horizon).TargetRootTotal := by
  intro target htarget
  obtain
      ⟨source, hsource, hrelated⟩ :=
    htarget
  exact ⟨source, hrelated⟩

/-- Behavioral strategy compilation is surjective because the serializer
reuses the source decision information and abstract action types exactly. -/
theorem behavioralMacroContinuationSimulation_strategySurjective
    [(world : G.WorldState) →
      Decidable (G.isTerminal world)]
    (D : G.DecisionModel)
    (rootPayoff : Fin (n + 1) → U)
    (sourceDeclaredRoot : G.HistoryState → Prop)
    (data : MacroPolicyData G D rootPayoff sourceDeclaredRoot)
    [(targetState :
        (macroExecutionKernelArena G D rootPayoff
          sourceDeclaredRoot).State) →
      Decidable
        (IsEmpty
          ((macroExecutionKernelArena G D rootPayoff
            sourceDeclaredRoot).Action targetState))]
    (certificate :
      BehavioralStrategyEquivalence G D rootPayoff sourceDeclaredRoot)
    (horizon : ℕ) :
    (behavioralMacroContinuationSimulation
      G D rootPayoff sourceDeclaredRoot data
      horizon).StrategySurjective := by
  intro i targetStrategy
  refine ⟨(certificate.strategyEquiv i).symm targetStrategy, ?_⟩
  funext information
  change
    serializedObservedBehavioralStrategy G D rootPayoff
        sourceDeclaredRoot i
        ((certificate.strategyEquiv i).symm targetStrategy) information =
      targetStrategy information
  rw [show
    serializedObservedBehavioralStrategy G D rootPayoff
        sourceDeclaredRoot i
        ((certificate.strategyEquiv i).symm targetStrategy) information =
      certificate.strategyEquiv i
        ((certificate.strategyEquiv i).symm targetStrategy) information by
      exact (certificate.strategyEquiv_apply i _ information).symm]
  exact congrFun
    ((certificate.strategyEquiv i).apply_symm_apply targetStrategy)
    information

/-- The macro continuation simulation preserves a common root-independent
functional on optional terminal-payoff laws. -/
theorem behavioralMacroContinuationSimulation_utilityCompatible
    [(world : G.WorldState) →
      Decidable (G.isTerminal world)]
    (D : G.DecisionModel)
    (rootPayoff : Fin (n + 1) → U)
    (sourceDeclaredRoot : G.HistoryState → Prop)
    (data : MacroPolicyData G D rootPayoff sourceDeclaredRoot)
    [(targetState :
        (macroExecutionKernelArena G D rootPayoff
          sourceDeclaredRoot).State) →
      Decidable
        (IsEmpty
          ((macroExecutionKernelArena G D rootPayoff
            sourceDeclaredRoot).Action targetState))]
    (horizon : ℕ)
    (utility :
      ((Option (Fin (n + 1) → U) → ℚ) → ℚ) →
        Fin (n + 1) → V) :
    (behavioralMacroContinuationSimulation
      G D rootPayoff sourceDeclaredRoot data
      horizon).UtilityCompatible
        (fun _ => utility)
        (fun _ => utility) := by
  intro source target hrelated outcome i
  rfl

/-! ### Behavioral macro-Nash on declared continuation roots -/

/-- Finite-horizon behavioral Nash equilibrium at every declared FOSG macro
root. The root predicate is caller supplied and does not itself certify
standard subgames. -/
def IsSourceBehavioralMacroNashOnDeclaredRoots
    [(world : G.WorldState) →
      Decidable (G.isTerminal world)]
    [DecidableEq (Fin (n + 1))]
    {V : Type uV} [Preorder V]
    (D : G.DecisionModel)
    (sourceDeclaredRoot : G.HistoryState → Prop)
    (utility :
      ((Option (Fin (n + 1) → U) → ℚ) → ℚ) →
        Fin (n + 1) → V)
    (profile : D.BehavioralProfile)
    (horizon : ℕ) : Prop :=
  (sourceBehavioralMacroContinuationFamily
    G D sourceDeclaredRoot horizon
    ).IsNashOnRoots
      (fun _ => utility) profile

/-- Finite-horizon behavioral Nash equilibrium of genuine serialized micro
execution at every related declared macro root. -/
def IsSerializedBehavioralMacroNashOnDeclaredRoots
    [(world : G.WorldState) →
      Decidable (G.isTerminal world)]
    [DecidableEq (Fin (n + 1))]
    {V : Type uV} [Preorder V]
    (D : G.DecisionModel)
    (rootPayoff : Fin (n + 1) → U)
    (sourceDeclaredRoot : G.HistoryState → Prop)
    (utility :
      ((Option (Fin (n + 1) → U) → ℚ) → ℚ) →
        Fin (n + 1) → V)
    (profile :
      (observedChanceGame G D rootPayoff
        sourceDeclaredRoot).observed.BehavioralProfile)
    (horizon : ℕ) : Prop :=
  (serializedBehavioralMacroContinuationFamily
    G D rootPayoff sourceDeclaredRoot horizon
    ).IsNashOnRoots
      (fun _ => utility) profile

/-- Finite-horizon behavioral Nash on declared macro roots transfers in both
directions through the weak serializer. -/
theorem behavioralMacroNashOnDeclaredRoots_iff
    [(world : G.WorldState) →
      Decidable (G.isTerminal world)]
    [DecidableEq (Fin (n + 1))]
    {V : Type uV} [Preorder V]
    (D : G.DecisionModel)
    (rootPayoff : Fin (n + 1) → U)
    (sourceDeclaredRoot : G.HistoryState → Prop)
    (data : MacroPolicyData G D rootPayoff sourceDeclaredRoot)
    [(targetState :
        (macroExecutionKernelArena G D rootPayoff
          sourceDeclaredRoot).State) →
      Decidable
        (IsEmpty
          ((macroExecutionKernelArena G D rootPayoff
            sourceDeclaredRoot).Action targetState))]
    (certificate :
      BehavioralStrategyEquivalence G D rootPayoff sourceDeclaredRoot)
    (utility :
      ((Option (Fin (n + 1) → U) → ℚ) → ℚ) →
        Fin (n + 1) → V)
    (profile : D.BehavioralProfile)
    (horizon : ℕ) :
    IsSourceBehavioralMacroNashOnDeclaredRoots
        G D sourceDeclaredRoot utility
        profile horizon ↔
      IsSerializedBehavioralMacroNashOnDeclaredRoots
        G D rootPayoff sourceDeclaredRoot
        utility
        (serializedObservedBehavioralProfile
          G D rootPayoff sourceDeclaredRoot
          profile)
        horizon := by
  exact
    (behavioralMacroContinuationSimulation
      G D rootPayoff sourceDeclaredRoot data horizon).isNashOnRoots_iff_of_total
        (behavioralMacroContinuationSimulation_utilityCompatible
          G D rootPayoff sourceDeclaredRoot data horizon utility)
        (behavioralMacroContinuationSimulation_strategySurjective
          G D rootPayoff sourceDeclaredRoot data certificate horizon)
        (behavioralMacroContinuationSimulation_sourceRootTotal
          G D rootPayoff sourceDeclaredRoot data horizon)
        (behavioralMacroContinuationSimulation_targetRootTotal
          G D rootPayoff sourceDeclaredRoot data horizon)
        profile

/-- Full finite-macro-horizon behavioral Nash on presentation-designated continuations on the source: Nash at the random
initialization root and Nash at every admissible proper macro continuation. -/
def IsSourceBehavioralMacroNashOnDeclaredContinuations
    [(world : G.WorldState) →
      Decidable (G.isTerminal world)]
    [DecidableEq (Fin (n + 1))]
    {V : Type uV} [Preorder V]
    (D : G.DecisionModel)
    (sourceDeclaredRoot : G.HistoryState → Prop)
    (utility :
      ((Option (Fin (n + 1) → U) → ℚ) → ℚ) →
        Fin (n + 1) → V)
    (profile : D.BehavioralProfile)
    (horizon : ℕ) : Prop :=
  (sourceBehavioralGameForm
      G D horizon).IsNash utility profile ∧
    IsSourceBehavioralMacroNashOnDeclaredRoots
      G D sourceDeclaredRoot utility
      profile horizon

/-- Full finite-macro-horizon behavioral Nash on presentation-designated continuations on the serialized target: Nash
at the synthetic random-initialization root and at every admissible proper
macro continuation under genuine micro execution. -/
def IsSerializedBehavioralMacroNashOnDeclaredContinuations
    [(world : G.WorldState) →
      Decidable (G.isTerminal world)]
    [DecidableEq (Fin (n + 1))]
    {V : Type uV} [Preorder V]
    (D : G.DecisionModel)
    (rootPayoff : Fin (n + 1) → U)
    (sourceDeclaredRoot : G.HistoryState → Prop)
    (utility :
      ((Option (Fin (n + 1) → U) → ℚ) → ℚ) →
        Fin (n + 1) → V)
    (profile :
      (observedChanceGame G D rootPayoff
        sourceDeclaredRoot).observed.BehavioralProfile)
    (horizon : ℕ) : Prop :=
  (serializedBehavioralGameForm
      G D rootPayoff sourceDeclaredRoot
      horizon).IsNash utility profile ∧
    IsSerializedBehavioralMacroNashOnDeclaredRoots
      G D rootPayoff sourceDeclaredRoot
      utility profile horizon

/-- The concrete weak/stuttering FOSG serialization preserves full
finite-macro-horizon behavioral Nash on presentation-designated continuations in both directions.

Initialization uses the exact initialized game-form isomorphism; every proper
caller-declared macro continuation uses the relational-root continuation
simulation. -/
theorem behavioralMacroNashOnDeclaredContinuations_iff
    [(world : G.WorldState) →
      Decidable (G.isTerminal world)]
    [DecidableEq (Fin (n + 1))]
    {V : Type uV} [Preorder V]
    (D : G.DecisionModel)
    (rootPayoff : Fin (n + 1) → U)
    (sourceDeclaredRoot : G.HistoryState → Prop)
    (data : MacroPolicyData G D rootPayoff sourceDeclaredRoot)
    [(targetState :
        (macroExecutionKernelArena G D rootPayoff
          sourceDeclaredRoot).State) →
      Decidable
        (IsEmpty
          ((macroExecutionKernelArena G D rootPayoff
            sourceDeclaredRoot).Action targetState))]
    (certificate :
      BehavioralStrategyEquivalence G D rootPayoff sourceDeclaredRoot)
    (utility :
      ((Option (Fin (n + 1) → U) → ℚ) → ℚ) →
        Fin (n + 1) → V)
    (profile : D.BehavioralProfile)
    (horizon : ℕ) :
    IsSourceBehavioralMacroNashOnDeclaredContinuations
        G D sourceDeclaredRoot utility
        profile horizon ↔
      IsSerializedBehavioralMacroNashOnDeclaredContinuations
        G D rootPayoff sourceDeclaredRoot
        utility
        (serializedObservedBehavioralProfile
          G D rootPayoff sourceDeclaredRoot
          profile)
        horizon := by
  let iso :=
    behavioralGameFormIso G D rootPayoff
      sourceDeclaredRoot data certificate horizon
  have hprofile :
      iso.mapProfile profile =
        serializedObservedBehavioralProfile G D rootPayoff
          sourceDeclaredRoot profile := by
    funext i information
    exact certificate.strategyEquiv_apply i (profile i) information
  have hinitial :=
    behavioralIsNash_iff G D rootPayoff sourceDeclaredRoot
      data certificate horizon utility profile
  change
    (sourceBehavioralGameForm G D horizon).IsNash utility profile ↔
      (serializedBehavioralGameForm G D rootPayoff sourceDeclaredRoot
        horizon).IsNash utility (iso.mapProfile profile) at hinitial
  rw [hprofile] at hinitial
  exact and_congr hinitial
    (behavioralMacroNashOnDeclaredRoots_iff G D rootPayoff
      sourceDeclaredRoot data certificate utility profile horizon)

end ExtensiveGame.FOSG.Sequentialization
