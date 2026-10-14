/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.FOSG.FOSG
import EconCSLib.GameTheory.ExtensiveGame.Observed.Behavior
import EconCSLib.GameTheory.GameForm.Continuation.Iso

/-!
# EconCSLib.GameTheory.ExtensiveGame.FOSG.FOSGBehavioralSerialization

Reusable behavioral theorem-transfer interface for weak FOSG serializations.

`FOSG.WeakSerialization` is deliberately operational: one augmented FOSG
macro step is coupled to a positive finite target execution, while
observations, public states, terminal payoffs, and caller-declared continuation
roots are preserved at related macro boundaries.  Operational correctness
alone does not identify
which complete behavioral target profile realizes a source profile, nor does
it package an iterated payoff law.

`WeakSerialization.BehavioralBridge` supplies exactly that strategic semantic
layer:

* a per-player equivalence between source decision-model behavioral strategies
  and target observed-EFG behavioral strategies;
* a target finite-horizon optional terminal-payoff law from every target root;
* exact equality with the canonical source FOSG payoff law at every related
  macro root;
* coverage of every admissible source root;
* a target initialized payoff law exactly matching random FOSG
  initialization.

From these fields this module constructs, generically:

* source and target continuation families;
* a relational-root `ContinuationGameForm.Simulation`;
* an initialized `GameForm.Iso`;
* two-way behavioral Nash transfer over caller-declared macro roots.

Thus a new serializer proves its operational coupling once, proves that its
actual behavioral execution realizes the bridge laws, and inherits the
equilibrium theorem without repeating deviation or subgame reasoning.

## Main definitions

* `FOSG.behavioralPayoffLawFrom` and `behavioralInitialPayoffLaw`.
* `FOSG.WeakSerialization.BehavioralBridge`.
* `BehavioralBridge.sourceContinuationFamily` and
  `targetContinuationFamily`.
* `BehavioralBridge.continuationSimulation`.
* `BehavioralBridge.initialGameFormIso`.
* `BehavioralBridge.IsSourceMacroNashOnDeclaredContinuations` and `IsTargetMacroNashOnDeclaredContinuations`.

## Main results

* `BehavioralBridge.macroNashOnDeclaredRoots_iff`.
* `BehavioralBridge.initialIsNash_iff`.
* `BehavioralBridge.macroNashOnDeclaredContinuations_iff`.
-/

namespace ExtensiveGame

universe uU uV

namespace FOSG

variable {k : ℕ} {U : Type uU}

/-- Canonical finite-horizon optional terminal-payoff law of a decision-model
behavioral profile from one augmented FOSG history. -/
def behavioralPayoffLawFrom
    (G : FOSG (Fin k) U)
    [(world : G.WorldState) → Decidable (G.isTerminal world)]
    (D : G.DecisionModel)
    (profile : D.BehavioralProfile)
    (source : G.HistoryState)
    (horizon : ℕ) :
    FiniteLaw (Option (Fin k → U)) := by
  letI (history : G.HistoryState) :
      Decidable
        (IsEmpty (G.historyKernelArena.Action history)) :=
    decidable_of_iff
      (G.isTerminal history.1)
      (G.historyKernelArena_isTerminal_iff history).symm
  exact
    (G.historyKernelArena.stateLawFrom
        (D.behavioralHistoryPolicy profile)
        horizon source).map
      G.stoppedPayoffAtHistory

/-- Canonical finite-horizon optional terminal-payoff law after random FOSG
initialization. -/
def behavioralInitialPayoffLaw
    (G : FOSG (Fin k) U)
    [(world : G.WorldState) → Decidable (G.isTerminal world)]
    (D : G.DecisionModel)
    (profile : D.BehavioralProfile)
    (horizon : ℕ) :
    FiniteLaw (Option (Fin k → U)) := by
  letI (history : G.HistoryState) :
      Decidable
        (IsEmpty (G.historyKernelArena.Action history)) :=
    decidable_of_iff
      (G.isTerminal history.1)
      (G.historyKernelArena_isTerminal_iff history).symm
  exact
    (G.initialHistoryKernel.bind
        (G.historyKernelArena.stateLawFrom
          (D.behavioralHistoryPolicy profile)
          horizon)).map
      G.stoppedPayoffAtHistory

@[simp]
theorem behavioralPayoffLawFrom_zero
    (G : FOSG (Fin k) U)
    [(world : G.WorldState) → Decidable (G.isTerminal world)]
    (D : G.DecisionModel)
    (profile : D.BehavioralProfile)
    (source : G.HistoryState) :
    G.behavioralPayoffLawFrom D profile source 0 =
      FiniteLaw.pure (G.stoppedPayoffAtHistory source) := by
  rw [behavioralPayoffLawFrom]
  change
    FiniteLaw.map G.stoppedPayoffAtHistory (FiniteLaw.pure source) =
      FiniteLaw.pure (G.stoppedPayoffAtHistory source)
  exact FiniteLaw.pure_map _ _

theorem behavioralPayoffLawFrom_zero_of_not_terminal
    (G : FOSG (Fin k) U)
    [(world : G.WorldState) → Decidable (G.isTerminal world)]
    (D : G.DecisionModel)
    (profile : D.BehavioralProfile)
    (source : G.HistoryState)
    (hnonterminal : ¬ G.isTerminal source.1) :
    G.behavioralPayoffLawFrom D profile source 0 =
      FiniteLaw.pure none := by
  rw [behavioralPayoffLawFrom_zero]
  simp [hnonterminal]

namespace WeakSerialization

variable {G : FOSG (Fin k) U}
variable [(world : G.WorldState) → Decidable (G.isTerminal world)]
variable {H : ObservedChanceGame (Fin k) U}
variable
  [(state : H.observed.base.State) →
    Decidable (H.observed.base.isTerminal state)]

/-- Strategic and finite-horizon semantic realization of an operational weak
serialization.

The target payoff-law fields are intentionally abstract.  Different
serializers may use a fixed micro-step multiplier, variable-length macro
execution, or a direct macro controller.  The bridge only requires the final
law equality needed by representation-neutral theorem transfer. -/
structure BehavioralBridge
    (S : G.WeakSerialization H)
    (D : G.DecisionModel) where
  /-- Equivalence between every player's source and target behavioral
  strategy spaces. -/
  strategyEquiv :
    (i : Fin k) →
      D.BehavioralStrategy i ≃
        H.observed.BehavioralStrategy i
  /-- Target optional terminal-payoff law from a complete target history at a
  requested source macro horizon. -/
  targetPayoffLawFrom :
    H.observed.BehavioralProfile →
      H.observed.base.toArena.HistoryFrom
        H.observed.base.init →
      ℕ → FiniteLaw (Option (Fin k → U))
  /-- Exact payoff-law naturality at every related macro root. -/
  map_payoffLawFrom :
    ∀ (source : G.HistoryState)
      (target :
        H.observed.base.toArena.HistoryFrom
          H.observed.base.init),
      S.simulation.Rel source target →
      ∀ (profile : D.BehavioralProfile)
        (horizon : ℕ),
        (targetPayoffLawFrom
            (fun i =>
              strategyEquiv i (profile i))
            target horizon).Equivalent
          (G.behavioralPayoffLawFrom
            D profile source horizon)
  /-- Every caller-declared source continuation root has at least one related
  target history. -/
  sourceRootTotal :
    ∀ source : G.HistoryState,
      S.IsDeclaredMacroRoot source →
        ∃ target :
            H.observed.base.toArena.HistoryFrom
              H.observed.base.init,
          S.simulation.Rel source target
  /-- Target optional terminal-payoff law after serializer-specific
  initialization. -/
  targetInitialPayoffLaw :
    H.observed.BehavioralProfile →
      ℕ → FiniteLaw (Option (Fin k → U))
  /-- Exact payoff-law naturality at the random initialization root. -/
  map_initialPayoffLaw :
    ∀ (profile : D.BehavioralProfile)
      (horizon : ℕ),
      (targetInitialPayoffLaw
          (fun i =>
            strategyEquiv i (profile i))
          horizon).Equivalent
        (G.behavioralInitialPayoffLaw
          D profile horizon)

namespace BehavioralBridge

variable {S : G.WeakSerialization H}
variable {D : G.DecisionModel}

/-- Map a complete source behavioral profile through the playerwise strategy
equivalences of the bridge. -/
def mapProfile
    (B : S.BehavioralBridge D)
    (profile : D.BehavioralProfile) :
    H.observed.BehavioralProfile :=
  fun i => B.strategyEquiv i (profile i)

@[simp]
theorem mapProfile_apply
    (B : S.BehavioralBridge D)
    (profile : D.BehavioralProfile)
    (i : Fin k) :
    B.mapProfile profile i =
      B.strategyEquiv i (profile i) :=
  rfl

/-- Target declared macro roots represented by the weak simulation relation.

The target's synthetic initialization root is handled separately by the
initialized game form. -/
def IsTargetDeclaredMacroRoot
    (_B : S.BehavioralBridge D)
    (target :
      H.observed.base.toArena.HistoryFrom
        H.observed.base.init) : Prop :=
  ∃ source : G.HistoryState,
    S.IsDeclaredMacroRoot source ∧
      S.simulation.Rel source target

/-- The bridge target-root predicate is always a subpredicate of the
serialization's explicit target-root presentation. -/
theorem targetDeclaredMacroRoot_isTargetRoot
    (B : S.BehavioralBridge D)
    {target :
      H.observed.base.toArena.HistoryFrom
        H.observed.base.init}
    (htarget :
      B.IsTargetDeclaredMacroRoot target) :
    S.targetRoots.IsRoot target := by
  obtain
      ⟨source, hsourceRoot, hrelated⟩ :=
    htarget
  exact
    (S.declaredMacroRoot_iff
      source target hrelated).mp hsourceRoot

/-- Source continuation-family payoff semantics supplied canonically by the
FOSG decision model. -/
def sourceContinuationFamily
    (_B : S.BehavioralBridge D)
    (horizon : ℕ) :
    ContinuationGameForm (Fin k) where
  Strategy := D.BehavioralStrategy
  Root := G.HistoryState
  IsDeclaredRoot := S.IsDeclaredMacroRoot
  Outcome := (Option (Fin k → U) → ℚ) → ℚ
  outcome := fun source profile =>
    (G.behavioralPayoffLawFrom
      D profile source horizon).expectRat

/-- Target continuation-family payoff semantics supplied by the bridge. -/
def targetContinuationFamily
    (B : S.BehavioralBridge D)
    (horizon : ℕ) :
    ContinuationGameForm (Fin k) where
  Strategy := H.observed.BehavioralStrategy
  Root :=
    H.observed.base.toArena.HistoryFrom
      H.observed.base.init
  IsDeclaredRoot :=
    B.IsTargetDeclaredMacroRoot
  Outcome := (Option (Fin k → U) → ℚ) → ℚ
  outcome := fun target profile =>
    (B.targetPayoffLawFrom
      profile target horizon).expectRat

/-- Every behavioral bridge induces an exact relational-root continuation
simulation. -/
def continuationSimulation
    (B : S.BehavioralBridge D)
    (horizon : ℕ) :
    (B.sourceContinuationFamily
      horizon).Simulation
      (B.targetContinuationFamily horizon) where
  RootRel := S.simulation.Rel
  strategyMap := fun i =>
    B.strategyEquiv i
  outcomeMap := id
  map_declaredRoot := by
    intro source target hrelated
    constructor
    · intro hsourceRoot
      exact
        ⟨source, hsourceRoot, hrelated⟩
    · intro htargetRoot
      have htargetObserved :
          S.targetRoots.IsRoot target :=
        B.targetDeclaredMacroRoot_isTargetRoot
          htargetRoot
      exact
        (S.declaredMacroRoot_iff
          source target hrelated).mpr
          htargetObserved
  map_outcome := by
    intro source target hrelated profile
    exact
      funext fun value =>
        (B.map_payoffLawFrom
          source target hrelated profile horizon value).symm

/-- The continuation simulation covers every admissible source root. -/
theorem continuationSimulation_sourceRootTotal
    (B : S.BehavioralBridge D)
    (horizon : ℕ) :
    (B.continuationSimulation
      horizon).SourceRootTotal := by
  intro source hsourceRoot
  exact B.sourceRootTotal source hsourceRoot

/-- The target macro-root predicate makes target-root coverage immediate. -/
theorem continuationSimulation_targetRootTotal
    (B : S.BehavioralBridge D)
    (horizon : ℕ) :
    (B.continuationSimulation
      horizon).TargetRootTotal := by
  intro target htargetRoot
  obtain
      ⟨source, hsourceRoot, hrelated⟩ :=
    htargetRoot
  exact ⟨source, hrelated⟩

/-- Strategy equivalences make the continuation simulation
strategy-surjective. -/
theorem continuationSimulation_strategySurjective
    (B : S.BehavioralBridge D)
    (horizon : ℕ) :
    (B.continuationSimulation
      horizon).StrategySurjective := by
  intro i targetStrategy
  exact
    ⟨(B.strategyEquiv i).symm targetStrategy,
      (B.strategyEquiv i).apply_symm_apply
        targetStrategy⟩

/-- The continuation simulation preserves a common root-independent
functional on optional terminal-payoff laws. -/
theorem continuationSimulation_utilityCompatible
    (B : S.BehavioralBridge D)
    (horizon : ℕ)
    (utility :
      ((Option (Fin k → U) → ℚ) → ℚ) → Fin k → V) :
    (B.continuationSimulation
      horizon).UtilityCompatible
        (fun _ => utility)
        (fun _ => utility) := by
  intro source target hrelated outcome i
  rfl

/-- Source game form at the random initialization root. -/
def sourceInitialGameForm
    (_B : S.BehavioralBridge D)
    (horizon : ℕ) :
    GameForm (Fin k) where
  Strategy := D.BehavioralStrategy
  Outcome := (Option (Fin k → U) → ℚ) → ℚ
  outcome := fun profile =>
    (G.behavioralInitialPayoffLaw
      D profile horizon).expectRat

/-- Target game form at its serializer-specific initialization root. -/
def targetInitialGameForm
    (B : S.BehavioralBridge D)
    (horizon : ℕ) :
    GameForm (Fin k) where
  Strategy := H.observed.BehavioralStrategy
  Outcome := (Option (Fin k → U) → ℚ) → ℚ
  outcome := fun profile =>
    (B.targetInitialPayoffLaw
      profile horizon).expectRat

/-- Exact game-form isomorphism at random initialization. -/
def initialGameFormIso
    (B : S.BehavioralBridge D)
    (horizon : ℕ) :
    (B.sourceInitialGameForm horizon).Iso
      (B.targetInitialGameForm horizon) where
  strategyEquiv := B.strategyEquiv
  outcomeEquiv := Equiv.refl _
  map_outcome := by
    intro profile
    exact
      funext fun value =>
        (B.map_initialPayoffLaw
          profile horizon value).symm

/-- Behavioral Nash equilibrium at every declared source macro root. -/
def IsSourceMacroNashOnDeclaredRoots
    [DecidableEq (Fin k)] [Preorder V]
    (B : S.BehavioralBridge D)
    (utility :
      ((Option (Fin k → U) → ℚ) → ℚ) → Fin k → V)
    (profile : D.BehavioralProfile)
    (horizon : ℕ) : Prop :=
  (B.sourceContinuationFamily
    horizon).IsNashOnRoots
      (fun _ => utility) profile

/-- Behavioral Nash equilibrium at every related target macro root. -/
def IsTargetMacroNashOnDeclaredRoots
    [DecidableEq (Fin k)] [Preorder V]
    (B : S.BehavioralBridge D)
    (utility :
      ((Option (Fin k → U) → ℚ) → ℚ) → Fin k → V)
    (profile : H.observed.BehavioralProfile)
    (horizon : ℕ) : Prop :=
  (B.targetContinuationFamily
    horizon).IsNashOnRoots
      (fun _ => utility) profile

/-- Every behavioral bridge preserves macro-root Nash on presentation-designated continuations in both directions. -/
theorem macroNashOnDeclaredRoots_iff
    [DecidableEq (Fin k)] [Preorder V]
    (B : S.BehavioralBridge D)
    (utility :
      ((Option (Fin k → U) → ℚ) → ℚ) → Fin k → V)
    (profile : D.BehavioralProfile)
    (horizon : ℕ) :
    B.IsSourceMacroNashOnDeclaredRoots
        utility profile horizon ↔
      B.IsTargetMacroNashOnDeclaredRoots
        utility (B.mapProfile profile)
        horizon := by
  exact
    (B.continuationSimulation
      horizon).isNashOnRoots_iff_of_total
        (B.continuationSimulation_utilityCompatible
          horizon utility)
        (B.continuationSimulation_strategySurjective
          horizon)
        (B.continuationSimulation_sourceRootTotal
          horizon)
        (B.continuationSimulation_targetRootTotal
          horizon)
        profile

/-- Initialized behavioral Nash equilibrium transfers in both directions. -/
theorem initialIsNash_iff
    [DecidableEq (Fin k)] [Preorder V]
    (B : S.BehavioralBridge D)
    (utility :
      ((Option (Fin k → U) → ℚ) → ℚ) → Fin k → V)
    (profile : D.BehavioralProfile)
    (horizon : ℕ) :
    (B.sourceInitialGameForm
      horizon).IsNash utility profile ↔
      (B.targetInitialGameForm
        horizon).IsNash
          utility (B.mapProfile profile) := by
  exact
    (B.initialGameFormIso
      horizon).isNash_iff
        (by
          intro outcome i
          rfl)
        profile

/-- Full finite-horizon macro-Nash on presentation-designated continuations on the source: Nash after random
initialization and Nash at every declared proper macro root. -/
def IsSourceMacroNashOnDeclaredContinuations
    [DecidableEq (Fin k)] [Preorder V]
    (B : S.BehavioralBridge D)
    (utility :
      ((Option (Fin k → U) → ℚ) → ℚ) → Fin k → V)
    (profile : D.BehavioralProfile)
    (horizon : ℕ) : Prop :=
  (B.sourceInitialGameForm
      horizon).IsNash utility profile ∧
    B.IsSourceMacroNashOnDeclaredRoots
      utility profile horizon

/-- Full finite-horizon macro-Nash on presentation-designated continuations on the target: initialized Nash and Nash at
every related proper macro root. -/
def IsTargetMacroNashOnDeclaredContinuations
    [DecidableEq (Fin k)] [Preorder V]
    (B : S.BehavioralBridge D)
    (utility :
      ((Option (Fin k → U) → ℚ) → ℚ) → Fin k → V)
    (profile : H.observed.BehavioralProfile)
    (horizon : ℕ) : Prop :=
  (B.targetInitialGameForm
      horizon).IsNash utility profile ∧
    B.IsTargetMacroNashOnDeclaredRoots
      utility profile horizon

/-- Every behavioral weak-serialization bridge preserves full
finite-horizon macro-Nash on presentation-designated continuations in both directions. -/
theorem macroNashOnDeclaredContinuations_iff
    [DecidableEq (Fin k)] [Preorder V]
    (B : S.BehavioralBridge D)
    (utility :
      ((Option (Fin k → U) → ℚ) → ℚ) → Fin k → V)
    (profile : D.BehavioralProfile)
    (horizon : ℕ) :
    B.IsSourceMacroNashOnDeclaredContinuations
        utility profile horizon ↔
      B.IsTargetMacroNashOnDeclaredContinuations
        utility (B.mapProfile profile)
        horizon := by
  exact
    and_congr
      (B.initialIsNash_iff
        utility profile horizon)
      (B.macroNashOnDeclaredRoots_iff
        utility profile horizon)

end BehavioralBridge

end WeakSerialization

end FOSG

end ExtensiveGame
