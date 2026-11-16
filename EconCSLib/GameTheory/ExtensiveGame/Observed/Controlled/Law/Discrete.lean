/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Relations.Discrete.StochasticNaturality
import EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled

/-!
# Payoff-free discrete chance and bounded history laws

`DiscreteControlledObservedChanceGame` attaches normalized, countably
supported `FiniteLaw` chance kernels to a payoff-free observed controlled game.
It stores no payoff, root selection, finiteness, recall, or objective.

`BoundedHistoryLawFamily` is the raw data layer. The dependent history carrier
already witnesses root reachability, but arbitrary values are not called
execution semantics. `CertifiedBehavioralExecutionLaw` additionally exposes
normalization, legal reachable support, terminal absorption, and equality with
the specified chance-kernel/behavioral-profile executor; the concrete
behavioral executor constructs this certificate.

Full measure-valued path laws and their downstream interpretation hierarchy
live in `Controlled.Law`, so finite clients do not acquire the infinite
execution stack.
-/

namespace ExtensiveGame

universe uN uA uS uO uI uP

namespace ControlledObservedGame

variable {N : Type*} (G : ControlledObservedGame N)

/-! ## Discrete behavioral strategies -/

/-- A countably supported behavioral strategy indexed by payoff-free decision
information. -/
abbrev BehavioralStrategy (i : N) :=
  (information : G.RepresentedInfo i) →
    FiniteLaw (G.InfoAction i information.1)

/-- One payoff-free discrete behavioral strategy per player. -/
abbrev BehavioralProfile :=
  (i : N) → G.BehavioralStrategy i

/-- Unilateral update of a payoff-free discrete behavioral profile. -/
def BehavioralProfile.deviate [DecidableEq N]
    (profile : G.BehavioralProfile) (who : N)
    (deviation : G.BehavioralStrategy who) :
    G.BehavioralProfile :=
  Function.update profile who deviation

/-- Realize a discrete behavioral strategy as a law on legal actions at one
represented player decision. -/
def BehavioralStrategy.actionLawAt
    {i : N} (strategy : G.BehavioralStrategy i)
    (history : G.base.History)
    (hmover : G.base.mover history.1 = some i)
    (hnonterminal : ¬ G.base.isTerminal history.1) :
    FiniteLaw (G.base.Action history.1) :=
  let hdecision :=
    G.base.toArena.isDecision_of_not_isTerminal history.1 hnonterminal
  (strategy (G.representedInfoAt history i hmover hdecision)).map
    (G.actionEquiv history i hmover hdecision)

/-- Equal information states force a behavioral profile to choose the same
dependent abstract action law. -/
theorem BehavioralProfile.actionLaw_eq_of_infoState_eq
    (profile : G.BehavioralProfile) (i : N)
    (first second : G.base.History)
    (firstMover : G.base.mover first.1 = some i)
    (firstDecision : G.base.toArena.IsDecision first.1)
    (secondMover : G.base.mover second.1 = some i)
    (secondDecision : G.base.toArena.IsDecision second.1)
    (hsame :
      G.infoAt first i firstMover firstDecision =
        G.infoAt second i secondMover secondDecision) :
    (⟨G.representedInfoAt first i firstMover firstDecision,
        profile i
          (G.representedInfoAt first i firstMover firstDecision)⟩ :
      Σ information : G.RepresentedInfo i,
        FiniteLaw (G.InfoAction i information.1)) =
      ⟨G.representedInfoAt second i secondMover secondDecision,
        profile i
          (G.representedInfoAt second i secondMover secondDecision)⟩ :=
  congrArg
    (fun information : G.RepresentedInfo i =>
      (⟨information, profile i information⟩ :
        Σ state : G.RepresentedInfo i,
          FiniteLaw (G.InfoAction i state.1)))
    (Subtype.ext hsame)

end ControlledObservedGame

/-- A payoff-free observed game with discrete, countably supported chance
kernels. -/
structure DiscreteControlledObservedChanceGame
    (N : Type uN) where
  /-- Payoff-free observed strategic carrier. -/
  observed :
    ControlledObservedGame.{uN, uA, uS, uO, uI, uP} N
  /-- Normalized law on legal actions at every chance history. -/
  chanceKernel :
    (history : observed.base.History) →
      observed.base.isChanceState history.1 →
        FiniteLaw (observed.base.Action history.1)

namespace DiscreteControlledObservedChanceGame

variable {N : Type*}
  (G : DiscreteControlledObservedChanceGame N)

/-- Attach a discrete chance kernel to a payoff-free observation carrier. -/
abbrev withChanceKernel
    (observed : ControlledObservedGame N)
    (chanceKernel :
      (history : observed.base.History) →
        observed.base.isChanceState history.1 →
          FiniteLaw (observed.base.Action history.1)) :
    DiscreteControlledObservedChanceGame N where
  observed := observed
  chanceKernel := chanceKernel

/-- Behavioral plans indexed only by decision information. -/
abbrev BehavioralStrategy (i : N) :=
  G.observed.BehavioralStrategy i

/-- One payoff-free behavioral plan per player. -/
abbrev BehavioralProfile :=
  G.observed.BehavioralProfile

/-- Unilateral update of a payoff-free behavioral profile. -/
abbrev BehavioralProfile.deviate [DecidableEq N]
    (profile : G.BehavioralProfile) (who : N)
    (deviation : G.BehavioralStrategy who) :
    G.BehavioralProfile :=
  ControlledObservedGame.BehavioralProfile.deviate
    G.observed profile who deviation

/-- Concrete legal-action law at one represented player decision. -/
abbrev BehavioralStrategy.actionLawAt
    {i : N} (strategy : G.BehavioralStrategy i)
    (history : G.observed.base.History)
    (hmover :
      G.observed.base.mover history.1 = some i)
    (hnonterminal :
      ¬ G.observed.base.isTerminal history.1) :
    FiniteLaw (G.observed.base.Action history.1) :=
  ControlledObservedGame.BehavioralStrategy.actionLawAt
    G.observed strategy history hmover hnonterminal

/-- Stochastic history policy induced jointly by strategic and chance laws. -/
def BehavioralProfile.toHistoryPolicy
    (profile : G.BehavioralProfile) :
    G.observed.base.toArena.StochasticHistoryPolicy
      G.observed.base.init :=
  fun history hnonterminal =>
    match hmover : G.observed.base.mover history.1 with
    | some i =>
        DiscreteControlledObservedChanceGame.BehavioralStrategy.actionLawAt
          G (profile i) history hmover hnonterminal
    | none =>
        G.chanceKernel history ⟨hmover, hnonterminal⟩

/-- At a represented player decision, the induced stochastic history policy
is the mover's concrete behavioral action law. -/
theorem BehavioralProfile.toHistoryPolicy_of_mover
    (profile : G.BehavioralProfile)
    (history : G.observed.base.History)
    (hnonterminal :
      ¬ G.observed.base.isTerminal history.1)
    (i : N)
    (hmover : G.observed.base.mover history.1 = some i) :
    profile.toHistoryPolicy G history hnonterminal =
      DiscreteControlledObservedChanceGame.BehavioralStrategy.actionLawAt
        G (profile i) history hmover hnonterminal := by
  rw [BehavioralProfile.toHistoryPolicy]
  split
  · rename_i j hj
    have hji : j = i :=
      Option.some.inj (hj.symm.trans hmover)
    subst j
    rfl
  · rename_i hnone
    rw [hmover] at hnone
    contradiction

/-- At a chance history, the induced stochastic history policy is exactly
the stored discrete chance kernel. -/
theorem BehavioralProfile.toHistoryPolicy_of_chance
    (profile : G.BehavioralProfile)
    (history : G.observed.base.History)
    (hnonterminal :
      ¬ G.observed.base.isTerminal history.1)
    (hmover : G.observed.base.mover history.1 = none) :
    profile.toHistoryPolicy G history hnonterminal =
      G.chanceKernel history ⟨hmover, hnonterminal⟩ := by
  rw [BehavioralProfile.toHistoryPolicy]
  split
  · rename_i i hi
    rw [hmover] at hi
    contradiction
  · rfl

/-- Bounded complete-history law for the discrete behavioral model. -/
def behavioralHistoryLaw
    [(state : G.observed.base.State) →
      Decidable (G.observed.base.isTerminal state)]
    (profile : G.BehavioralProfile)
    (current : G.observed.base.History)
    (fuel : ℕ) :
    FiniteLaw G.observed.base.History :=
  G.observed.base.toArena.stochasticHistoryLawFrom
    (profile.toHistoryPolicy G) current fuel

end DiscreteControlledObservedChanceGame

namespace DiscreteControlledObservedChanceGame

universe uStrategy

variable {N : Type*}

/-! ## Payoff-free bounded history-law families -/

/-- Uncertified finite laws on bounded histories, indexed by strategies.

The semantic object is the full occurrence-sensitive history, not merely its
endpoint state. The dependent history type already enforces legal reachability
from the game root, but this raw family stores no terminal-absorption or
executor-consistency certificate. It must not by itself be advertised as
operational execution semantics. -/
structure BoundedHistoryLawFamily
    (G : DiscreteControlledObservedChanceGame N) where
  /-- One strategy carrier per player. -/
  Strategy : N → Type uStrategy
  /-- Complete-history law from every current history and fuel bound. -/
  historyLaw :
    (profile : ∀ i, Strategy i) →
      G.observed.base.History → ℕ →
        FiniteLaw G.observed.base.History

namespace BoundedHistoryLawFamily

variable {G : DiscreteControlledObservedChanceGame N}

/-- Profiles for one bounded complete-history semantic model. -/
abbrev Profile (S : G.BoundedHistoryLawFamily) :=
  ∀ i, S.Strategy i

/-- Equality of bounded occurrence-sensitive complete-history laws. -/
def CompleteHistoryLawEquivalentAt
    (S T : G.BoundedHistoryLawFamily)
    (source : S.Profile) (target : T.Profile)
    (current : G.observed.base.History)
    (fuel : ℕ) : Prop :=
  S.historyLaw source current fuel =
    T.historyLaw target current fuel

/-- One-way realization of every bounded complete-history law.

The playerwise strategy map gives a source-deviation map. Reverse target
deviation coverage remains a separate property. -/
structure CompleteHistoryLawRealization
    (S T : G.BoundedHistoryLawFamily) where
  /-- Map each player's source strategy into the target carrier. -/
  mapStrategy :
    (i : N) → S.Strategy i → T.Strategy i
  /-- Preserve every bounded complete-history FiniteLaw exactly. -/
  historyLaw_eq :
    ∀ (profile : S.Profile)
      (current : G.observed.base.History)
      (fuel : ℕ),
      S.historyLaw profile current fuel =
        T.historyLaw
          (fun i => mapStrategy i (profile i))
          current fuel

/-- Map a complete source profile player by player. -/
def CompleteHistoryLawRealization.mapProfile
    {S T : G.BoundedHistoryLawFamily}
    (R : S.CompleteHistoryLawRealization T)
    (profile : S.Profile) : T.Profile :=
  fun i => R.mapStrategy i (profile i)

/-- Playerwise complete-history realization commutes with unilateral update. -/
theorem CompleteHistoryLawRealization.mapProfile_update
    [DecidableEq N]
    {S T : G.BoundedHistoryLawFamily}
    (R : S.CompleteHistoryLawRealization T)
    (profile : S.Profile) (who : N)
    (deviation : S.Strategy who) :
    R.mapProfile (Function.update profile who deviation) =
      Function.update (R.mapProfile profile) who
        (R.mapStrategy who deviation) := by
  funext i
  by_cases hi : i = who
  · subst i
    simp [CompleteHistoryLawRealization.mapProfile]
  · simp [CompleteHistoryLawRealization.mapProfile, hi]

/-- Reverse target-deviation coverage for one source profile.

This condition is intentionally stronger than merely mapping every source
deviation. -/
def CompleteHistoryLawRealization.TargetDeviationsCoveredAt
    [DecidableEq N]
    {S T : G.BoundedHistoryLawFamily}
    (R : S.CompleteHistoryLawRealization T)
    (profile : S.Profile)
    (current : G.observed.base.History)
    (fuel : ℕ) : Prop :=
  ∀ (who : N) (targetDeviation : T.Strategy who),
    ∃ sourceDeviation : S.Strategy who,
      T.historyLaw
          (Function.update (R.mapProfile profile)
            who targetDeviation)
          current fuel =
        S.historyLaw
          (Function.update profile who sourceDeviation)
          current fuel

/-- A strategy-space isomorphism preserving bounded complete-history laws.

This is strictly stronger data than a one-way realization plus a particular
target-deviation coverage proof. -/
structure CompleteHistoryLawStrategyIso
    (S T : G.BoundedHistoryLawFamily)
    extends S.CompleteHistoryLawRealization T where
  /-- Playerwise strategy equivalence. -/
  strategyEquiv : (i : N) → S.Strategy i ≃ T.Strategy i
  /-- The realization map is the equivalence's forward map. -/
  mapStrategy_eq :
    ∀ i, toCompleteHistoryLawRealization.mapStrategy i =
      strategyEquiv i

end BoundedHistoryLawFamily

/-! ## Certified discrete behavioral execution laws -/

/-- Certified bounded execution law for the declared chance kernel and
behavioral profiles.

`FiniteLaw` values already carry normalization intrinsically; `normalized` exposes
that fact as a named certificate. The dependent `History` codomain makes every
support point a legal root-reachable history. `terminal_absorbing` records
stopping, while `execution_eq` ties the family to the concrete behavioral
history-policy executor, including its player and chance branches. -/
structure CertifiedBehavioralExecutionLaw
    (G : DiscreteControlledObservedChanceGame N)
    [(state : G.observed.base.State) →
      Decidable (G.observed.base.isTerminal state)] where
  /-- Certified bounded history FiniteLaw. -/
  historyLaw :
    G.BehavioralProfile →
      G.observed.base.History → ℕ →
        FiniteLaw G.observed.base.History
  /-- Each bounded law has total mass one. -/
  normalized :
    ∀ (profile : G.BehavioralProfile)
      (current : G.observed.base.History)
      (fuel : ℕ),
      FiniteLaw.totalWeight
        (historyLaw profile current fuel).atoms = 1
  /-- Every positive atom carries a legal history from the game root. -/
  positive_atoms_are_legal_reachable :
    ∀ (profile : G.BehavioralProfile)
      (current history : G.observed.base.History)
      (fuel : ℕ),
      (historyLaw profile current fuel).HasPositiveAtom history →
        Nonempty
          (G.observed.base.toArena.History
            G.observed.base.init history.1)
  /-- A terminal current history is absorbing at every fuel. -/
  terminal_absorbing :
    ∀ (profile : G.BehavioralProfile)
      (current : G.observed.base.History)
      (fuel : ℕ),
      G.observed.base.isTerminal current.1 →
        historyLaw profile current fuel = FiniteLaw.pure current
  /-- The certified law is exactly the specified behavioral/chance executor. -/
  execution_eq :
    ∀ (profile : G.BehavioralProfile)
      (current : G.observed.base.History)
      (fuel : ℕ),
      historyLaw profile current fuel =
        G.behavioralHistoryLaw profile current fuel

namespace CertifiedBehavioralExecutionLaw

/-- Every support endpoint is an occurrence-sensitive continuation of the
supplied current history.

The witness is a legal typed suffix in the underlying Arena, and the equality
retains the complete action-occurrence history rather than merely relating
endpoint states. This is derived from `execution_eq`; callers do not need to
unfold the concrete stochastic executor. -/
theorem exists_suffix_of_hasPositiveAtom
    {G : DiscreteControlledObservedChanceGame N}
    {terminalDecidable :
      (state : G.observed.base.State) →
        Decidable (G.observed.base.isTerminal state)}
    (S :
      @CertifiedBehavioralExecutionLaw N G terminalDecidable)
    (profile : G.BehavioralProfile)
    (current endpoint : G.observed.base.History)
    (fuel : ℕ)
    (hsupport :
      (S.historyLaw profile current fuel).HasPositiveAtom endpoint) :
    ∃ suffix :
        G.observed.base.toArena.History current.1 endpoint.1,
      endpoint.2 = current.2.append suffix := by
  rw [S.execution_eq profile current fuel] at hsupport
  exact
    G.observed.base.toArena.exists_suffix_of_hasPositiveAtom_stochasticHistoryLawFrom
      (profile.toHistoryPolicy G) current endpoint fuel hsupport

/-- A support endpoint from a terminal current history is the current history
itself. Equivalently, the only continuation suffix is empty; the accompanying
law-level statement is `terminal_absorbing`, which gives the Dirac law at
`current`. -/
theorem eq_current_of_terminal_of_hasPositiveAtom
    {G : DiscreteControlledObservedChanceGame N}
    {terminalDecidable :
      (state : G.observed.base.State) →
        Decidable (G.observed.base.isTerminal state)}
    (S :
      @CertifiedBehavioralExecutionLaw N G terminalDecidable)
    (profile : G.BehavioralProfile)
    (current endpoint : G.observed.base.History)
    (fuel : ℕ)
    (hterminal : G.observed.base.isTerminal current.1)
    (hsupport :
      (S.historyLaw profile current fuel).HasPositiveAtom endpoint) :
    endpoint = current := by
  rw [S.terminal_absorbing profile current fuel hterminal] at hsupport
  exact
    (FiniteLaw.hasPositiveAtom_pure_iff current endpoint).mp hsupport

/-- Forget execution certificates and retain the raw history-law family. -/
def toBoundedHistoryLawFamily
    {G : DiscreteControlledObservedChanceGame N}
    {terminalDecidable :
      (state : G.observed.base.State) →
        Decidable (G.observed.base.isTerminal state)}
    (S :
      @CertifiedBehavioralExecutionLaw N G terminalDecidable) :
    G.BoundedHistoryLawFamily where
  Strategy := G.BehavioralStrategy
  historyLaw := S.historyLaw

end CertifiedBehavioralExecutionLaw

/-- Functional bounded complete-history-law realization across two different
payoff-free discrete EFG representations. -/
structure CrossGameBoundedCompleteHistoryLawRealization
    {G H : DiscreteControlledObservedChanceGame N}
    (S : G.BoundedHistoryLawFamily)
    (T : H.BoundedHistoryLawFamily) where
  /-- Playerwise strategy map. -/
  mapStrategy :
    (i : N) → S.Strategy i → T.Strategy i
  /-- Occurrence-sensitive complete-history map. -/
  mapHistory :
    G.observed.base.History →
      H.observed.base.History
  /-- Exact bounded FiniteLaw pushforward at every profile, history, and fuel. -/
  historyLaw_map_eq :
    ∀ (profile : S.Profile)
      (current : G.observed.base.History)
      (fuel : ℕ),
      (S.historyLaw profile current fuel).map mapHistory =
        T.historyLaw
          (fun i => mapStrategy i (profile i))
          (mapHistory current) fuel

namespace CrossGameBoundedCompleteHistoryLawRealization

variable {G H : DiscreteControlledObservedChanceGame N}
  {S : G.BoundedHistoryLawFamily}
  {T : H.BoundedHistoryLawFamily}

/-- Map a bounded-law profile player by player. -/
def mapProfile
    (R : CrossGameBoundedCompleteHistoryLawRealization S T)
    (profile : S.Profile) : T.Profile :=
  fun i => R.mapStrategy i (profile i)

/-- Cross-game bounded-law strategy mapping commutes with unilateral update. -/
theorem mapProfile_update
    [DecidableEq N]
    (R : CrossGameBoundedCompleteHistoryLawRealization S T)
    (profile : S.Profile) (who : N)
    (deviation : S.Strategy who) :
    R.mapProfile (Function.update profile who deviation) =
      Function.update (R.mapProfile profile) who
        (R.mapStrategy who deviation) := by
  funext i
  by_cases hi : i = who
  · subst i
    simp [mapProfile]
  · simp [mapProfile, hi]

end CrossGameBoundedCompleteHistoryLawRealization

/-- Concrete certified bounded execution law for behavioral strategies and the
stored discrete chance kernel. -/
def behavioralCertifiedExecutionLaw
    (G : DiscreteControlledObservedChanceGame N)
    [(state : G.observed.base.State) →
      Decidable (G.observed.base.isTerminal state)] :
    G.CertifiedBehavioralExecutionLaw where
  historyLaw := fun profile current fuel =>
    G.behavioralHistoryLaw profile current fuel
  normalized := by
    intro profile current fuel
    exact FiniteLaw.totalWeight_atoms _
  positive_atoms_are_legal_reachable := by
    intro profile current history fuel hsupport
    exact ⟨history.2⟩
  terminal_absorbing := by
    intro profile current fuel hterminal
    exact
      G.observed.base.toArena.stochasticHistoryLawFrom_of_terminal
        (profile.toHistoryPolicy G) current hterminal fuel
  execution_eq := by
    intro profile current fuel
    rfl

end DiscreteControlledObservedChanceGame

end ExtensiveGame
