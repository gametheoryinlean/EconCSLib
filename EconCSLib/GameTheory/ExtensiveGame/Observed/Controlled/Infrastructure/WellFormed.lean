/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled

/-!
# General payoff-free controlled well-formedness

Represented-information and optional mover-normalization certificates that require neither
finite action/information carriers nor a structural history-length bound.
`Finite` and `Recall` depend on this leaf without acquiring each other's
assumptions or execution infrastructure.

Pure strategies themselves need no availability assumption: their coordinates
are `RepresentedInfo` values and therefore carry a concrete decision witness.
`PureStrategyAvailabilityCertificate` is retained as the stronger assertion
that every raw information value is represented.
-/

namespace ExtensiveGame.ControlledObservedGame

variable {N : Type*} {G : ControlledObservedGame N}

/-- Every declared information state is represented by a player decision. -/
def AllDecisionInfoRepresented
    (G : ControlledObservedGame N) : Prop :=
  ∀ (i : N) (information : G.InfoState i),
    Nonempty (G.DecisionInfoWitness i information)

/-- Every player-labelled history has a nonempty legal-action type. -/
def DecisionMoverCoherent
    (G : ControlledObservedGame N) : Prop :=
  ∀ (history : G.base.History) (i : N),
    G.base.mover history.1 = some i →
      Nonempty (G.base.Action history.1)

/-- Optional certificate asserting that every declared raw information value
is represented by a decision.

Pure strategies are already inhabited without this certificate because their
domain is `RepresentedInfo`. The certificate remains useful to APIs that need
to quantify over the full raw `InfoState` carrier. -/
structure PureStrategyAvailabilityCertificate
    (G : ControlledObservedGame N) : Prop where
  /-- Every declared decision-information state has a concrete witness. -/
  allDecisionInfoRepresented : G.AllDecisionInfoRepresented

/-- Optional higher-level certificate for models that need both inhabited pure
profiles and chance-free execution on reachable histories.

The bundle is deliberately narrow: consumers needing only one component
should state that component instead of requiring this certificate. -/
structure ReachablePureStrategyModelCertificate
    (G : ControlledObservedGame N) : Prop
    extends G.PureStrategyAvailabilityCertificate where
  /-- Every reachable nonterminal history has a strategic mover. -/
  noChanceOnHistories : G.base.NoChanceOnHistories

/-- The legacy availability bundle is exactly full raw-information
representation. -/
theorem pureStrategyAvailabilityCertificate_iff
    (G : ControlledObservedGame N) :
    G.PureStrategyAvailabilityCertificate ↔
      G.AllDecisionInfoRepresented := by
  constructor
  · intro certificate
    exact certificate.allDecisionInfoRepresented
  · intro hrepresented
    exact ⟨hrepresented⟩

/-- The reachable pure-model bundle projects to exactly the two independent
predicates it packages. -/
theorem reachablePureStrategyModelCertificate_iff
    (G : ControlledObservedGame N) :
    G.ReachablePureStrategyModelCertificate ↔
      G.AllDecisionInfoRepresented ∧
        G.base.NoChanceOnHistories := by
  constructor
  · intro certificate
    exact
      ⟨certificate.allDecisionInfoRepresented,
        certificate.noChanceOnHistories⟩
  · rintro ⟨hrepresented, hNoChance⟩
    exact ⟨⟨hrepresented⟩, hNoChance⟩

/-- Mover coherence is exactly terminal-mover normalization on complete
histories reachable from `G.base.init`.

This theorem does not normalize every ambient Arena state: `G.base.History`
contains precisely the occurrence-sensitive histories reachable from the
controlled game's initial state. -/
theorem decisionMoverCoherent_iff_terminal_mover_eq_none_on_histories
    (G : ControlledObservedGame N) :
    G.DecisionMoverCoherent ↔
      ∀ history : G.base.History,
        G.base.isTerminal history.1 →
          G.base.mover history.1 = none := by
  constructor
  · intro hcoherent history hterminal
    cases hmover : G.base.mover history.1 with
    | none => rfl
    | some i =>
        have haction := hcoherent history i hmover
        exact ((not_nonempty_iff.mpr hterminal) haction).elim
  · intro hnormalized history i hmover
    classical
    by_contra hnonempty
    have hterminal : G.base.isTerminal history.1 :=
      not_nonempty_iff.mp hnonempty
    have hnone := hnormalized history hterminal
    rw [hmover] at hnone
    simp at hnone

namespace AllDecisionInfoRepresented

/-- Represented information has a legal abstract action. -/
theorem nonempty_infoAction
    (hrepresented : G.AllDecisionInfoRepresented)
    (i : N) (information : G.InfoState i) :
    Nonempty (G.InfoAction i information) := by
  rcases hrepresented i information with ⟨witness⟩
  have habstract :=
    witness.decision.map
      (G.actionEquiv witness.history i witness.mover
        witness.decision).symm
  simpa [witness.infoAt_eq] using habstract

end AllDecisionInfoRepresented

/-- Each pure-strategy carrier is inhabited without a global mover-coherence
or raw-information representation assumption. -/
theorem nonempty_pureStrategy
    (i : N) :
    Nonempty (G.PureStrategy i) := by
  classical
  exact
    ⟨fun information =>
      Classical.choice
        (G.toControlledDecisionGame.representedInfo_nonempty_infoAction
          i information)⟩

/-- The pure-profile carrier is inhabited without extra well-formedness
assumptions. -/
theorem nonempty_pureProfile
    : Nonempty G.PureProfile := by
  classical
  exact
    ⟨fun i =>
      Classical.choice
        (nonempty_pureStrategy i)⟩

end ExtensiveGame.ControlledObservedGame
