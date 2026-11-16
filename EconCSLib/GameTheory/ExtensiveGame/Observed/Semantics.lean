/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Semantics
import EconCSLib.GameTheory.ExtensiveGame.Observed.Game

/-!
# EconCSLib.GameTheory.ExtensiveGame.Observed.Semantics

State-payoff observed-game compatibility for payoff-free continuation
semantics.

The canonical carrier and theorem layer live in
`Observed.Controlled.Semantics` and depend only on `ControlledObservedGame`.
This module preserves the established `ObservedGame.ContinuationSemantics`
spelling by projecting through `toControlledObservedGame`. It does not inspect
or store state payoffs. Evaluator-relative equilibrium remains distinct from
operational standard SPE, which remains owned by concrete execution layers.
Cross-game wrappers permit different source and target state-payoff types.
-/

namespace ExtensiveGame.ObservedGame

universe uN uU uW uStrategy uHorizon uOutcome uV

variable {N : Type uN} {U : Type uU}

/-- Compatibility name for the payoff-free continuation semantics attached to
`G.toControlledObservedGame`.

The state-payoff field of `G` is not stored or inspected. -/
abbrev ContinuationSemantics (G : ObservedGame N U) :=
  G.toControlledObservedGame.ContinuationSemantics

namespace ContinuationSemantics

variable {G : ObservedGame N U}

/-- Compatibility name for complete profiles. -/
abbrev Profile (S : G.ContinuationSemantics) :=
  ControlledObservedGame.ContinuationSemantics.Profile S

/-- Compatibility adapter on an explicit root predicate. -/
def toIndexedGameFormOn
    (S : G.ContinuationSemantics)
    (roots : G.base.toArena.HistoryFrom G.base.init → Prop) :
    IndexedContinuationGameForm N :=
  ControlledObservedGame.ContinuationSemantics.toIndexedGameFormOn S roots

/-- Compatibility adapter on a state-payoff observed-game root
presentation. -/
def toIndexedGameFormOnPresentation
    (S : G.ContinuationSemantics)
    (roots : G.RootPresentation) :
    IndexedContinuationGameForm N :=
  S.toIndexedGameFormOn roots.IsRoot

@[simp]
theorem toIndexedGameFormOnPresentation_outcome
    (S : G.ContinuationSemantics)
    (roots : G.RootPresentation)
    (horizon : S.Horizon)
    (root : G.base.toArena.HistoryFrom G.base.init)
    (profile : S.Profile) :
    (S.toIndexedGameFormOnPresentation roots).outcome
        horizon root profile =
      S.evaluate horizon root profile :=
  rfl

/-- Compatibility definition of Nash equilibrium on a root presentation. -/
def IsNashOnPresentationAt
    {V : Type uV} [DecidableEq N] [Preorder V]
    (S : G.ContinuationSemantics)
    (roots : G.RootPresentation)
    (utility :
      G.base.toArena.HistoryFrom G.base.init →
        S.Outcome → N → V)
    (horizon : S.Horizon) (profile : S.Profile) : Prop :=
  (S.toIndexedGameFormOnPresentation roots).IsNashOnRootsAt
    utility horizon profile

/-- Compatibility definition of evaluator-relative continuation equilibrium
on a selected lawful payoff-free subgame system. -/
def IsEvaluatorContinuationEquilibriumOnAt
    {V : Type uV} [DecidableEq N] [Preorder V]
    (S : G.ContinuationSemantics)
    (system : G.SubgameSystem)
    (utility :
      G.base.toArena.HistoryFrom G.base.init →
        S.Outcome → N → V)
    (horizon : S.Horizon) (profile : S.Profile) : Prop :=
  ControlledObservedGame.ContinuationSemantics.IsEvaluatorContinuationEquilibriumOnAt
    S system utility horizon profile

/-- Compatibility definition of evaluator-relative continuation equilibrium
on every lawful payoff-free subgame root. -/
def IsEvaluatorContinuationEquilibriumAt
    {V : Type uV} [DecidableEq N] [Preorder V]
    (S : G.ContinuationSemantics)
    (system : G.CompleteSubgameSystem)
    (utility :
      G.base.toArena.HistoryFrom G.base.init →
        S.Outcome → N → V)
    (horizon : S.Horizon) (profile : S.Profile) : Prop :=
  ControlledObservedGame.ContinuationSemantics.IsEvaluatorContinuationEquilibriumAt
    S system utility horizon profile

/-- The compatibility presentation adapter introduces no new equilibrium
predicate. -/
theorem isNashOnPresentationAt_iff
    {V : Type uV} [DecidableEq N] [Preorder V]
    (S : G.ContinuationSemantics)
    (roots : G.RootPresentation)
    (utility :
      G.base.toArena.HistoryFrom G.base.init →
        S.Outcome → N → V)
    (horizon : S.Horizon) (profile : S.Profile) :
    S.IsNashOnPresentationAt roots utility horizon profile ↔
      (S.toIndexedGameFormOnPresentation roots).IsNashOnRootsAt
        utility horizon profile :=
  Iff.rfl

/-- Compatibility form of the payoff-free abstract game-form transfer theorem.

Source and target state-payoff types may differ because neither payoff field
participates in continuation evaluation or utility compatibility. -/
theorem isEvaluatorContinuationEquilibriumAt_iff_of_surjective
    {W : Type uW} {H : ObservedGame N W}
    {V : Type uV} [DecidableEq N] [Preorder V]
    (S : G.ContinuationSemantics)
    (T : H.ContinuationSemantics)
    (sourceSystem : G.CompleteSubgameSystem)
    (targetSystem : H.CompleteSubgameSystem)
    (f :
      (S.toIndexedGameFormOn
        sourceSystem.toSubgameSystem.IsRoot).Hom
        (T.toIndexedGameFormOn
          targetSystem.toSubgameSystem.IsRoot))
    (sourceUtility :
      S.Horizon →
        G.base.toArena.HistoryFrom G.base.init →
          S.Outcome → N → V)
    (targetUtility :
      T.Horizon →
        H.base.toArena.HistoryFrom H.base.init →
          T.Outcome → N → V)
    (hutility :
      f.UtilityCompatible sourceUtility targetUtility)
    (hstrategy : f.StrategySurjective)
    (hroot : f.DeclaredRootSurjective)
    (horizon : S.Horizon)
    (profile : S.Profile) :
    S.IsEvaluatorContinuationEquilibriumAt sourceSystem
        (sourceUtility horizon) horizon profile ↔
      T.IsEvaluatorContinuationEquilibriumAt targetSystem
        (targetUtility (f.horizonMap horizon))
        (f.horizonMap horizon) (f.mapProfile profile) := by
  exact
    ExtensiveGame.ControlledObservedGame.ContinuationSemantics.isEvaluatorContinuationEquilibriumAt_iff_of_surjective
        S T sourceSystem targetSystem f
        sourceUtility targetUtility hutility hstrategy hroot horizon profile

end ContinuationSemantics

end ExtensiveGame.ObservedGame
