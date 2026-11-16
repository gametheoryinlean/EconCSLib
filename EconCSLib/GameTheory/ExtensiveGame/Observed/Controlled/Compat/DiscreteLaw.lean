/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Observed.Chance
import EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Law.Discrete

/-!
# Payoff-aware adapter for discrete controlled chance

API role: **downstream payoff-aware adapter**. Its location under
`Controlled.Compat` marks it as non-canonical, and canonical controlled
modules must never import it.

This module forgets only the payoff interpretation of an
`ObservedChanceGame`.  Discrete chance and bounded execution remain owned by
the payoff-free `Controlled.Law.Discrete` module.
-/

namespace ExtensiveGame.ObservedChanceGame

variable {N U : Type*}

/-- Forget payoffs from a discrete observed chance game while retaining its
complete history and chance laws definitionally. -/
def toDiscreteControlledObservedChanceGame
    (G : ObservedChanceGame N U) :
    DiscreteControlledObservedChanceGame N where
  observed := G.observed.toControlledObservedGame
  chanceKernel := G.chanceKernel

/-- Attach an endpoint-state payoff interpretation to a payoff-free discrete
observed chance game.

The chance kernel and the full observation/information carrier are reused
definitionally; only the supplied payoff is added. -/
def ofDiscreteControlledObservedChanceGame
    (G : DiscreteControlledObservedChanceGame N)
    (payoff : G.observed.base.State → N → U) :
    ObservedChanceGame N U where
  observed :=
    ObservedGame.ofControlledObservedGame G.observed payoff
  chanceKernel := G.chanceKernel

@[simp]
theorem ofDiscreteControlledObservedChanceGame_toControlled
    (G : DiscreteControlledObservedChanceGame N)
    (payoff : G.observed.base.State → N → U) :
    (ofDiscreteControlledObservedChanceGame G payoff).toDiscreteControlledObservedChanceGame =
      G :=
  rfl

@[simp]
theorem ofDiscreteControlledObservedChanceGame_payoff
    (G : DiscreteControlledObservedChanceGame N)
    (payoff : G.observed.base.State → N → U)
    (state : G.observed.base.State) (i : N) :
    (ofDiscreteControlledObservedChanceGame G payoff).observed.base.payoff
        state i =
      payoff state i :=
  rfl

/-- Reattaching an observed chance game's existing endpoint payoff after its
payoff-free projection recovers the original game. -/
@[simp]
theorem ofDiscreteControlledObservedChanceGame_toControlled_payoff
    (G : ObservedChanceGame N U) :
    ofDiscreteControlledObservedChanceGame
        G.toDiscreteControlledObservedChanceGame
        G.observed.base.payoff =
      G := by
  cases G with
  | mk observed chanceKernel =>
      cases observed
      rfl

end ExtensiveGame.ObservedChanceGame
