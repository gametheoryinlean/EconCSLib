/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Simulation.Equilibrium.Outcome
import EconCSLib.Math.Probability.Effective.Semantics

/-!
# Effective expectation queries for path utility

This module specializes effective-law expectation correctness to the EFG
`PathUtility.expectedUtility` semantics.  The executable theorem applies when
one player's utility is exactly denoted by a finite rational simple observable
over a selected path-event language.

General measurable integrable utilities remain available through
`PathUtility.expectedUtility`; a certified enclosure query additionally needs
the finite observable representation required below (or a separate
certified approximation theorem).
-/

namespace ExtensiveGame.ObservedGame

universe uN uU uPathCode

variable {N : Type uN} {U : Type uU}
variable {G : ObservedGame N U}

namespace MeasurableHistoryModel.PathUtility

variable {model : MeasurableHistoryModel G}

/-- If an effective law represents the profile's analytic state-path measure
and a finite rational simple observable denotes one player's path utility,
then its executable expectation oracle represents that player's existing
`expectedUtility` value. -/
theorem effective_expectedUtility_represents
    (evaluation : PathUtility model)
    {presentation : G.MeasurableKernelPresentation model}
    (profile : presentation.KernelBehavioralProfile)
    (initialHistory : CompleteHistory G)
    (hintegrable : evaluation.IntegrableAt profile initialHistory)
    (i : N)
    {PathCode : Type uPathCode}
    (law : EffectiveProbability.EffectiveLaw PathCode)
    (pathSemantics :
      EffectiveProbability.EventSemantics PathCode
        (ℕ → model.toArena.State))
    (observable : EffectiveProbability.SimpleObservable PathCode)
    (hlaw :
      law.Represents pathSemantics
        (profile.statePathMeasure initialHistory))
    (hobservable :
      observable.Denotes pathSemantics (evaluation.utility i)) :
    (law.expect observable).Represents
      (evaluation.expectedUtility
        profile initialHistory hintegrable i) := by
  refine (hlaw.expect_integral hobservable).congr ?_
  unfold expectedUtility
  rfl

end MeasurableHistoryModel.PathUtility

end ExtensiveGame.ObservedGame
