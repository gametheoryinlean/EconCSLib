/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Execution.Length
import EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Infrastructure.WellFormed

/-!
# Payoff-free finite EFG certificates

Structural finite-EFG hypotheses for `ControlledObservedGame`. General
represented-information and mover-normalization certificates live in
`Controlled.Infrastructure.WellFormed`; this leaf adds only the assumptions and
consequences that genuinely require a finite reachable unfolding or a
structural history-length bound. Pure-profile inhabitation is already general
and is therefore not restated under `FiniteEFGHypotheses`.
-/

namespace ExtensiveGame.ControlledObservedGame

variable {N : Type*} {G : ControlledObservedGame N}

/-! ## Finite structure -/

/-- Structural certificate for a finite payoff-free observed EFG.

The bound applies to the reachable complete-history unfolding, not to the
ambient compact state type. Chance laws, recall, player finiteness, and
objectives are intentionally separate. -/
structure FiniteEFGHypotheses
    (G : ControlledObservedGame N) where
  /-- Uniform bound on legal action occurrences. -/
  lengthBound : ℕ
  /-- Every legal continuation of that length has terminated. -/
  hasLengthBound :
    G.base.toArena.HasLengthBoundFrom
      G.base.init lengthBound
  /-- Explicit enumeration of each reachable concrete action fiber. -/
  finiteAction :
    ∀ history : G.base.History,
      Fintype (G.base.Action history.1)
  /-- Executable presentation of every represented decision carrier.

  The explicit equivalence fixes a stable coordinate order.  Equality on
  each abstract action fiber is stored as data because finite laws may have
  an infinite ambient outcome type even though their support is finite.  Raw
  `InfoState` values that never occur at a decision remain irrelevant. -/
  finiteDecisionPresentation :
    ∀ i : N,
      (Σ size : ℕ, G.RepresentedInfo i ≃ Fin size) ×
        (∀ information : G.RepresentedInfo i,
          DecidableEq (G.InfoAction i information.1))

namespace FiniteEFGHypotheses

/-- A finite-EFG certificate makes the history unfolding well-founded. -/
theorem isWellFoundedFrom
    (h : G.FiniteEFGHypotheses) :
    G.base.toArena.IsWellFoundedFrom G.base.init :=
  Arena.HasLengthBoundFrom.isWellFoundedFrom
    h.hasLengthBound

/-- Every complete play under a finite-EFG certificate terminates. -/
theorem eventuallyTerminates
    (h : G.FiniteEFGHypotheses)
    (play : G.base.CompletePlay) :
    play.EventuallyTerminates :=
  Arena.HasLengthBoundAt.eventuallyTerminates
    h.hasLengthBound play

end FiniteEFGHypotheses

end ExtensiveGame.ControlledObservedGame
