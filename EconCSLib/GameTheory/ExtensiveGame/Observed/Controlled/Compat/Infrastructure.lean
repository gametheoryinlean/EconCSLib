/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Infrastructure.Recall
import EconCSLib.GameTheory.ExtensiveGame.Observed.Quasi
import EconCSLib.GameTheory.ExtensiveGame.Observed.SignalRecall

/-!
# Payoff-aware adapters for controlled observed-game infrastructure

API role: **downstream payoff-aware adapter**. Its location under
`Controlled.Compat` marks it as non-canonical, and canonical controlled
modules must never import it.

This module is the one-way compatibility boundary from `ObservedGame` to the
payoff-free `ControlledObservedGame`.  Core recall and quasistrategy ownership
remains in the defining `Controlled.Infrastructure.Recall` and
`Controlled.Infrastructure.Quasi` leaves; these theorems only identify the
legacy payoff-aware surface with its projection.
-/

namespace ExtensiveGame.ObservedGame

variable {N U : Type*} {G : ObservedGame N U}

/-- Pure strategies are definitionally unchanged by forgetting payoffs. -/
theorem pureStrategy_toControlled
    (i : N) :
    G.PureStrategy i =
      G.toControlledObservedGame.PureStrategy i :=
  rfl

/-- Pure profiles are definitionally unchanged by forgetting payoffs. -/
theorem pureProfile_toControlled :
    G.PureProfile =
      G.toControlledObservedGame.PureProfile :=
  rfl

/-- Forgetting payoffs leaves the extracted own-decision trace unchanged. -/
theorem ownDecisionHistory_toControlled
    [DecidableEq N] (i : N)
    (history : G.base.toArena.HistoryFrom G.base.init) :
    G.toControlledObservedGame.ownDecisionHistory i history =
      G.ownDecisionHistory i history :=
  rfl

/-- Forgetting payoffs leaves the private-signal trace unchanged. -/
theorem signalHistory_toControlled
    (i : N)
    (history : G.base.toArena.HistoryFrom G.base.init) :
    G.toControlledObservedGame.signalHistory i history =
      G.signalHistory i history :=
  rfl

/-- Forgetting payoffs leaves the public-signal trace unchanged. -/
theorem publicSignalHistory_toControlled
    (history : G.base.toArena.HistoryFrom G.base.init) :
    G.toControlledObservedGame.publicSignalHistory history =
      G.publicSignalHistory history :=
  rfl

/-- Classic perfect recall is exactly the payoff-free projection predicate. -/
theorem hasPerfectRecall_iff_toControlled
    [DecidableEq N] (i : N) :
    G.HasPerfectRecall i ↔
      G.toControlledObservedGame.HasPerfectRecall i :=
  Iff.rfl

/-- Event-clock private-signal recall is exactly the payoff-free projection
predicate. -/
theorem hasEventClockSignalPerfectRecall_iff_toControlled
    (i : N) :
    G.HasEventClockSignalPerfectRecall i ↔
      G.toControlledObservedGame.HasEventClockSignalPerfectRecall i :=
  Iff.rfl

/-- Event-clock public recall is exactly the payoff-free projection
predicate. -/
theorem hasEventClockPublicPerfectRecall_iff_toControlled :
    G.HasEventClockPublicPerfectRecall ↔
      G.toControlledObservedGame.HasEventClockPublicPerfectRecall :=
  Iff.rfl

/-- No-absent-mindedness is exactly the payoff-free projection predicate. -/
theorem hasNoAbsentMindedness_iff_toControlled
    (i : N) :
    G.HasNoAbsentMindedness i ↔
      G.toControlledObservedGame.HasNoAbsentMindedness i :=
  Iff.rfl

end ExtensiveGame.ObservedGame
