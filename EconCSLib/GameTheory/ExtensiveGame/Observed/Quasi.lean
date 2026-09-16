/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Infrastructure.Quasi
import EconCSLib.GameTheory.ExtensiveGame.Observed.WellFormed
import EconCSLib.GameTheory.ExtensiveGame.Winning.BasicCompat

/-!
# Payoff-aware quasistrategy compatibility

The quasistrategy theory is implemented once, on
`ControlledObservedGame`, in `Controlled.Infrastructure.Quasi`, with winning
predicates in `Winning.Basic`. This
module preserves the historical `ObservedGame` names as payoff-forgetting
adapters.  No independent quasistrategy carrier or compatibility predicate is
defined here.
-/

namespace ExtensiveGame.ObservedGame

variable {N U : Type*} {G : ObservedGame N U}

/-- Compatibility spelling for a nonempty permitted-action set. -/
abbrev NonemptyActionSet (Action : Type*) :=
  ControlledObservedGame.NonemptyActionSet Action

/-- Compatibility spelling for a payoff-free quasistrategy. -/
abbrev QuasiStrategy (G : ObservedGame N U) (i : N) :=
  G.toControlledObservedGame.QuasiStrategy i

namespace QuasiStrategy

/-- Pointwise inclusion of permitted actions. -/
abbrev Refines {i : N}
    (narrow broad : G.QuasiStrategy i) : Prop :=
  ControlledObservedGame.QuasiStrategy.Refines narrow broad

/-- A pure contingent plan permits exactly its selected action. -/
def ofPure {i : N} (strategy : G.PureStrategy i) :
    G.QuasiStrategy i :=
  ControlledObservedGame.QuasiStrategy.ofPure strategy

/-- Every singleton quasistrategy refines itself. -/
theorem ofPure_refines_self {i : N}
    (strategy : G.PureStrategy i) :
    (ofPure strategy).Refines (ofPure strategy) :=
  fun _information => Set.Subset.rfl

end QuasiStrategy

/-- Payoff-aware spelling of payoff-free quasistrategy compatibility from an
arbitrary current history. -/
abbrev IsCompatibleWithQuasiStrategyFrom
    {current : G.base.toArena.HistoryFrom G.base.init}
    (i : N) (strategy : G.QuasiStrategy i)
    (play : G.base.toArena.CompletePlayFromHistory current) : Prop :=
  G.toControlledObservedGame.IsCompatibleWithQuasiStrategyFrom
    i strategy play

/-- Root-started compatibility with one quasistrategy. -/
abbrev IsCompatibleWithQuasiStrategy
    (G : ObservedGame N U) (i : N)
    (strategy : G.QuasiStrategy i)
    (play : G.base.toArena.CompletePlayFrom G.base.init) : Prop :=
  G.IsCompatibleWithQuasiStrategyFrom i strategy play

/-- Pure compatibility is compatibility with singleton permissions. -/
theorem isCompatibleWithQuasiStrategy_ofPure_iff
    {current : G.base.toArena.HistoryFrom G.base.init}
    (i : N) (strategy : G.PureStrategy i)
    (play : G.base.toArena.CompletePlayFromHistory current) :
    G.IsCompatibleWithQuasiStrategyFrom
        i (QuasiStrategy.ofPure strategy) play ↔
      G.IsCompatibleWithPlayerStrategyFrom i strategy play :=
  ControlledObservedGame.isCompatibleWithQuasiStrategy_ofPure_iff
    (G := G.toControlledObservedGame) i strategy play

/-- Compatibility is contravariant in permission-set refinement. -/
theorem IsCompatibleWithQuasiStrategyFrom.mono
    {current : G.base.toArena.HistoryFrom G.base.init}
    {i : N} {narrow broad : G.QuasiStrategy i}
    (hrefines : narrow.Refines broad)
    {play : G.base.toArena.CompletePlayFromHistory current}
    (hcompatible :
      G.IsCompatibleWithQuasiStrategyFrom i narrow play) :
    G.IsCompatibleWithQuasiStrategyFrom i broad play := by
  intro n hnonterminal hmover
  rcases hcompatible n hnonterminal hmover with
    ⟨abstractAction, hallowed, hnext⟩
  exact
    ⟨abstractAction, hrefines _ hallowed, hnext⟩

/-- Compatibility spelling for robust pathwise winning by a quasistrategy. -/
abbrev HasWinningQuasiStrategy
    (G : ObservedGame N U)
    (W : G.base.toArena.WinningCondition G.base.init N)
    (i : N) (strategy : G.QuasiStrategy i) : Prop :=
  G.toControlledObservedGame.HasWinningQuasiStrategy W i strategy

/-- A robust winning quasistrategy remains winning after narrowing its
permission sets. -/
theorem HasWinningQuasiStrategy.of_refines
    {W : G.base.toArena.WinningCondition G.base.init N}
    {i : N} {narrow broad : G.QuasiStrategy i}
    (hbroad : G.HasWinningQuasiStrategy W i broad)
    (hrefines : narrow.Refines broad) :
    G.HasWinningQuasiStrategy W i narrow := by
  intro play hcompatible
  apply hbroad play
  intro n hnonterminal hmover
  rcases hcompatible n hnonterminal hmover with
    ⟨abstractAction, hallowed, hnext⟩
  exact
    ⟨abstractAction, hrefines _ hallowed, hnext⟩

end ExtensiveGame.ObservedGame
