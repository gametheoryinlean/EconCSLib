/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Strategy and chance semantic classifications

Lightweight tags shared by bounded complete-history and infinite complete-path
law interfaces. The analytic tags reserve an honest classification boundary;
they do not construct measurable strategy carriers.
-/

namespace ExtensiveGame.ObservedChanceGame

/-- Strategy-space classification used by semantic comparison records.

`discreteGeneral` means a PMF-supported general strategy.
`analyticGeneral` is reserved for a genuinely measurable strategy-space
construction. -/
inductive StrategicMode where
  | pure
  | behavioral
  | mixed
  | discreteGeneral
  | analyticGeneral
  deriving DecidableEq, Repr

/-- Probability semantics used by a history/path-law evaluator. -/
inductive ChanceSemantics where
  | noChance
  | discretePMF
  | analyticKernel
  deriving DecidableEq, Repr

end ExtensiveGame.ObservedChanceGame
