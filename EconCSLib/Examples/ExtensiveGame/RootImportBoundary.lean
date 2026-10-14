/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib

/-!
# Root-aggregate import boundary

The governed project root aggregate intentionally exposes finite/PMF execution,
`GameTree` syntax, and backward-induction values, but not infinite path laws,
historical endpoint-policy equilibrium, extraction, reference compilers, or
the analytic measurable-kernel stack. These negative compilation guards
prevent convenience imports from silently widening the root surface. This
regression does not promise external source compatibility for the
pre-stability EFG paths it reaches.
-/

#check Arena.stochasticHistoryLawFrom
#check GameTree.value

/--
error: Unknown identifier `Examples.HistoryDiamond.arena`
-/
#guard_msgs in
#check Examples.HistoryDiamond.arena

/--
error: Unknown identifier `Examples.TerminalStoppedExecution.arena`
-/
#guard_msgs in
#check Examples.TerminalStoppedExecution.arena

/--
error: Unknown constant `Arena.pathLaw`
-/
#guard_msgs in
#check Arena.pathLaw

/--
error: Unknown constant `GameTree.Kuhn_exists_globalEndpointSPE`
-/
#guard_msgs in
#check GameTree.Kuhn_exists_globalEndpointSPE

/--
error: Unknown constant `GameTree.Kuhn_exists_NE`
-/
#guard_msgs in
#check GameTree.Kuhn_exists_NE

/--
error: Unknown constant `ExtensiveGame.FiniteExtractable`
-/
#guard_msgs in
#check ExtensiveGame.FiniteExtractable

/--
error: Unknown constant `GameTree.zermelo_determinacy`
-/
#guard_msgs in
#check GameTree.zermelo_determinacy

/--
error: Unknown identifier `MeasurableKernelArena`
-/
#guard_msgs in
#check MeasurableKernelArena

/--
error: Unknown constant `GameTree.Kuhn_exists_occurrencePureSPE`
-/
#guard_msgs in
#check GameTree.Kuhn_exists_occurrencePureSPE

/--
error: Unknown constant `Arena.play`
-/
#guard_msgs in
#check Arena.play

/--
error: Unknown constant `ExtensiveGame.BehaviorStrategy`
-/
#guard_msgs in
#check ExtensiveGame.BehaviorStrategy

/--
error: Unknown identifier `FiniteImperfectGame`
-/
#guard_msgs in
#check FiniteImperfectGame

/--
error: Unknown identifier `StochasticGameTree`
-/
#guard_msgs in
#check StochasticGameTree
