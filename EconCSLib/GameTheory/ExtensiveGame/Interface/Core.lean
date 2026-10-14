/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Execution.CompletePlay
import EconCSLib.GameTheory.ExtensiveGame.Execution.History
import EconCSLib.GameTheory.ExtensiveGame.Execution.Length
import EconCSLib.GameTheory.ExtensiveGame.Execution.StoppedExecution
import EconCSLib.GameTheory.ExtensiveGame.Execution.StochasticExecution
import EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Infrastructure.Core
import EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Infrastructure.WellFormed
import EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Infrastructure.Subgame
import EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Infrastructure.Finite
import EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Infrastructure.Quasi
import EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Infrastructure.Recall

/-!
# EconCSLib.GameTheory.ExtensiveGame.Interface.Core

Canonical pre-stability Foundation Facade for typed histories, measure-free
complete plays, structural termination certificates, bounded deterministic
and finite-law execution, and the payoff-free controlled history-indexed information
structure. It also includes represented information, mover coherence,
finite-EFG certificates, recall predicates, quasistrategies, and external
lawful subgame systems without introducing another game record.

`ControlledObservedGame.completeInformation` uses exactly each player's
mover-labeled decision-history subtype, so chance and other-player histories
do not create spurious strategy coordinates. Terminal histories are excluded
under terminal-mover normalization; the general carrier instead exposes
`DecisionMoverCoherent` as the explicit obligation. Public projection and
designated-root selection remain explicit orthogonal arguments.

This governed facade documents the declaration families above, not every
declaration that might become visible through an implementation import. There
is currently no external source-compatibility guarantee. It intentionally
excludes payoff-aware `ObservedGame`, objectives and winning conditions,
measure-valued path laws, representation relations, equilibrium, simulation,
serialization, and compilers. The genuinely narrow structural entry is
`Interface.StructuralCore`; payoff-aware clients must import adapters
explicitly.
-/
