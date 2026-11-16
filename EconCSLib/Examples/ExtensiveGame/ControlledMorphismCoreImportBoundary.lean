/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Morphism.Core

/-!
# Controlled morphism core import boundary

The structural leaf exposes morphism carriers, maps, strict isomorphisms, and
their algebra without importing lawful-subgame, recall, finite-EFG, or
structural history-length infrastructure.
-/

#check ExtensiveGame.ControlledObservedGame.Hom
#check ExtensiveGame.ControlledObservedGame.InformationRefinement
#check ExtensiveGame.ControlledObservedGame.Iso
#check ExtensiveGame.ControlledObservedGame.Iso.strategyEquiv
#check ExtensiveGame.ControlledObservedGame.Iso.trans_assoc

/--
error: Unknown constant `ExtensiveGame.ControlledObservedGame.Iso.mapSubgameSystem`
-/
#guard_msgs in
#check ExtensiveGame.ControlledObservedGame.Iso.mapSubgameSystem

/--
error: Unknown constant `ExtensiveGame.ControlledObservedGame.Iso.perfectRecall_iff`
-/
#guard_msgs in
#check ExtensiveGame.ControlledObservedGame.Iso.perfectRecall_iff

/--
error: Unknown constant `ExtensiveGame.ControlledObservedGame.FiniteEFGHypotheses`
-/
#guard_msgs in
#check ExtensiveGame.ControlledObservedGame.FiniteEFGHypotheses

/--
error: Unknown constant `Arena.HasLengthBoundFrom`
-/
#guard_msgs in
#check Arena.HasLengthBoundFrom
