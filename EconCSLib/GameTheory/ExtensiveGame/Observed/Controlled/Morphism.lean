/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Morphism.Core
import EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Morphism.Subgame
import EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Morphism.Recall
import EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Morphism.Objective

/-!
# Controlled observed-game morphism facade

API role: **canonical aggregate facade**. It owns no declarations.

This broad entry point re-exports the structural, lawful-subgame, recall, and
operational objective leaves. New implementation code should import the narrowest
`Observed.Controlled.Morphism.*` leaf that provides the declarations it uses.
-/
