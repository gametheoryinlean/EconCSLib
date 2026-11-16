/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Infrastructure.Core
import EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Infrastructure.WellFormed
import EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Infrastructure.Subgame
import EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Infrastructure.Finite
import EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Infrastructure.Quasi
import EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Infrastructure.Recall
import EconCSLib.GameTheory.ExtensiveGame.Winning.Basic

/-!
# Controlled observed-game infrastructure facade

API role: **canonical aggregate facade**. It owns no declarations.

This broad entry point re-exports the focused `Controlled.Infrastructure.*`
responsibility leaves. New implementation modules should import the narrowest
defining leaf, and winning-dependent quasistrategy predicates belong to
`Winning.Basic`.

This module intentionally contains imports and documentation only.
-/
