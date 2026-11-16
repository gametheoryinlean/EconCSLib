/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Interface.Objective
import EconCSLib.GameTheory.ExtensiveGame.Winning.Determinacy
import EconCSLib.GameTheory.ExtensiveGame.Winning.DeterminacyCompat

/-!
# EconCSLib.GameTheory.ExtensiveGame.Interface.Winning

Recommended pre-stability facade for logical extensive games: complete-play
winning conditions, pathwise robust and profile-based pure winning strategies,
pathwise quasi winning strategies, two-player determinacy predicates, and
explicit finite/well-founded determinacy hypothesis packages.

The facade does not claim arbitrary winning-set determinacy. The payoff-free
finite perfect-information, no-chance, two-player zero-sum theorem is exposed
as `FiniteTwoPlayerHypotheses.isTwoPlayerDetermined`; the strictly broader
well-founded result is
`WellFoundedPrefixHypotheses.isTwoPlayerDetermined`. Gale--Stewart
open/closed existence remains a separate theorem track; topological and
almost-sure winning remain later opt-in layers. For arbitrary player types,
`HasSomePathwiseWinningStrategy` is deliberately not named “determined.”
-/
