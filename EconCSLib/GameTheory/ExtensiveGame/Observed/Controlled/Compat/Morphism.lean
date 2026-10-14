/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Morphism.Core
import EconCSLib.GameTheory.ExtensiveGame.Observed.Morphism.Inverse

/-!
# Payoff-aware adapters for controlled observed-game morphisms

API role: **downstream payoff-aware adapter**. Its location under
`Controlled.Compat` marks it as non-canonical, and canonical controlled
modules must never import it.

The strict structural relation is owned by `Controlled.Morphism.Core`. This
module adds only the terminal-payoff square and conversion from the
payoff-aware `ObservedGame.Iso`.
-/

namespace ExtensiveGame.ObservedGame

variable {N U : Type*}

/-- A payoff-compatible strict isomorphism is a payoff-free structural
isomorphism plus the terminal-payoff commuting square. -/
structure PayoffCompatibleIso
    (G H : ObservedGame N U) where
  /-- Underlying payoff-free strict isomorphism. -/
  structural :
    G.toControlledObservedGame.Iso
      H.toControlledObservedGame
  /-- Terminal payoff vectors agree at corresponding histories. -/
  map_payoff :
    ∀ history : G.base.toArena.HistoryFrom G.base.init,
      G.base.isTerminal history.1 →
      H.base.payoff
          (structural.historyIso.stateEquiv history).1 =
        G.base.payoff history.1

namespace Iso

variable {G H : ObservedGame N U}

/-- Repackage the legacy strict isomorphism as a structural isomorphism plus
orthogonal payoff compatibility. -/
def toPayoffCompatibleIso (e : G.Iso H) :
    G.PayoffCompatibleIso H where
  structural := e.toControlledIso
  map_payoff := e.map_payoff

end Iso

end ExtensiveGame.ObservedGame
