/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Basic
import EconCSLib.GameTheory.ExtensiveGame.Structural.Reachability

/-!
# EconCSLib.GameTheory.ExtensiveGame.Execution.Reachability

Payoff-aware reachability compatibility for the Arena extensive-game model.

The representation-neutral `Arena.Reachable` relation and the payoff-free
`ControlledGame.IsReachable` specialization live in
`Structural.Reachability`. This module adds only the historical
`ExtensiveGame.IsReachable` projection.

## Main definitions

* `ExtensiveGame.IsReachable` — reachability from an extensive game's initial
  state.
-/

namespace ExtensiveGame

variable {N : Type*} {U : Type*}

/-- A state is reachable in the game if it is reachable from `init`. -/
def IsReachable (G : ExtensiveGame N U) (s : G.State) : Prop :=
  G.toControlledGame.IsReachable s

/-- The initial state is always reachable. -/
theorem isReachable_init (G : ExtensiveGame N U) : G.IsReachable G.init :=
  ControlledGame.isReachable_init G.toControlledGame

/-- If `s` is reachable and we take action `a`, then `next s a` is reachable. -/
theorem IsReachable.next {G : ExtensiveGame N U} {s : G.State}
    (h : G.IsReachable s) (a : G.Action s) :
    G.IsReachable (G.next s a) :=
  h.step' a

end ExtensiveGame
