/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Observed.Game
import EconCSLib.Math.Probability.FiniteLaw.Core

/-!
# Finite pure-profile laws

This module gives finitely supported joint laws on complete pure profiles a
stable executable owner.  Such a law may correlate players.  Its player
marginals, evaluated outcomes, and executed complete paths are all computed by
the same finite `List.map` operation underlying `FiniteLaw.map`.

This executable owner does not import measure theory.  Exact semantic bridges
to `ArbitraryMeasurePureProfileLaw` live in
`Simulation.Equilibrium.FiniteMeasureStrategy`.

## Main definitions

* `ObservedGame.FinitePureProfileLaw`;
* `FinitePureProfileLaw.marginal`;
* `FinitePureProfileLaw.outcomeLaw`;
* `FinitePureProfileLaw.pathLaw`.

-/

namespace ExtensiveGame.ObservedGame

universe uN uU uOutcome

variable {N : Type uN} {U : Type uU}

/-- A finite exact joint law on complete pure profiles.

Unlike `MixedProfile`, this carrier permits correlation between players. -/
abbrev FinitePureProfileLaw (G : ObservedGame N U) :=
  FiniteLaw G.PureProfile

namespace FinitePureProfileLaw

variable {G : ObservedGame N U}

/-- Compute one player's marginal by projecting every joint-law atom to that
player's complete pure strategy. -/
def marginal (law : G.FinitePureProfileLaw) (i : N) :
    FiniteLaw (G.PureStrategy i) :=
  law.map fun profile => profile i

/-- Compute the pushforward of a finite pure-profile law through an outcome
evaluator. -/
def outcomeLaw (law : G.FinitePureProfileLaw)
    {Outcome : Type uOutcome} (evaluate : G.PureProfile → Outcome) :
    FiniteLaw Outcome :=
  law.map evaluate

/-- Compute the finite law on complete plays induced by a supplied pure-profile
executor. -/
def pathLaw (law : G.FinitePureProfileLaw)
    (execute : G.PureProfile → G.base.CompletePlay) :
    FiniteLaw G.base.CompletePlay :=
  law.map execute

@[simp]
theorem marginal_atoms (law : G.FinitePureProfileLaw) (i : N) :
    (law.marginal i).atoms =
      law.atoms.map fun atom => (atom.1 i, atom.2) :=
  rfl

@[simp]
theorem outcomeLaw_atoms (law : G.FinitePureProfileLaw)
    {Outcome : Type uOutcome} (evaluate : G.PureProfile → Outcome) :
    (law.outcomeLaw evaluate).atoms =
      law.atoms.map fun atom => (evaluate atom.1, atom.2) :=
  rfl

@[simp]
theorem pathLaw_atoms (law : G.FinitePureProfileLaw)
    (execute : G.PureProfile → G.base.CompletePlay) :
    (law.pathLaw execute).atoms =
      law.atoms.map fun atom => (execute atom.1, atom.2) :=
  rfl

theorem pathLaw_eq_outcomeLaw (law : G.FinitePureProfileLaw)
    (execute : G.PureProfile → G.base.CompletePlay) :
    law.pathLaw execute = law.outcomeLaw execute :=
  rfl

end FinitePureProfileLaw

end ExtensiveGame.ObservedGame
