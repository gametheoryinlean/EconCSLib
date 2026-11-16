/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Interface.Equilibrium.Analytic
import EconCSLib.GameTheory.ExtensiveGame.Simulation.Restart.FiniteExecution
import EconCSLib.GameTheory.ExtensiveGame.Simulation.Restart.Equilibrium
import EconCSLib.GameTheory.ExtensiveGame.Simulation.Restart.Factorization

/-!
# Fresh-restart compatibility

Recommended pre-stability import for comparing fresh-clock restart semantics
with absolute-prefix continuation semantics.

The tier requires explicit compatibility for the baseline profile and every
admitted unilateral deviation. Its governed semantic surface is state-law
compatibility, deviation-complete compatibility at/on roots, and the canonical
rootwise, designated-root, subgame-perfection-on, and complete standard-SPE
`_of_compatible` transfers. Generated-law a.e. steps, rooted action kernels,
statistic factorization, and time-varying information rebasing are the
recommended constructors.

For finite discrete models, `Simulation.Restart.FiniteExecution` proves that
the exact fresh-clock, absolute-clock, and spliced `FiniteLaw` prefix queries
denote the existing analytic restart-prefix measures at every horizon.
For a high-level effective kernel behavioral profile with an explicit
analytic representation, `Simulation.Restart.Observed` also identifies every
finite marginal of the original continuation event/state laws, the time-zero
fresh-restart state law, and the coordinate-zero-normalized continuation event
law.  Event actions are retained until the state projection, and the fresh
clock is not identified with the absolute clock.
This is the restart branch of the semantic compatibility layer; neither clock
definition is treated as a legacy spelling of the other.

Transitive implementation declarations for splicing, finite prefixes,
partial trajectories, and certificate conversion remain available to proofs
but are not individually governed contracts. Certificate-specific equilibrium
wrappers are private; convert a certificate to state-law compatibility and
use the canonical transfer theorem. This tier makes no automatic
identification of the two clocks and no pointwise conditioning claim at null
histories.
-/
