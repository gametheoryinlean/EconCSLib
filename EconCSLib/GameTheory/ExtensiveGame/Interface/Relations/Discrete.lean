/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Interface.Execution.Finite
import EconCSLib.GameTheory.ExtensiveGame.Relations.Discrete.Morphism
import EconCSLib.GameTheory.ExtensiveGame.Relations.Discrete.StochasticNaturality
import EconCSLib.GameTheory.ExtensiveGame.Execution.Discrete.KernelTrajectory
import EconCSLib.GameTheory.ExtensiveGame.Relations.Discrete.KernelWeakSimulation
import EconCSLib.GameTheory.ExtensiveGame.Observed.Morphism.Operational
import EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Morphism.Core
import EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Morphism.Subgame
import EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Morphism.Recall
import EconCSLib.GameTheory.ExtensiveGame.Observed.Chance
import EconCSLib.GameTheory.ExtensiveGame.Observed.Behavior
import EconCSLib.GameTheory.ExtensiveGame.Observed.Refinement.Structural
import EconCSLib.GameTheory.ExtensiveGame.Observed.BehaviorRefinement.Structural

/-!
# Discrete and structural EFG relations

Recommended pre-stability import for strict structural representation
changes, information refinements, finite-kernel trajectory couplings, and
weak/stuttering simulations. The strict structural tier includes the
payoff-free `ControlledObservedGame.Hom`/`Iso` hierarchy and external root,
recall, and lawful-subgame transport; payoff compatibility is a separate
extension certificate.


It extends `Interface.Execution.Finite` and deliberately excludes
measure-valued infinite paths and the `MeasurableKernelArena` implementation
stack. Continuation/Nash transfer belongs to `Interface.Equilibrium.Discrete`;
analytic execution remains available directly through
`Interface.Execution.Analytic`.
-/
