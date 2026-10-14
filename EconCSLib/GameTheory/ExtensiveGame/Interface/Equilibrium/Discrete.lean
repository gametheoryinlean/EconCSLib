/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Interface.Relations.Discrete
import EconCSLib.GameTheory.ExtensiveGame.Observed.Morphism.Continuation
import EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Morphism.Objective
import EconCSLib.GameTheory.ExtensiveGame.Observed.BehaviorMorphism
import EconCSLib.GameTheory.ExtensiveGame.Observed.Refinement.Termination
import EconCSLib.GameTheory.ExtensiveGame.Observed.BehaviorRefinement.Execution
import EconCSLib.GameTheory.ExtensiveGame.Observed.MorphismHierarchy
import EconCSLib.GameTheory.ExtensiveGame.Observed.SPE
import EconCSLib.GameTheory.ExtensiveGame.Observed.Semantics
import EconCSLib.GameTheory.ExtensiveGame.Observed.PerfectRecall
import EconCSLib.GameTheory.ExtensiveGame.Observed.Realization
import EconCSLib.GameTheory.ExtensiveGame.Observed.Mixed
import EconCSLib.GameTheory.ExtensiveGame.Observed.General
import EconCSLib.GameTheory.ExtensiveGame.Observed.Continuation
import EconCSLib.GameTheory.ExtensiveGame.Observed.Kuhn
import EconCSLib.GameTheory.ExtensiveGame.Observed.DeferredSampling.Realization
import EconCSLib.GameTheory.ExtensiveGame.Observed.KuhnConditioning.Realization
import EconCSLib.GameTheory.ExtensiveGame.Observed.LawEquivalence
import EconCSLib.GameTheory.ExtensiveGame.Observed.StrategyBridge
import EconCSLib.GameTheory.ExtensiveGame.Observed.FinitePureNash
import EconCSLib.GameTheory.ExtensiveGame.Observed.FiniteMeasureStrategy

/-!
# Discrete EFG equilibrium

Recommended pre-stability import for pure, behavioral, mixed, and
discrete-general finite-fuel strategy semantics and the available structural
representation-transfer theorems.

It extends `Interface.Relations.Discrete` with bounded and
termination-certified equilibrium predicates, subgame perfection on lawful
systems, payoff-free outcome-parametric continuation semantics and its
state-payoff compatibility spelling, perfect recall, finite-law realization, finite
Kuhn bridges, conditioning, the countably supported general-strategy carrier,
the uniform strategy bridge, and exact finite-horizon pure Nash checking when
the original root-bound information/action tables are explicitly enumerable.
Finite joint pure-profile laws expose executable marginal, outcome, and path
pushforwards without importing measure theory.
It does not import infinite path measures,
non-atomic measurable kernels, measurable path utilities, continuation
conditioning, fresh-clock restart, or concrete compilers.

The complete-history-law layer records one-way realizations separately from
strict isomorphisms and derives terminal/outcome/payoff and law-utility
equality by pushforward.
-/
