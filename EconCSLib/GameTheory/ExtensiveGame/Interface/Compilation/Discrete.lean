/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Interface.Equilibrium.Discrete
import EconCSLib.GameTheory.ExtensiveGame.FOSG.FOSG
import EconCSLib.GameTheory.ExtensiveGame.FOSG.FOSGBehavioralSerialization
import EconCSLib.GameTheory.ExtensiveGame.FOSG.Sequentialization.Equilibrium
import EconCSLib.GameTheory.ExtensiveGame.FOSG.FOSGContinuation
import EconCSLib.GameTheory.ExtensiveGame.Compiler.GameTreeOccurrenceObserved
import EconCSLib.GameTheory.ExtensiveGame.Compiler.StochasticGameTreeObserved
import EconCSLib.GameTheory.ExtensiveGame.Compiler.FiniteImperfectObserved

/-!
# Discrete EFG compilation

Recommended pre-stability import for the FOSG serializers with exact finite laws and
finite reference observed-EFG compilers.

It extends `Interface.Equilibrium.Discrete` and does not import the analytic
measurable-kernel execution/equilibrium stack. Clients needing that sibling
branch import `Interface.Equilibrium.Analytic` explicitly.
-/
