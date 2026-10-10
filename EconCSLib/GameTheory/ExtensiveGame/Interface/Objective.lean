/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Interface.Core
import EconCSLib.GameTheory.ExtensiveGame.Execution.Objective
import EconCSLib.GameTheory.ExtensiveGame.Observed.Quasi
import EconCSLib.GameTheory.ExtensiveGame.Observed.SignalRecall
import EconCSLib.GameTheory.ExtensiveGame.Winning.Basic
import EconCSLib.GameTheory.ExtensiveGame.Winning.Topology

/-!
# EconCSLib.GameTheory.ExtensiveGame.Interface.Objective

Recommended pre-stability facade for measure-free complete plays, structural
length and well-foundedness certificates, history-sensitive terminal/path
outcomes, and complete-play winning conditions. It also exposes finite
agreement cylinders, prefix-open/closed events, finite-prefix decision
witnesses, and the generated prefix topology/measurable space.
Information-consistent quasistrategies provide a probability-free
nondeterministic permission layer.

This tier does not import probability laws, equilibrium, compilers, analytic
kernels, or determinacy theorems. It is suitable for defining a new EFG
objective and robust pure winning strategy independently of later stochastic
or equilibrium solution concepts.
-/
