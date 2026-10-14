/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.Math.Probability.Effective
import EconCSLib.Math.Probability.Effective.Semantics
import EconCSLib.Math.Probability.Effective.UniformSemantics

/-!
# Analytic semantics of effective probability queries

This opt-in aggregate connects the executable effective-probability layer to
Mathlib measures, kernels, and real integrals.  The underlying query programs
remain owned by the measure-free `Effective` aggregate.
-/
