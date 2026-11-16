/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.Math.Probability.Effective.Enclosure
import EconCSLib.Math.Probability.Effective.Core
import EconCSLib.Math.Probability.Effective.Uniform

/-!
# Effective probability queries

This is the aggregate import for the executable effective-probability layer.
It exposes rational enclosures, coded-event laws and kernels, and the exact
uniform-unit-interval backend without importing measures or real integrals.
Import `EconCSLib.Math.Probability.Effective.Analytic` for the separate
measure-theoretic correctness layer.
-/
