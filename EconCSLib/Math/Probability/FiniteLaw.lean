/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.Math.Probability.FiniteLaw.Conditioning
import EconCSLib.Math.Probability.FiniteLaw.Coupling
import EconCSLib.Math.Probability.FiniteLaw.DeferredSampling
import EconCSLib.Math.Probability.FiniteLaw.Product

/-!
# Executable finite probability

Aggregate import for executable finite probability laws with exact
nonnegative-rational weights.

Start with `FiniteLaw.pure`, `FiniteLaw.map`, `FiniteLaw.bind`, and
`FiniteLaw.expectRat` in `FiniteLaw.Core`. `Product` constructs independent
finite families, `Conditioning` computes partial posteriors, `Coupling`
transports related joint laws, and `DeferredSampling` proves equivalence of
pre-sampled and on-demand fresh queries.

The outcome type need not be finite or decidably equal. Equality decisions
are explicit inputs to point-mass and fiber queries; products over a general
finite index type require a supplied enumeration and linear order. Zero-mass
conditioning returns `none`.

`FiniteLaw.Equivalent` compares exact rational expectations, allowing atom
lists with different orders or repeated outcomes. This executable interface
does not construct arbitrary real-weighted distributions or infinite path
measures.
-/
