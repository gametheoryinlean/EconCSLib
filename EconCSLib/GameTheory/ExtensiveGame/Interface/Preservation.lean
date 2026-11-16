/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Relations.Preservation

/-!
# EFG preservation certificates

Recommended pre-stability import for the relation-strength vocabulary used by
EFG compilers and semantic bridges.

The facade exposes strict structural isomorphisms, directional information
refinement, strict and weak simulations, bounded and complete-path
realizations, probability couplings, and strict/weak compiler packages. These
contracts deliberately retain different strengths. In particular, a coupling
is not an equality, an isomorphism, or bidirectional deviation coverage.

The measure-valued path-law vocabulary makes this facade broader than
`Interface.Relations.Discrete`; it does not import the non-atomic analytic
executor, equilibrium, restart, or compiler implementations.
-/
