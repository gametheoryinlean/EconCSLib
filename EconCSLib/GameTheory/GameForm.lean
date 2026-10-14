/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.GameForm.Basic
import EconCSLib.GameTheory.GameForm.Continuation.Core
import EconCSLib.GameTheory.GameForm.Continuation.Simulation
import EconCSLib.GameTheory.GameForm.Continuation.Iso
import EconCSLib.GameTheory.GameForm.IndexedContinuation
import EconCSLib.GameTheory.GameForm.Law

/-!
# EconCSLib.GameTheory.GameForm

Stable aggregate import for representation-neutral game-form semantics.

The layer is split into deterministic outcomes, normalized outcome laws,
families of continuation game forms sharing one complete strategy space, and
an arbitrary-index adapter for bounded, total, or limiting semantics.

The historical `GameForm.LimitSPE` path remains available by explicit import;
it is not part of this stable aggregate.
-/
