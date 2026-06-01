/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# EconCSLib.Foundation.Player

Players are represented by elements of an arbitrary index type `N`.

**Convention**: use `Fin n` for concrete n-player games in examples.
Finiteness is added via `[Fintype N]` at theorem sites, never baked into structures.

This file contains no definitions — it documents the player-type convention
shared across all subfields of the library.
-/
