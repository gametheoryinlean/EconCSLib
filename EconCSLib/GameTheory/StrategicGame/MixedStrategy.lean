/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.StrategicGame.NashEquilibrium
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp

/-!
# EconCSLib.GameTheory.StrategicGame.MixedStrategy

Mixed strategies and mixed Nash equilibrium for arbitrary player sets,
polymorphic in the payoff field `U`.

## Design

* `MixedProfile G` = a mixed strategy for each player, for any `N`
* `IsCompletelyMixed G p i` = player `i` assigns positive probability to every
  pure strategy
* `IsCompletelyMixedProfile G p` = every player is completely mixed
* `expectedPayoff G p who` = expected payoff (requires `[Fintype N]` and `[∀ i, Fintype (G.strategy i)]`)
* `IsMixedNashEq G p` = no player can improve by deviating to any pure strategy

The payoff type `U` is polymorphic with `[Field U] [LinearOrder U]
[IsStrictOrderedRing U]`. This covers both `ℚ` (for `native_decide`-style
constructive examples) and `ℝ` (for the Loomis minimax theorem).

Key Bourbaki point: `StrategicGame` and `MixedProfile` have NO finiteness
constraints. `[Fintype N]` is only added to theorems/definitions that need
computation.

## References

* [MSZ] Chapter 5
-/

open Finset BigOperators

namespace StrategicGame

variable {N U : Type*} [Field U] [LinearOrder U] [IsStrictOrderedRing U]

/-! ### Mixed strategies and profiles -/

/-- A mixed strategy for player `i`: a probability distribution over pure strategies.
    Requires `[Fintype (G.strategy i)]` but NOT `[Fintype N]`. -/
abbrev MixedStrategy (G : StrategicGame N U) (i : N) [Fintype (G.strategy i)] :=
  stdSimplex U (G.strategy i)

/-- A mixed profile: each player has a mixed strategy.
    No finiteness constraint on `N` (player set can be arbitrary). -/
def MixedProfile (G : StrategicGame N U) [∀ i, Fintype (G.strategy i)] :=
  ∀ i, MixedStrategy G i

/-! ### Complete mixing -/

/-- A player's mixed strategy is completely mixed if every pure strategy is
    assigned positive probability. This is the strategic-form mixed-strategy
    part of MSZ Definition 7.6. -/
def IsCompletelyMixed
    (G : StrategicGame N ℚ) {i : N} [Fintype (G.strategy i)]
    (p : MixedStrategy G i) : Prop :=
  ∀ s : G.strategy i, 0 < p.val s

/-- A mixed profile is completely mixed if every player's mixed strategy is
    completely mixed. -/
def IsCompletelyMixedProfile
    (G : StrategicGame N ℚ) [∀ i, Fintype (G.strategy i)]
    (p : MixedProfile G) : Prop :=
  ∀ i : N, IsCompletelyMixed G (p i)

/-- A completely mixed profile gives a completely mixed strategy for each player. -/
theorem IsCompletelyMixedProfile.player {G : StrategicGame N ℚ}
    [∀ i, Fintype (G.strategy i)] {p : MixedProfile G}
    (hp : IsCompletelyMixedProfile G p) (i : N) :
    IsCompletelyMixed G (p i) :=
  hp i

/-! ### Constructors -/

/-- Embed a pure strategy as a mixed strategy (point mass). -/
def pureToMixed {G : StrategicGame N U}
    {i : N} [Fintype (G.strategy i)] [DecidableEq (G.strategy i)]
    (s₀ : G.strategy i) : MixedStrategy G i where
  val s := if s = s₀ then 1 else 0
  property := ⟨fun s => by simp only; split_ifs <;> norm_num,
               by simp [Finset.sum_ite_eq', Finset.mem_univ]⟩

/-- The uniform mixed strategy over a finite nonempty strategy set. -/
def uniformMixed {G : StrategicGame N U}
    {i : N} [Fintype (G.strategy i)] [Nonempty (G.strategy i)] :
    MixedStrategy G i where
  val _ := 1 / Fintype.card (G.strategy i)
  property := ⟨fun _ => by positivity,
               by simp [Finset.sum_const, Finset.card_univ]⟩

/-- The uniform mixed strategy assigns `1 / card` to every pure strategy. -/
theorem uniformMixed_apply {G : StrategicGame N ℚ}
    {i : N} [Fintype (G.strategy i)] [Nonempty (G.strategy i)]
    (s : G.strategy i) :
    (uniformMixed (G := G) (i := i)).val s = 1 / Fintype.card (G.strategy i) :=
  rfl

/-- Every pure strategy has positive probability under the uniform mixed strategy. -/
theorem uniformMixed_pos {G : StrategicGame N ℚ}
    {i : N} [Fintype (G.strategy i)] [Nonempty (G.strategy i)]
    (s : G.strategy i) :
    0 < (uniformMixed (G := G) (i := i)).val s := by
  rw [uniformMixed_apply]
  exact one_div_pos.mpr (Nat.cast_pos.mpr (Fintype.card_pos (α := G.strategy i)))

/-- The uniform mixed strategy is completely mixed on any finite nonempty
    strategy set. -/
theorem uniformMixed_isCompletelyMixed {G : StrategicGame N ℚ}
    {i : N} [Fintype (G.strategy i)] [Nonempty (G.strategy i)] :
    IsCompletelyMixed G (uniformMixed (G := G) (i := i)) := by
  intro s
  exact uniformMixed_pos (G := G) (i := i) s

/-- The profile where every player uses the uniform mixed strategy. -/
def uniformMixedProfile
    (G : StrategicGame N ℚ) [∀ i, Fintype (G.strategy i)]
    [∀ i, Nonempty (G.strategy i)] : MixedProfile G :=
  fun i => uniformMixed (G := G) (i := i)

/-- The uniform mixed profile is completely mixed. -/
theorem uniformMixedProfile_isCompletelyMixed
    (G : StrategicGame N ℚ) [∀ i, Fintype (G.strategy i)]
    [∀ i, Nonempty (G.strategy i)] :
    IsCompletelyMixedProfile G (uniformMixedProfile G) := by
  intro i
  exact uniformMixed_isCompletelyMixed (G := G) (i := i)

/-- A point-mass mixed strategy is not completely mixed when there is another
    pure strategy available. -/
theorem pureToMixed_not_isCompletelyMixed_of_ne {G : StrategicGame N ℚ}
    {i : N} [Fintype (G.strategy i)] [DecidableEq (G.strategy i)]
    {s₀ s₁ : G.strategy i} (h : s₁ ≠ s₀) :
    ¬ IsCompletelyMixed G (pureToMixed (G := G) (i := i) s₀) := by
  intro hcm
  have hpos := hcm s₁
  simp [pureToMixed, h] at hpos

/-- Embed a pure profile as a mixed profile. -/
def pureProfileToMixed {G : StrategicGame N U}
    [∀ i, Fintype (G.strategy i)] [∀ i, DecidableEq (G.strategy i)]
    (σ : G.Profile) : MixedProfile G :=
  fun i => pureToMixed (σ i)

/-! ### Expected payoff -/

/-- Expected payoff for player `who` under mixed profile `p`.

    `EU(p, who) = ∑_{σ : Profile} (∏_i p_i(σ_i)) · payoff(σ, who)`

    Requires `[Fintype N]` (to sum over all profiles) and
    `[∀ i, Fintype (G.strategy i)]` (finite strategy sets). -/
def expectedPayoff
    (G : StrategicGame N U)
    [Fintype N] [DecidableEq N] [∀ i, Fintype (G.strategy i)]
    (p : MixedProfile G) (who : N) : U :=
  ∑ σ : G.Profile, (∏ i : N, (p i).val (σ i)) * G.payoff σ who

/-- Deviate player `who` to pure strategy `s'`, keeping others' mixed strategies. -/
def deviateMixed
    (G : StrategicGame N U)
    [∀ i, Fintype (G.strategy i)] [DecidableEq N] [∀ i, DecidableEq (G.strategy i)]
    (p : MixedProfile G) (who : N) (s' : G.strategy who) : MixedProfile G :=
  Function.update p who (pureToMixed s')

/-! ### Mixed Nash equilibrium -/

/-- A mixed profile is a mixed Nash equilibrium if no player can improve their
    expected payoff by deviating to any pure strategy.

    By linearity of expected payoff in each player's mixed strategy, checking
    pure deviations suffices. [MSZ 5.5, 5.18]

    Requires `[Fintype N]` for expected payoff computation. -/
def IsMixedNashEq
    (G : StrategicGame N U)
    [Fintype N] [DecidableEq N]
    [∀ i, Fintype (G.strategy i)] [∀ i, DecidableEq (G.strategy i)]
    (p : MixedProfile G) : Prop :=
  ∀ (who : N) (s' : G.strategy who),
    expectedPayoff G (deviateMixed G p who s') who ≤
    expectedPayoff G p who

end StrategicGame
