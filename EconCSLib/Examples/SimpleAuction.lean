/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.StrategicGame.Dominance
import EconCSLib.GameTheory.StrategicGame.NashEquilibrium
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.FinCases

/-!
# EconCSLib.Examples.SimpleAuction

A 2-bidder Vickrey (second-price sealed-bid) auction as a `StrategicGame`.

Design:
- Players: `Fin 2`
- Bids: `Fin n` (discrete bids 0 … n-1) for computability
- Valuations: fixed `v : Fin 2 → Fin n`
- Winner: highest bidder wins; player 0 wins ties
- Payment: winner pays the opponent's bid (second-price)
- Payoffs in `ℤ` so that overbidding can yield *negative* utility

Key result (T7): Truthful bidding is weakly dominant for each player.

**Proof technique**: After `intro s' b`, rewrite payoffs using definitional equality (`rfl`)
to expose the `if-then-else` arithmetic form, then close with `split_ifs <;> omega`.
The `rfl`s hold because Lean evaluates `(1 : Fin 2) = 0` to `false` via `DecidableEq`,
and `Function.update` reduces at constant indices.

Concrete instance (n=4, v=(2,3)) is also verified by `native_decide`.
-/

variable (n : ℕ) [NeZero n]

/-- 2-bidder Vickrey auction. Payoffs in `ℤ` so overbidding yields negative utility. -/
def Vickrey (v : Fin 2 → Fin n) : StrategicGame (Fin 2) ℤ where
  strategy := fun _ => Fin n
  payoff b i :=
    let b0 : ℤ := (b 0).val
    let b1 : ℤ := (b 1).val
    if i = 0 then
      if b0 ≥ b1 then (v 0).val - b1   -- player 0 wins (including ties), pays b1
      else 0
    else
      if b1 > b0 then (v 1).val - b0   -- player 1 wins (strict), pays b0
      else 0

namespace Vickrey

open StrategicGame

/-!
### Payoff unfolding lemmas (proved by `rfl`)

These are the key computational steps: `Lean` evaluates `(0 : Fin 2) = 0` to `true`
and `(1 : Fin 2) = 0` to `false` via `DecidableEq`, and reduces `Function.update`
at its updated and unchanged indices.
-/

omit [NeZero n] in
private lemma payoff_p0_dev (v : Fin 2 → Fin n) (b : Fin 2 → Fin n) (s' : Fin n) :
    (Vickrey n v).payoff (deviate b 0 s') 0 =
    if (s'.val : ℤ) ≥ (b 1).val then (v 0).val - ((b 1).val : ℤ) else 0 := rfl

omit [NeZero n] in
private lemma payoff_p0_truth (v : Fin 2 → Fin n) (b : Fin 2 → Fin n) :
    (Vickrey n v).payoff (deviate b 0 (v 0)) 0 =
    if ((v 0).val : ℤ) ≥ (b 1).val then (v 0).val - ((b 1).val : ℤ) else 0 := rfl

omit [NeZero n] in
private lemma payoff_p1_dev (v : Fin 2 → Fin n) (b : Fin 2 → Fin n) (s' : Fin n) :
    (Vickrey n v).payoff (deviate b 1 s') 1 =
    if (s'.val : ℤ) > (b 0).val then (v 1).val - ((b 0).val : ℤ) else 0 := rfl

omit [NeZero n] in
private lemma payoff_p1_truth (v : Fin 2 → Fin n) (b : Fin 2 → Fin n) :
    (Vickrey n v).payoff (deviate b 1 (v 1)) 1 =
    if ((v 1).val : ℤ) > (b 0).val then (v 1).val - ((b 0).val : ℤ) else 0 := rfl

omit [NeZero n] in
/-- T7 (player 0): Truthful bidding is weakly dominant.
    Core insight: if you bid truthfully, you win exactly when winning is profitable. -/
theorem truthful_weakly_dominant_p0 (v : Fin 2 → Fin n) :
    IsWeaklyDominant (Vickrey n v) 0 (v 0) := by
  intro s' b
  rw [payoff_p0_dev n v b s', payoff_p0_truth n v b]
  split_ifs <;> omega

omit [NeZero n] in
/-- T7 (player 1): Truthful bidding is weakly dominant. -/
theorem truthful_weakly_dominant_p1 (v : Fin 2 → Fin n) :
    IsWeaklyDominant (Vickrey n v) 1 (v 1) := by
  intro s' b
  rw [payoff_p1_dev n v b s', payoff_p1_truth n v b]
  split_ifs <;> omega

end Vickrey

/-!
## Concrete instance: n=4, v=(2,3)

Cross-check: the general theorem implies dominance in this instance, and we also
verify directly by `native_decide` (exhaustive evaluation over `Fin 4` profiles).
-/

section ConcreteAuction

private def v4 : Fin 2 → Fin 4
  | 0 => ⟨2, by omega⟩
  | 1 => ⟨3, by omega⟩

-- Bridge: expose (Vickrey 4 v4).strategy j = Fin 4 for native_decide
private instance (j : Fin 2) : Fintype ((Vickrey 4 v4).strategy j) :=
  inferInstanceAs (Fintype (Fin 4))
private instance (j : Fin 2) : DecidableEq ((Vickrey 4 v4).strategy j) :=
  inferInstanceAs (DecidableEq (Fin 4))

/-- Direct `native_decide` verification: truthful is weakly dominant for player 0. -/
theorem vickrey4_p0_dominant : IsWeaklyDominant (Vickrey 4 v4) 0 (v4 0) := by
  show ∀ (s' : Fin 4) (b : Fin 2 → Fin 4),
    (Vickrey 4 v4).payoff (StrategicGame.deviate b 0 s') 0 ≤
      (Vickrey 4 v4).payoff (StrategicGame.deviate b 0 (v4 0)) 0
  native_decide

/-- Direct `native_decide` verification: truthful is weakly dominant for player 1. -/
theorem vickrey4_p1_dominant : IsWeaklyDominant (Vickrey 4 v4) 1 (v4 1) := by
  show ∀ (s' : Fin 4) (b : Fin 2 → Fin 4),
    (Vickrey 4 v4).payoff (StrategicGame.deviate b 1 s') 1 ≤
      (Vickrey 4 v4).payoff (StrategicGame.deviate b 1 (v4 1)) 1
  native_decide

/-- Truthful bidding profile is a Nash equilibrium in the concrete instance (via T3). -/
theorem vickrey4_truthful_nash : IsNashEquilibrium (Vickrey 4 v4) v4 :=
  IsNashEquilibrium.of_dominant fun i => by
    fin_cases i
    · exact vickrey4_p0_dominant
    · exact vickrey4_p1_dominant

end ConcreteAuction
