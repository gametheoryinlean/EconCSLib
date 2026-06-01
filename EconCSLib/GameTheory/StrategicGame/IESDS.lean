/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.StrategicGame.NashEquilibrium
import Mathlib.Tactic.Linarith

/-!
# EconCSLib.GameTheory.StrategicGame.IESDS

Iterated elimination of strictly dominated strategies (IESDS) and rationalizability.

## Main definitions

* `Survives G n i s` — strategy `s` survives round `n` of elimination
* `IsRationalizable G i s` — survives all rounds
* `IsDominanceSolvable G` — IESDS yields a unique profile

## Main results

* `survives_mono` — survival is monotone decreasing in rounds
* `nash_implies_rationalizable` — Nash strategies are rationalizable [MSZ 4.31]

## References

* [MSZ] Section 4.2, Theorems 4.31, 4.33, 4.37
-/

namespace StrategicGame

variable {N U : Type*} [DecidableEq N] [Preorder U]

open StrategicGame

/-- A strategy survives round `n` of iterated strict dominance elimination.
    Round 0: all strategies survive.
    Round n+1: `s` survives if it survived round `n` and is not strictly
    dominated by any round-n survivor. -/
def Survives (G : StrategicGame N U) : ℕ → (i : N) → G.strategy i → Prop
  | 0 => fun _ _ => True
  | n + 1 => fun i s =>
      G.Survives n i s ∧
      ¬ ∃ t : G.strategy i, G.Survives n i t ∧
        ∀ σ : G.Profile, (∀ j, G.Survives n j (σ j)) →
          G.payoff (deviate σ i s) i < G.payoff (deviate σ i t) i

/-- Survival at round n+1 implies survival at round n. -/
theorem Survives.prev {G : StrategicGame N U} {n : ℕ} {i : N} {s : G.strategy i}
    (h : G.Survives (n + 1) i s) : G.Survives n i s :=
  h.1

/-- Survival is monotone: later rounds ⊆ earlier rounds. -/
theorem Survives.mono {G : StrategicGame N U} {m n : ℕ} (hmn : m ≤ n)
    {i : N} {s : G.strategy i} (h : G.Survives n i s) : G.Survives m i s := by
  induction hmn with
  | refl => exact h
  | step _ ih => exact ih h.prev

/-- A strategy is rationalizable if it survives all rounds. -/
def IsRationalizable (G : StrategicGame N U) (i : N) (s : G.strategy i) : Prop :=
  ∀ n, G.Survives n i s

/-- Nash equilibrium strategies survive all rounds. [MSZ 4.31] -/
theorem IsNashEquilibrium.survives {G : StrategicGame N U}
    {σ : G.Profile} (hN : IsNashEquilibrium G σ) :
    ∀ (n : ℕ) (i : N), G.Survives n i (σ i) := by
  intro n; induction n with
  | zero => intro _; trivial
  | succ n ih =>
    intro i; refine ⟨ih i, ?_⟩
    -- Need: ¬ ∃ t, Survives n i t ∧ ∀ σ', (∀ j, Survives n j (σ' j)) → payoff(deviate σ' i (σ i)) < payoff(deviate σ' i t)
    intro ⟨t, _, hdom⟩
    -- Specialize hdom to the Nash profile σ (whose strategies all survive by ih)
    have hd := hdom σ ih
    -- This says: payoff(σ, i) < payoff(deviate σ i t, i) (since deviate σ i (σ i) = σ)
    simp [Profile.deviate_self] at hd
    -- But Nash says σ i is a best response: payoff(deviate σ i t, i) ≤ payoff(σ, i)
    exact absurd (lt_of_lt_of_le hd (hN i t)) (lt_irrefl _)

/-- Nash strategies are rationalizable. -/
theorem IsNashEquilibrium.isRationalizable {G : StrategicGame N U}
    {σ : G.Profile} (hN : IsNashEquilibrium G σ) (i : N) :
    G.IsRationalizable i (σ i) :=
  fun n => hN.survives n i

/-- A game is dominance-solvable if IESDS yields a unique surviving profile. -/
def IsDominanceSolvable (G : StrategicGame N U) : Prop :=
  ∃! σ : G.Profile, ∀ i, ∀ n, G.Survives n i (σ i)

end StrategicGame
