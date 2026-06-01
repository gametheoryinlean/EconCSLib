/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.StrategicGame.ZeroSum.MatrixGame
import EconCSLib.GameTheory.StrategicGame.ZeroSum.MatrixGameNash
import Mathlib.Algebra.BigOperators.Field

/-!
# EconCSLib.GameTheory.StrategicGame.ZeroSum.Learning.FictitiousPlay

Fictitious play for a finite zero-sum matrix game over `ℝ`. This module
introduces the basic vocabulary used throughout the Robinson 1951 convergence
analysis:

* `empiricalFrequency` — the empirical distribution of the first `n` pure
  actions of an infinite sequence.
* `IsFictitiousPlay` — predicate on pairs `(iSeq, jSeq) : (ℕ → I) × (ℕ → J)`
  asserting that at every step both players best-respond to the opponent's
  empirical frequency so far.

The Robinson induction-on-matrix-size proof itself lives in
`StrategicGame/FictitiousPlay/Robinson.lean`; the Cesàro payoff convergence
in `StrategicGame/FictitiousPlay/Cesaro.lean`; the main convergence theorem
in `StrategicGame/FictitiousPlay/Convergence.lean`; the continuous-time
variant in `StrategicGame/FictitiousPlay/Continuous.lean`.

## References

* [MFoGT] Laraki, Renault, Sorin, *Mathematical Foundations of Game Theory*,
  Definition 2.7.1 and Theorem 2.7.2.
* [Robinson 1951] J. Robinson, "An iterative method of solving a game",
  *Annals of Mathematics* 54 (1951), 296–301.

## Blueprint

* `docs/knowledge/staged/zero_sum/empirical_frequency.md`
* `docs/knowledge/staged/zero_sum/fictitious_play.md`
-/

open Finset BigOperators

set_option linter.unusedSectionVars false

namespace MatrixGame

variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] [DecidableEq I] [DecidableEq J]

/-- **Empirical frequency** of the first `n` pure actions of a sequence
`a : ℕ → I`. For `n = 0` we fall back to the uniform distribution so the
function is total; the FP statements always require `0 < n`. -/
noncomputable def empiricalFrequency (a : ℕ → I) (n : ℕ) : stdSimplex ℝ I :=
  if hn : 0 < n then
    ⟨fun i => (((Finset.range n).filter (fun s => a s = i)).card : ℝ) / n, by
      refine ⟨fun i => ?_, ?_⟩
      · positivity
      · have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
        have hsum_div :
            (∑ i, (((Finset.range n).filter (fun s => a s = i)).card : ℝ) / n)
              = (∑ i, (((Finset.range n).filter (fun s => a s = i)).card : ℝ)) / n := by
          rw [← Finset.sum_div]
        rw [hsum_div]
        have hcount :
            (∑ i, ((Finset.range n).filter (fun s => a s = i)).card)
              = (Finset.range n).card := by
          rw [← Finset.card_eq_sum_card_fiberwise (f := a)
                (s := Finset.range n) (t := Finset.univ)
                (fun s _ => Finset.mem_univ (a s))]
        have hsum_real :
            (∑ i, (((Finset.range n).filter (fun s => a s = i)).card : ℝ))
              = (n : ℝ) := by
          calc
            (∑ i, (((Finset.range n).filter (fun s => a s = i)).card : ℝ))
                = ((∑ i, ((Finset.range n).filter (fun s => a s = i)).card : ℕ) : ℝ) := by
                  push_cast; rfl
            _ = ((Finset.range n).card : ℝ) := by exact_mod_cast hcount
            _ = (n : ℝ) := by rw [Finset.card_range]
        rw [hsum_real, div_self hn_pos.ne']⟩
  else
    ⟨fun _ => (Fintype.card I : ℝ)⁻¹, by
      have hcard : 0 < Fintype.card I := Fintype.card_pos
      have hpos : (0 : ℝ) < (Fintype.card I : ℝ) := by exact_mod_cast hcard
      refine ⟨fun _ => le_of_lt (inv_pos.mpr hpos), ?_⟩
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      field_simp⟩

/-- **Fictitious play realisation** on a matrix game `A`. At every step
`n + 1`, the row player picks a pure row best-responding to the column
player's empirical frequency `y_n`, and dually for the column player. The
`n = 0` "warm-up" step is unconstrained (the empirical frequency is undefined
before any play has occurred). -/
def IsFictitiousPlay (A : MatrixGame I J ℝ) (iSeq : ℕ → I) (jSeq : ℕ → J) : Prop :=
  ∀ n : ℕ, 0 < n →
    (∀ k : I, A.Ei k (empiricalFrequency jSeq n) ≤ A.Ei (iSeq n) (empiricalFrequency jSeq n)) ∧
    (∀ ℓ : J, A.Ej (empiricalFrequency iSeq n) (jSeq n) ≤ A.Ej (empiricalFrequency iSeq n) ℓ)

end MatrixGame
