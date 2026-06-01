/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.StrategicGame.ZeroSum.Learning.FictitiousPlay

/-!
# EconCSLib.GameTheory.StrategicGame.ZeroSum.Learning.Robinson

Robinson's admissible-sequence lemma (Robinson 1951; MFoGT Section 2.8,
Exercise 12): for every matrix game `A`, every `ε > 0`, and every admissible
sequence on `A`, the cumulative duality gap `μ(t)` is eventually `≤ ε·t`.

This module defines the objects used by that argument. The proof targets remain
recorded in the knowledge blueprint until formal proofs are added.

## Main definitions

* `AdmissibleSequence A` — a sequence of cumulative counterfactual payoff
  vectors `(α(t), β(t))` on `A` satisfying the Robinson update rule.
* `AdmissibleSequence.mu` — the cumulative duality gap `max_i β^i - min_j α^j`.
* `MatrixGame.normMax` — `‖A‖ = max_{i,j} |A i j|`.
-/

open Finset BigOperators

set_option linter.unusedSectionVars false

namespace MatrixGame

variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]

/-- `‖A‖ := max_{i,j} |A_{i,j}|`, the entrywise sup norm of the payoff matrix.

Field-generic in the abstract, but the Robinson analysis is stated over `ℝ`
(needed for the asymptotic `o(t)` formulation). -/
noncomputable def normMax (A : MatrixGame I J ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (fun i : I => Finset.univ.sup' Finset.univ_nonempty (fun j : J => |A.g i j|))

/-- An **admissible sequence** on a matrix game `A` (Robinson 1951 setup).

Records cumulative counterfactual payoff vectors
`α(t) : J → ℝ` (payoff to playing column `j` against the actual row sequence)
and `β(t) : I → ℝ` (payoff to playing row `i` against the actual column
sequence), together with the row/column choice sequences and the
admissibility conditions:

* `init_bracket` — `min_j α^j(0) = max_i β^i(0)` (the bracket-start condition,
  MFoGT (i)).
* `iSeq_best`, `jSeq_best` — at each step the chosen row is in `argmax β(t)`
  and the chosen column is in `argmin α(t)`.
* `α_step`, `β_step` — the cumulative-payoff update by the chosen pure
  actions, MFoGT (ii).

This is the cumulative-payoff encoding of a fictitious-play realisation; see
`MatrixGame.IsFictitiousPlay` for the empirical-frequency formulation, and
the blueprint node for the correspondence
`α(t)/t = x(t) A`, `β(t)/t = A y(t)` (plus the negligible boundary). -/
structure AdmissibleSequence (A : MatrixGame I J ℝ) where
  α : ℕ → J → ℝ
  β : ℕ → I → ℝ
  iSeq : ℕ → I
  jSeq : ℕ → J
  init_bracket :
    Finset.univ.inf' Finset.univ_nonempty (α 0)
      = Finset.univ.sup' Finset.univ_nonempty (β 0)
  iSeq_best :
    ∀ t i', β t i' ≤ β t (iSeq t)
  jSeq_best :
    ∀ t j', α t (jSeq t) ≤ α t j'
  α_step :
    ∀ t j, α (t + 1) j = α t j + A.g (iSeq t) j
  β_step :
    ∀ t i, β (t + 1) i = β t i + A.g i (jSeq t)

namespace AdmissibleSequence

variable {A : MatrixGame I J ℝ}

/-- Cumulative duality gap `μ(t) := max_i β^i(t) - min_j α^j(t)`. -/
noncomputable def mu (s : AdmissibleSequence A) (t : ℕ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (s.β t)
    - Finset.univ.inf' Finset.univ_nonempty (s.α t)

/-- A pure row `i` is **useful** in the window `[s, s + t*]` if there is a step
inside the window at which `i` is among the row player's argmax choices. -/
def IsRowUsefulInWindow (s : AdmissibleSequence A) (start length : ℕ) (i : I) : Prop :=
  ∃ k, start ≤ k ∧ k < start + length ∧ s.iSeq k = i

/-- A pure column `j` is **useful** in the window `[s, s + t*]` analogously. -/
def IsColUsefulInWindow (s : AdmissibleSequence A) (start length : ℕ) (j : J) : Prop :=
  ∃ k, start ≤ k ∧ k < start + length ∧ s.jSeq k = j

end AdmissibleSequence

end MatrixGame
