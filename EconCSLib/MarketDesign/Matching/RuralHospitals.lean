/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.MarketDesign.Matching.GaleShapley

/-!
# EconCSLib.MarketDesign.Matching.RuralHospitals

Rural Hospitals theorem, specialized to the **balanced full-preference**
one-to-one market (`Preferences n` via `MatchingMarket.ofEquivData`).

In that model every agent is acceptable to every other and `|M| = |W| = n`,
so the general statement ("the set of matched participants is the same in
every stable matching") collapses to: **every stable matching is perfect** —
all `n` women and all `n` men are matched. Hence the matched set is the whole
of `Fin n` in *every* stable matching, trivially invariant across them.

## Main result

* `GS.stable_matching_perfect` — every stable matching on
  `MatchingMarket.ofEquivData w m` matches every agent on both sides.

## Proof

If some woman were unmatched, then `matchW` (men → women) cannot be total:
were it total it would be an injection `Fin n → Fin n`, hence a bijection,
forcing the unmatched woman to be someone's partner. So some man is also
unmatched — and an unmatched woman together with an unmatched man form a
blocking pair (each strictly prefers any partner to staying single, since
`none` is the least-preferred option), contradicting stability. The man side
is symmetric, using totality of `matchM`.

## References

* [MSZ Theorem 22.14] Maschler, Solan, Zamir, *Game Theory*, §22.
* Roth (1986); McVitie–Wilson (1970).
-/

open GS

namespace GS

variable {n : ℕ} (w m : Preferences n)

/-- In the balanced full-preference one-to-one market, every stable matching is
**perfect**: every woman and every man is matched. This is the
Rural-Hospitals specialization — the matched set is all of `Fin n` in every
stable matching, hence invariant across the stable set. -/
theorem stable_matching_perfect
    (μ : Matching (Fin n) (Fin n))
    (hμ : Matching.IsStable (MatchingMarket.ofEquivData w m) μ) :
    (∀ i : Fin n, (μ.matchM i).isSome) ∧ (∀ j : Fin n, (μ.matchW j).isSome) := by
  -- Every woman is matched.
  have hwomen : ∀ i : Fin n, (μ.matchM i).isSome := by
    intro i₀
    by_contra hi0
    rw [Option.not_isSome_iff_eq_none] at hi0
    -- Some man is unmatched, else `matchW` is a total injection (hence a
    -- bijection) and would force `i₀` to be matched.
    obtain ⟨j₀, hj0⟩ : ∃ j : Fin n, μ.matchW j = none := by
      by_contra hall
      push Not at hall
      have hsome : ∀ j, (μ.matchW j).isSome := fun j =>
        Option.isSome_iff_ne_none.mpr (hall j)
      set f : Fin n → Fin n := fun j => (μ.matchW j).get (hsome j) with hf
      have hf_spec : ∀ j, μ.matchW j = some (f j) := fun j =>
        (Option.some_get (hsome j)).symm
      have hf_inj : Function.Injective f := by
        intro j1 j2 he
        have e1 := (μ.consistent (f j1) j1).mpr (hf_spec j1)
        have e2 := (μ.consistent (f j2) j2).mpr (hf_spec j2)
        rw [he] at e1; rw [e2] at e1
        exact (Option.some.inj e1).symm
      obtain ⟨j, hj⟩ := (Finite.injective_iff_bijective.mp hf_inj).2 i₀
      have hcon : μ.matchM i₀ = some j := (μ.consistent i₀ j).mpr (hj ▸ hf_spec j)
      rw [hi0] at hcon
      simp at hcon
    -- `(i₀, j₀)` blocks: both are unmatched and `some _ ≻ none`.
    exact hμ i₀ j₀ ⟨by rw [hi0]; exact ⟨trivial, not_false⟩,
                    by rw [hj0]; exact ⟨trivial, not_false⟩⟩
  -- Every man is matched (symmetric: `matchM` is now a total injection).
  refine ⟨hwomen, fun j₀ => ?_⟩
  by_contra hj0
  rw [Option.not_isSome_iff_eq_none] at hj0
  set g : Fin n → Fin n := fun i => (μ.matchM i).get (hwomen i) with hg
  have hg_spec : ∀ i, μ.matchM i = some (g i) := fun i =>
    (Option.some_get (hwomen i)).symm
  have hg_inj : Function.Injective g := by
    intro i1 i2 he
    have e1 := (μ.consistent i1 (g i1)).mp (hg_spec i1)
    have e2 := (μ.consistent i2 (g i2)).mp (hg_spec i2)
    rw [he] at e1; rw [e2] at e1
    exact (Option.some.inj e1).symm
  obtain ⟨i, hi⟩ := (Finite.injective_iff_bijective.mp hg_inj).2 j₀
  have hcon : μ.matchW j₀ = some i := (μ.consistent i j₀).mp (hi ▸ hg_spec i)
  rw [hj0] at hcon
  simp at hcon

end GS
