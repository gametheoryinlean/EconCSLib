/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib

/-!
# EconCSLib.GameTheory.StrategicGame.ESS

Evolutionarily stable strategies (ESS) for symmetric two-player games.

## Main definitions

* `IsESS` — evolutionarily stable strategy [Maynard Smith-Price 1973]
* `IsNSS` — neutrally stable strategy

## Main results

* `ess_implies_nss`
* `strict_nash_implies_ess`
* `ess_is_symmetric_nash` — ESS implies symmetric Nash [MSZ 5.51]
* `ess_isolation` — distinct ESS are strictly separated

## References

* [MSZ] Section 5.6
* Maynard Smith, J. and Price, G.R. (1973). "The Logic of Animal Conflict".
-/

/-! ### Definitions -/

/-- A strategy `s` is an evolutionarily stable strategy (ESS) if:
    1. `u(s,s) ≥ u(t,s)` for all `t` (Nash condition)
    2. If `u(s,s) = u(t,s)` then `u(s,t) > u(t,t)` (invasion barrier)
    [MSZ 5.50] -/
def IsESS {S : Type*} (u : S → S → ℝ) (s : S) : Prop :=
  (∀ t, u s s ≥ u t s) ∧
  (∀ t, u s s = u t s → s ≠ t → u s t > u t t)

/-- A strategy `s` is neutrally stable (NSS) if:
    1. `u(s,s) ≥ u(t,s)` for all `t`
    2. If `u(s,s) = u(t,s)` then `u(s,t) ≥ u(t,t)` -/
def IsNSS {S : Type*} (u : S → S → ℝ) (s : S) : Prop :=
  (∀ t, u s s ≥ u t s) ∧
  (∀ t, u s s = u t s → u s t ≥ u t t)

/-! ### Theorems -/

section ESSTheorems
variable {S : Type*} {u : S → S → ℝ}

/-- Every ESS is neutrally stable. -/
theorem IsESS.isNSS {s : S} (h : IsESS u s) : IsNSS u s := by
  exact ⟨h.1, fun t heq => by
    by_cases hs : s = t
    · subst hs; exact le_refl _
    · exact le_of_lt (h.2 t heq hs)⟩

/-- A strict symmetric Nash equilibrium is automatically ESS. -/
theorem strict_nash_implies_ess {s : S}
    (hstrict : ∀ t, t ≠ s → u s s > u t s) : IsESS u s := by
  refine ⟨fun t => ?_, fun t heq hne => ?_⟩
  · by_cases h : t = s
    · subst h; exact le_refl _
    · exact le_of_lt (hstrict t h)
  · exact absurd heq (ne_of_gt (hstrict t hne.symm))

/-- An ESS satisfies the symmetric Nash condition. [MSZ 5.51] -/
theorem IsESS.nash_condition {s : S} (h : IsESS u s) :
    ∀ t, u s s ≥ u t s := h.1

/-- Distinct ESS are strictly separated: if `s ≠ t` are both ESS,
    then `u(s,s) > u(t,s)`. -/
theorem IsESS.strict_against_other {s t : S}
    (hs : IsESS u s) (ht : IsESS u t) (hne : s ≠ t) :
    u s s > u t s := by
  have hge := hs.1 t
  by_contra h
  push_neg at h
  have heq : u s s = u t s := le_antisymm h hge
  have hstab := hs.2 t heq hne
  linarith [ht.1 s]

end ESSTheorems
