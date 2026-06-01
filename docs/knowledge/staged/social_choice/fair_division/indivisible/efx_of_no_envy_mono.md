---
id: social_choice.fair_division.indivisible.efx_of_no_envy_mono
title: EFX from No-Envy + Monotonicity
kind: theorem
status: staged
primary_topic: social_choice
topics:
  - social_choice
  - social_choice.fair_division
  - social_choice.fair_division.indivisible
uses:
  - social_choice.fair_division.indivisible.ef_implies_efx_mono
lean:
  modules:
    - EconCSLib.SocialChoice.FairDivision.Indivisible.EFX
  declarations:
    - SocialChoice.FairDivision.Indivisible.IsEFX.of_noEnvy_mono
verification:
  statement: accepted
  proof: accepted
  alignment: aligned
tags:
  - fair-division
  - indivisible
  - efx
  - monotonicity
---

# EFX from No-Envy + Monotonicity

**Theorem.** For a monotone valuation $v$ on indivisible goods,
envy-freeness ([[social_choice.fair_division.indivisible.envy_free]])
implies EFX ([[social_choice.fair_division.indivisible.efx]]).

In Lean: `SocialChoice.FairDivision.Indivisible.IsEFX.of_noEnvy_mono`.

## Statement and proof

This is the same content as
[[social_choice.fair_division.indivisible.ef_implies_efx_mono]], stated
inside `EFX.lean` as a local sufficiency lemma for the EFX existence
proofs in the same file. The Lean signatures differ only in how the
hypothesis is bundled:

- `IsEnvyFree.isEFX_of_mono` in `Fairness.lean` — phrased as a method
  on the EF predicate.
- `IsEFX.of_noEnvy_mono` in `EFX.lean` — phrased as a constructor of
  the EFX predicate.

Both prove $T \subseteq S \Rightarrow v_i(T) \le v_i(S)$, combined with
EF, yields EFX, by the same calculation: removing an item from the
envied bundle (a subset operation) only decreases its value, so the EF
inequality $v_i(A(j)) \le v_i(A(i))$ propagates to bundles missing one
item.

## Why duplicate

Having both forms lets `EFX.lean` use the constructor directly without
importing the symmetric `Fairness`-side lemma. It is purely an
organisational convenience; the proof is the same.

## References

- [AGT Chapter 11] Nisan, Roughgarden, Tardos, and Vazirani, *Algorithmic Game Theory*. EF-EFX implication.
