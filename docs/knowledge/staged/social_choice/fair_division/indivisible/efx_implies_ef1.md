---
id: social_choice.fair_division.indivisible.efx_implies_ef1
title: EFX ⇒ EF1
kind: theorem
status: staged
primary_topic: social_choice
topics:
  - social_choice
  - social_choice.fair_division
  - social_choice.fair_division.indivisible
uses:
  - social_choice.fair_division.indivisible.efx
  - social_choice.fair_division.indivisible.ef1
lean:
  modules:
    - EconCSLib.SocialChoice.FairDivision.Indivisible.Fairness
  declarations:
    - SocialChoice.FairDivision.Indivisible.IsEFX.isEF1
verification:
  statement: accepted
  proof: accepted
  alignment: aligned
tags:
  - fair-division
  - indivisible
  - efx
  - ef1
---

# EFX ⇒ EF1

**Theorem.** Every EFX allocation
([[social_choice.fair_division.indivisible.efx]]) is EF1
([[social_choice.fair_division.indivisible.ef1]]).

In Lean: `SocialChoice.FairDivision.Indivisible.IsEFX.isEF1`.

## Proof

For agents $i \ne j$ with non-empty $A(j)$, EFX gives the universal
statement $\forall g \in A(j),\ v_i(A(j) \setminus \{g\}) \le v_i(A(i))$.
Picking *any* element $g \in A(j)$ (nonemptiness witnesses the existence)
gives an existential witness for EF1. $\square$

The Lean proof is the obvious one-liner: take the EFX witness for the
first element of the nonempty bundle.

## Significance

This is the easy direction of the EF / EF1 / EFX hierarchy
([[social_choice.fair_division.indivisible.implications]]). The
*non-trivial* direction (EF ⇒ EFX) requires *monotonicity* of the
valuation
([[social_choice.fair_division.indivisible.ef_implies_efx_mono]]).

## References

- [AGT Chapter 11] Nisan, Roughgarden, Tardos, and Vazirani, *Algorithmic Game Theory*. EFX-EF1 implication.
