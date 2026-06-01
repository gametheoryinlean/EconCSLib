---
id: social_choice.fair_division.divisible.measure_instance_ef_iff_real
title: Measure-Instance EF ↔ Real-Valued Cardinal EF
kind: theorem
status: staged
primary_topic: social_choice
topics:
  - social_choice
  - social_choice.fair_division
  - social_choice.fair_division.divisible
uses:
  - social_choice.fair_division.divisible.measure_instance
lean:
  modules:
    - EconCSLib.SocialChoice.FairDivision.Divisible.Instance
  declarations:
    - SocialChoice.FairDivision.Divisible.MeasureInstance.isEnvyFree_iff_toCardinalInstance_isEnvyFree
verification:
  statement: accepted
  proof: accepted
  alignment: aligned
tags:
  - fair-division
  - divisible
  - measure
  - envy-free
---

# Measure-Instance EF ↔ Real-Valued Cardinal EF

**Theorem.** For a divisible measure instance
$I : \mathrm{MeasureInstance}\ N\ \Omega$
([[social_choice.fair_division.divisible.measure_instance]]) with every
$I.\mathrm{measure}\ i$ finite, and any allocation $A$, the
$\mathrm{ENNReal}$-valued envy-freeness predicate agrees with the
real-valued cardinal envy-freeness obtained from $.toCardinalInstance$:
$$
I.\mathrm{IsEnvyFree}\ A \;\iff\; (I.\mathrm{toCardinalInstance}).\mathrm{IsEnvyFree}\ A.
$$

In Lean:
`SocialChoice.FairDivision.Divisible.MeasureInstance.isEnvyFree_iff_toCardinalInstance_isEnvyFree`.

## Proof

The two predicates compare values of the form $\mu_i(A(j))$ vs
$\mu_i(A(i))$:

- The $\mathrm{ENNReal}$ form compares directly:
  $\mu_i(A(j)) \le \mu_i(A(i))$ in $\mathrm{ENNReal}$.
- The real form compares after `.toReal`:
  $(\mu_i(A(j))).\mathrm{toReal} \le (\mu_i(A(i))).\mathrm{toReal}$.

Both quantities are finite (`[IsFiniteMeasure (I.measure i)]`) so
`measure_ne_top` lets `ENNReal.toReal_le_toReal` translate between the
two forms. Each direction of the iff is a short calculation.

## Why this matters

`MeasureInstance` is the natural input for measure-theoretic algorithms
(cut-and-choose, Dubins–Spanier, Stromquist), which all reason with
$\mathrm{ENNReal}$-valued measures. But the bundled real-valued cardinal
interface
([[social_choice.fair_division.divisible.cardinal_instance]]) is what
downstream call sites prefer (algebra over $\mathbb{R}$ is much easier
than over $\mathrm{ENNReal}$).

This equivalence lets a single theorem stated against either form
discharge both — pick the convenient one when authoring, then convert
at the boundary.

## References

- [AGT Chapter 13] Nisan, Roughgarden, Tardos, and Vazirani, *Algorithmic Game Theory*.
