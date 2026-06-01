---
id: social_choice.fair_division.divisible.cdf_continuous
title: CDF of a Non-Atomic Finite Measure on ℝ Is Continuous
kind: lemma
status: staged
primary_topic: social_choice
topics:
  - social_choice
  - social_choice.fair_division
  - social_choice.fair_division.divisible
uses: []
lean:
  modules:
    - EconCSLib.SocialChoice.FairDivision.Divisible.UnitInterval
  declarations:
    - SocialChoice.FairDivision.Divisible.cdfRealContinuous
verification:
  statement: accepted
  proof: accepted
  alignment: aligned
tags:
  - fair-division
  - divisible
  - measure
  - cake-cutting
---

# CDF of a Non-Atomic Finite Measure on ℝ Is Continuous

**Lemma.** Let $\nu$ be a finite non-atomic measure on $\mathbb{R}$. The
real-valued CDF
$$
F : \mathbb{R} \to \mathbb{R}, \qquad F(t) = \nu\bigl((-\infty, t]\bigr).\mathrm{toReal}
$$
is continuous.

In Lean: `SocialChoice.FairDivision.Divisible.cdfRealContinuous`. The
argument shows continuity from the left and from the right separately
using the monotonicity of $F$.

## Proof sketch

- *Monotonicity.* $F$ is monotone because $t \le s$ implies
  $(-\infty, t] \subseteq (-\infty, s]$, and `measure_mono` plus
  `ENNReal.toReal_le_toReal` give $F(t) \le F(s)$ (both measures are
  finite).
- *Right-continuity.* Apply `tendsto_measure_biInter_gt` to the
  decreasing family $\{(-\infty, r] : r > a\}$; its intersection is
  $(-\infty, a]$, and `ENNReal.continuousAt_toReal` finishes the
  reduction back to the real CDF.
- *Left-continuity.* This is where non-atomicity enters. Pick a strictly
  increasing sequence $u_n \uparrow a$ in $(-\infty, a)$. Its union
  satisfies $\bigcup_n (-\infty, u_n] = (-\infty, a)$, and
  `tendsto_measure_iUnion_atTop` plus `Iio_ae_eq_Iic` (which depends on
  non-atomicity to identify $(-\infty, a)$ and $(-\infty, a]$ up to
  $\nu$-null sets) closes the left limit equality.

The combination of left- and right-continuity yields continuity at every
$a \in \mathbb{R}$, hence everywhere.

## Where this is used

This is the IVT-input for cake-cutting: it lets `cut_exists`
([[social_choice.fair_division.divisible.cut_exists]]) build a cut point
$t$ with $\nu((-\infty, t]) = c$ for any prescribed $0 < c < \nu(\mathbb{R})$
on the unit interval — exactly what cut-and-choose, Dubins–Spanier, and
Stromquist all need.

## References

- Robertson, J. M. and Webb, W. A. (1998). *Cake-Cutting Algorithms*. Continuity of fair-cut-cumulative functions.
