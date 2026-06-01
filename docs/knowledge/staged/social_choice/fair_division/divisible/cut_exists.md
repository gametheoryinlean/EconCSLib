---
id: social_choice.fair_division.divisible.cut_exists
title: IVT — Cut Point Exists for Non-Atomic Measures on [0,1]
kind: lemma
status: staged
primary_topic: social_choice
topics:
  - social_choice
  - social_choice.fair_division
  - social_choice.fair_division.divisible
  - social_choice.fair_division.divisible.dubins_spanier
uses:
  - social_choice.fair_division.divisible.cdf_continuous
  - social_choice.fair_division.divisible.no_atoms_map_subtype
lean:
  modules:
    - EconCSLib.SocialChoice.FairDivision.Divisible.DubinsSpanier
  declarations:
    - SocialChoice.FairDivision.Divisible.cut_exists
verification:
  statement: accepted
  proof: accepted
  alignment: aligned
tags:
  - fair-division
  - divisible
  - measure
  - intermediate-value-theorem
  - cake-cutting
---

# IVT — Cut Point Exists for Non-Atomic Measures on [0,1]

**Lemma.** Let $\mu$ be a finite non-atomic measure on the unit interval
$I = [0, 1]$. For every target value $0 < c < (\mu(I)).\mathrm{toReal}$,
there exists a cut point $t \in I$ such that
$$
\bigl(\mu([0, t])\bigr).\mathrm{toReal} = c.
$$

In Lean: `SocialChoice.FairDivision.Divisible.cut_exists`.

## Proof sketch

This is the *intermediate value theorem applied to the real-valued CDF*
$$
F(t) = \bigl(\mu([0, t])\bigr).\mathrm{toReal}.
$$

The required ingredients:

1. **Continuity.** $F$ is continuous on $\mathbb{R}$ for finite
   non-atomic measures
   ([[social_choice.fair_division.divisible.cdf_continuous]]). Restricted
   to $I = [0, 1]$ it stays continuous.

2. **Boundary values.** $F(0) = (\mu(\{0\})).\mathrm{toReal} = 0$ by
   non-atomicity, and $F(1) = (\mu(I)).\mathrm{toReal}$.

3. **IVT.** The standard real IVT on $[0, 1]$ yields a $t$ in $I$ with
   $F(t) = c$ for any prescribed $0 < c < F(1)$.

The non-atomic-pushforward instance
[[social_choice.fair_division.divisible.no_atoms_map_subtype]] handles the
type-level conversion between `Measure I` and the real-valued
$\mu.\mathrm{map}\ \mathrm{Subtype.val}$ on $\mathbb{R}$ so that the IVT
applies cleanly.

## Where this is used

This is the *single* measure-theoretic input to the cake-cutting
algorithms in the library:

- Cut-and-choose specializes it at $c = \mu_0(I)/2$ to obtain a fair
  cut ([[social_choice.fair_division.divisible.fair_cut_exists]]).
- Dubins–Spanier specializes it at $c = \mu_i(I)/n$ at each agent in
  the moving-knife step.
- Stromquist uses it implicitly inside the value-continuity argument.

Keeping it as a self-contained lemma means downstream proofs reduce
*directly* to set-existence statements without ever opening
`MeasureTheory.tendsto_*` from inside an algorithm proof.

## References

- Robertson, J. M. and Webb, W. A. (1998). *Cake-Cutting Algorithms*. IVT-on-measures device.
- Dubins, L. E. and Spanier, E. H. (1961). "How to Cut a Cake Fairly". *Amer. Math. Monthly* 68: 1–17.
