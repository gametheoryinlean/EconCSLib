---
id: social_choice.fair_division.divisible.ef_exists
title: Envy-Free Existence (Stromquist, n Agents)
kind: theorem
status: staged
primary_topic: social_choice
topics:
  - social_choice
  - social_choice.fair_division
  - social_choice.fair_division.divisible
  - social_choice.fair_division.divisible.stromquist
uses:
  - social_choice.fair_division.divisible.stromquist_unusual_case
lean:
  modules:
    - EconCSLib.SocialChoice.FairDivision.Divisible.Existence
  declarations:
    - SocialChoice.FairDivision.Divisible.ef_exists
verification:
  statement: accepted
  proof: accepted
  alignment: aligned
tags:
  - fair-division
  - divisible
  - stromquist
  - envy-free
  - existence
---

# Envy-Free Existence (Stromquist, n Agents)

**Theorem (Stromquist 1980).** For every $n \ge 1$ and every family of
finite non-atomic measures $\mu : \mathrm{Fin}\ n \to \mathrm{Measure}\ I$
on the unit interval $I = [0, 1]$, there exists a complete measurable
partition $A : \mathrm{Fin}\ n \to \mathrm{Set}\ I$ that is envy-free
under the measure valuation $\mathrm{MeasureValuation}\ \mu$
([[social_choice.fair_division.divisible.envy_free]]).

In Lean: `SocialChoice.FairDivision.Divisible.ef_exists`.

## Proof

Case split on whether the agent-preference unions
$\{U(i)\}_i$ cover the division simplex
([[social_choice.fair_division.divisible.stromquist_U]]):

- **Usual case.** $\{U(i)\}_i$ covers $S$. Apply
  [[social_choice.fair_division.divisible.stromquist_usual_case]] —
  KKM yields a common point with a unique-preference bijection, and
  [[social_choice.fair_division.divisible.stromquist_assignment]]
  converts the bijection into an EF allocation.

- **Unusual case.** $\{U(i)\}_i$ does not cover $S$. Apply
  [[social_choice.fair_division.divisible.stromquist_unusual_case]] —
  the shifted-cell refinement
  ([[social_choice.fair_division.divisible.stromquist_shifted_cells]])
  produces approximate fair divisions whose limit is fair for the
  original measures.

In both cases the output is a *contiguous* EF allocation (each agent
receives a single interval).

## Significance

This is the high point of the divisible-fair-division formalization:

- Compared to cut-and-choose
  ([[social_choice.fair_division.divisible.cut_and_choose_ef_exists]])
  it works for *any* number of agents, not just two.
- Compared to Dubins–Spanier
  ([[social_choice.fair_division.divisible.dubins_spanier_proportional]])
  it gives EF, not merely PROP.
- The proof is *non-constructive*: KKM (and Brouwer / Sperner) are not
  algorithmic, so the EF allocation is shown to exist without an
  explicit construction.

The combined EF + PROP existence statement is
[[social_choice.fair_division.divisible.ef_exists_and_proportional]].

## References

- Stromquist, W. (1980). "How to Cut a Cake Fairly". *Amer. Math. Monthly* 87: 640–644.
- Su, F. E. (1999). "Rental Harmony: Sperner's Lemma in Fair Division". *Amer. Math. Monthly* 106.
- [AGT Chapter 13] Nisan, Roughgarden, Tardos, and Vazirani, *Algorithmic Game Theory*.
