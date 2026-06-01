---
id: social_choice.fair_division.divisible.stromquist_unusual_case
title: Stromquist — Unusual Case (Shifted-Cell Limit)
kind: theorem
status: staged
primary_topic: social_choice
topics:
  - social_choice
  - social_choice.fair_division
  - social_choice.fair_division.divisible
  - social_choice.fair_division.divisible.stromquist
uses:
  - social_choice.fair_division.divisible.stromquist_shifted_cells
  - social_choice.fair_division.divisible.stromquist_usual_case
lean:
  modules:
    - EconCSLib.SocialChoice.FairDivision.Divisible.Existence
  declarations:
    - SocialChoice.FairDivision.Divisible.strom_unusual_case
verification:
  statement: accepted
  proof: accepted
  alignment: aligned
tags:
  - fair-division
  - divisible
  - stromquist
  - envy-free
  - approximation
---

# Stromquist — Unusual Case (Shifted-Cell Limit)

**Theorem (unusual case).** When the agent-preference unions
$\{U(i)\}_i$ do not cover the simplex
([[social_choice.fair_division.divisible.stromquist_U]]), there is still
a complete measurable envy-free allocation.

The construction is the shifted-cell refinement
([[social_choice.fair_division.divisible.stromquist_shifted_cells]])
followed by a limit-passage argument.

## Proof

1. **Build approximate fair divisions.** Pick shifts $\alpha$ with
   pairwise irrational differences. For each grid scale $M$, the
   perturbed preference unions $\{U'_M(i)\}_i$ cover the simplex (the
   irrationality keeps the cells from straddling indifference
   hyperplanes). Apply the usual-case theorem
   ([[social_choice.fair_division.divisible.stromquist_usual_case]]) to
   obtain a simplex point $x^*_M$ and a corresponding fair division
   $A_M$ for the perturbed data.

2. **Compactness.** The sequence $(x^*_M)_M$ lies in the compact
   simplex $S$, so it has a convergent subsequence with limit
   $x^*_\infty \in S$.

3. **Limit is fair.** Two simplex points in the same shifted cell are
   within $\sqrt{n}/M$ in the sup norm, so $A_M \to A_\infty$ in the
   appropriate sense, and continuity of the piece-value function
   ([[social_choice.fair_division.divisible.stromquist_value_continuous]])
   carries EF through the limit: the EF inequality
   $\mu_i(A_\infty(j)) \le \mu_i(A_\infty(i))$ is the limit of the
   approximate EF inequalities for $A_M$.

The output is a contiguous envy-free allocation for the *original*
measures.

## Role in the overall proof

Combining the usual-case theorem
([[social_choice.fair_division.divisible.stromquist_usual_case]]) and
this unusual-case theorem covers both regimes, closing the EF existence
result for arbitrary $n$ agents
([[social_choice.fair_division.divisible.ef_exists]]).

## References

- Stromquist, W. (1980). "How to Cut a Cake Fairly". *Amer. Math. Monthly* 87: 640–644.
