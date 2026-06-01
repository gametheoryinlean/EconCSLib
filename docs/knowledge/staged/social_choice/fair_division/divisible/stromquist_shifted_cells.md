---
id: social_choice.fair_division.divisible.stromquist_shifted_cells
title: Stromquist Shifted-Cell Approximation
kind: definition
status: staged
primary_topic: social_choice
topics:
  - social_choice
  - social_choice.fair_division
  - social_choice.fair_division.divisible
  - social_choice.fair_division.divisible.stromquist
uses:
  - social_choice.fair_division.divisible.stromquist_U
lean:
  modules:
    - EconCSLib.SocialChoice.FairDivision.Divisible.Existence
verification:
  definition: accepted
  proof: accepted
  alignment: aligned
tags:
  - fair-division
  - divisible
  - stromquist
  - kkm
  - approximation
---

# Stromquist Shifted-Cell Approximation

The "unusual case" of Stromquist's proof arises when the preference
unions $\{U(i)\}_i$ do not cover the simplex
([[social_choice.fair_division.divisible.stromquist_U]]); concretely,
some divisions $x$ have every agent indifferent between two or more
pieces, so no agent *uniquely* prefers any piece at $x$.

The fix is *perturbation by an irrational shift*. The Lean source
follows the original Stromquist construction:

## Open cell decomposition

Pick a positive integer $M$ (the *grid scale*) and a tuple of shifts
$\alpha = (\alpha_0, \dots, \alpha_{n-1}) \in \mathbb{R}^n$. For each
agent $j$ and each integer-coordinate $p \in \mathbb{Z}^{n}$, define the
*open shifted cell*
$$
C_M(\alpha, p, j) \;=\; \{x \in S \mid \forall k,\ x_k \in [\,p_k/M + \alpha_j,\ (p_k+1)/M + \alpha_j\,)\}.
$$

The cell *hits* piece $i$ for agent $j$ if its intersection with the
simplex meets the preference set $A(i, j)$
([[social_choice.fair_division.divisible.stromquist_preference_sets]]).
The *owner* of a cell is the smallest piece index $i$ whose preference
set $A(i, j)$ meets the cell.

## Approximate preference and union sets

- `strom_A' M α i j` — approximate preference set: assign each open cell
  to its owner for agent $j$, then collect cells owned by piece $i$.
- `strom_U' M α i` — approximate agent-preference union for piece $i$.

## Why this fixes the unusual case

Two technical ingredients:

1. **Cover lemma.** If the shifts $\alpha_0, \dots, \alpha_{n-1}$ have
   pairwise irrational differences (a generic condition), the shifted
   cells' boundaries avoid the agent-$j$ indifference hyperplanes for
   every agent simultaneously. The resulting $\{U'(i)\}_i$ then *does*
   cover the simplex.

2. **Existence of suitable shifts.** Such irrational-difference shifts
   exist (a Baire-category / cardinality argument on $\mathbb{R}^n$).

With the perturbed $U'$ covering $S$, the usual-case KKM argument
([[social_choice.fair_division.divisible.stromquist_usual_case]])
produces a fair division for the *approximate* preferences.

## Limit passage

Two simplex points in the same shifted cell are uniformly close
(diameter $\le \sqrt{n}/M$). Letting $M \to \infty$, the sequence of
approximate fair divisions has a convergent subsequence by compactness
of the simplex, and the limit is a fair division for the *original*
preferences. This is closed in
[[social_choice.fair_division.divisible.stromquist_unusual_case]].

## References

- Stromquist, W. (1980). "How to Cut a Cake Fairly". *Amer. Math. Monthly* 87: 640–644.
