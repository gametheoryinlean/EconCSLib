---
id: game_theory.strategic_game.zero_sum.learning.robinson_admissible_lemma.useful_window
title: Useful Window Bound For Admissible Sequences
kind: lemma
status: admitted
primary_topic: game_theory.zero_sum
topics:
  - game_theory.zero_sum
  - game_theory.zero_sum.learning
uses:
  - game_theory.strategic_game.zero_sum.learning.robinson_admissible_lemma.bracket_invariant
source:
  spans:
    - artifact: mfogt
      locator: "Section 2.8, Exercise 12 parts (2)(iv) and (2)(v)"
      format: section
      note: "Useful-interval geometric collapse of cumulative payoff spread"
verification:
  statement: accepted
  proof: gap
tags:
  - zero-sum
  - fictitious-play
  - robinson
---

# Useful Window Bound For Admissible Sequences

A geometric collapse estimate used by
[[game_theory.strategic_game.zero_sum.learning.robinson_admissible_lemma]] inside the main
induction's "all rows/columns useful" case.

## Setup

For an admissible sequence on $A \in \mathbb{R}^{m \times n}$, an index
$i \in I$ is **useful** in the window $[t_1, t_2] \subseteq \mathbb{N}$ if
$$
  \exists t \in [t_1, t_2] : i \in I(\beta(t)) = \operatorname{argmax}_k \beta^k(t).
$$
That is, $i$ is selected as a best response at some moment in the window.
Symmetrically for $j \in J$ via $J(\alpha(t))$.

## Statement

Let $\|A\| := \max_{i,j} |A_{i,j}|$.

**(iv)** If every $j \in J$ is useful in $[s, s+t]$ then
$$
  \max_j \alpha^j(s+t) - \min_j \alpha^j(s+t) \;\le\; 2t \|A\|.
$$
Symmetrically, if every $i \in I$ is useful in $[s, s+t]$ then
$\max_i \beta^i(s+t) - \min_i \beta^i(s+t) \le 2t\|A\|$.

**(v)** If every $i \in I$ and every $j \in J$ is useful in $[s, s+t]$ then
$$
  \mu(s+t) \;\le\; 4 t \|A\|,
$$
where $\mu := \max_i \beta^i - \min_j \alpha^j$.

## Proof

**(iv).** Fix indices $j_1, j_2 \in J$. By hypothesis $j_2$ is useful: pick
$\tau \in [s, s+t]$ with $j_2 \in J(\alpha(\tau))$, so
$\alpha^{j_2}(\tau) = \min_k \alpha^k(\tau) \le \alpha^{j_1}(\tau)$.

Along admissible evolution, each component of $\alpha$ changes by at most
$\|A\|$ per step (only the argmin component updates, with increment
$A_{i_{\tau+1}, j_{\tau+1}}$ of magnitude $\le \|A\|$). In particular
$$
  |\alpha^{j_k}(s+t) - \alpha^{j_k}(\tau)| \le (s+t-\tau)\|A\| \le t\|A\|,
  \quad k = 1, 2.
$$
Combining,
$$
  \alpha^{j_2}(s+t) - \alpha^{j_1}(s+t)
   \le [\alpha^{j_2}(\tau) - \alpha^{j_1}(\tau)] + 2t\|A\| \le 2t\|A\|.
$$
Taking maximum over $j_2$ and minimum over $j_1$ gives the result.

The symmetric statement for $\beta$ is identical with $J(\alpha)$ replaced by
$I(\beta)$ and roles swapped.

**(v).** From (iv) and its dual:
$$
  \max_j \alpha^j(s+t) - \min_j \alpha^j(s+t) \le 2t\|A\|, \quad
  \max_i \beta^i(s+t) - \min_i \beta^i(s+t) \le 2t\|A\|.
$$
Adding:
$$
  [\max_i \beta^i - \min_i \beta^i](s+t)
  + [\max_j \alpha^j - \min_j \alpha^j](s+t)
  \le 4t\|A\|.
$$
Rewriting and inserting the bracket invariant
[[game_theory.strategic_game.zero_sum.learning.robinson_admissible_lemma.bracket_invariant]]
($\min_i \beta^i(s+t) \le \max_j \alpha^j(s+t)$):
$$
  \mu(s+t) + [\max_j \alpha^j(s+t) - \min_i \beta^i(s+t)] \le 4t\|A\|.
$$
The bracket invariant makes the second bracketed term non-negative, so
$\mu(s+t) \le 4t\|A\|$. $\square$

## Note

The bound is *absolute* — it does not depend on $\mu(s)$. This is the
mechanism by which the main induction "resets" the cumulative gap once a
window of full usefulness has been traversed.

## References

- [MFoGT, Section 2.8, Exercise 12 parts (2)(iv) and (2)(v)] Laraki, Renault,
  and Sorin, *Mathematical Foundations of Game Theory*. Useful-window collapse and
  combined $\mu$ bound.
