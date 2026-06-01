---
id: game_theory.strategic_game.zero_sum.learning.robinson_admissible_lemma.induction_step
title: Euclidean Division Pasting In Robinson Induction
kind: lemma
status: admitted
primary_topic: game_theory.zero_sum
topics:
  - game_theory.zero_sum
  - game_theory.zero_sum.learning
uses:
  - game_theory.strategic_game.zero_sum.learning.robinson_admissible_lemma.useful_window
  - game_theory.strategic_game.zero_sum.learning.robinson_admissible_lemma.subgame_reduction
source:
  spans:
    - artifact: mfogt
      locator: "Section 2.8, Exercise 12 parts (3)(c) and (3)(d)"
      format: section
      note: "Euclidean-division pasting to bound mu(t) by epsilon*t for large t"
verification:
  statement: accepted
  proof: gap
tags:
  - zero-sum
  - fictitious-play
  - robinson
---

# Euclidean Division Pasting In Robinson Induction

The arithmetic pasting step that closes the inductive proof of
[[game_theory.strategic_game.zero_sum.learning.robinson_admissible_lemma]] by combining the two
window-dichotomy cases over $t = q t^* + r$.

## Setup

Let $A \in \mathbb{R}^{m \times n}$ with $\|A\| := \max_{i,j} |A_{i,j}|$.
Suppose $t^* \in \mathbb{N}$ is such that, for every window $[s, s+t^*]$ of
length $t^*$ along an admissible sequence on $A$, exactly one of the
following holds:

- **(a)** every $i \in I$ and every $j \in J$ is useful in $[s, s+t^*]$;
- **(b)** at least one of them is not.

Suppose further that
- in case (a), [[game_theory.strategic_game.zero_sum.learning.robinson_admissible_lemma.useful_window]]
  gives $\mu(s+t^*) \le 4 t^* \|A\|$ (an *absolute* bound on the endpoint);
- in case (b), [[game_theory.strategic_game.zero_sum.learning.robinson_admissible_lemma.subgame_reduction]]
  combined with the inductive hypothesis on a strict submatrix gives
  $\mu(s+t^*) - \mu(s) \le \frac{\varepsilon t^*}{2} + 2 \|A\|$ (an *increment*
  bound).

## Statement

Under the above setup, for every $t \ge t^*$,
$$
  \mu(t) \;\le\; 6 t^* \|A\| + \frac{\varepsilon t}{2} + \frac{2 \|A\| t}{t^*}.
$$
Consequently, if $t^*$ is chosen so that $2\|A\|/t^* \le \varepsilon/2$, then
for all $t \ge s_0 := \max\!(t^*, 12 t^* \|A\| / \varepsilon)$,
$$
  \mu(t) \;\le\; \frac{3 \varepsilon}{2} t.
$$
Re-running the argument with $\varepsilon$ replaced by $2\varepsilon/3$
gives the form $\mu(t) \le \varepsilon t$ used in the parent lemma.

## Proof

Write $t = q t^* + r$ with $0 \le r < t^*$. The trajectory $[0, t]$ is
decomposed into $q$ consecutive windows of length $t^*$ plus a residual
window of length $r$.

Single-step bound on $\mu$. Each admissible step changes $\mu$ by at most
$2 \|A\|$ (each of $\max_i \beta^i$ and $\min_j \alpha^j$ changes by at most
$\|A\|$). Hence on the residual $r < t^*$,
$$
  \mu(t) - \mu(q t^*) \;\le\; 2 r \|A\| \;\le\; 2 t^* \|A\|.
$$

Let
$$
  p := \max \{ k \in \{0, 1, \ldots, q-1\} : \text{window } [k t^*, (k+1) t^*]
    \text{ is in case (a)} \},
$$
with the convention $p = -1$ if no window is in case (a).

- *If $p \ge 0$:* the case-(a) bound resets $\mu$ at the endpoint:
  $\mu((p+1) t^*) \le 4 t^* \|A\|$. From there, the remaining $q - p - 1$
  windows are all in case (b), each contributing increment
  $\frac{\varepsilon t^*}{2} + 2 \|A\|$. Summing,
  $$
    \mu(q t^*) \;\le\; 4 t^* \|A\|
      + (q - p - 1)\!\left(\frac{\varepsilon t^*}{2} + 2 \|A\|\right).
  $$
- *If $p = -1$:* every window is in case (b). The cumulative bound is then
  $\mu(0) + q (\frac{\varepsilon t^*}{2} + 2\|A\|)$, with $\mu(0) \le 2\|A\|$
  by admissibility condition (i). So
  $$
    \mu(q t^*) \;\le\; 2 \|A\| + q\!\left(\frac{\varepsilon t^*}{2} + 2 \|A\|\right).
  $$

In both branches, using $q - p - 1 \le q \le t/t^*$ and $2 \|A\| \le 2 t^* \|A\|$:
$$
  \mu(q t^*) \;\le\; 4 t^* \|A\| + \frac{\varepsilon t}{2} + 2 \|A\| \cdot \frac{t}{t^*}.
$$
Adding the residual contribution $\mu(t) - \mu(q t^*) \le 2 t^* \|A\|$:
$$
  \mu(t) \;\le\; 6 t^* \|A\| + \frac{\varepsilon t}{2} + \frac{2 \|A\| t}{t^*}.
$$

For the second form, with $t^* \ge 4\|A\|/\varepsilon$ the last term is
$\le \varepsilon t / 2$, giving $\mu(t) \le 6 t^* \|A\| + \varepsilon t$. The
dominant first term is $\le \varepsilon t / 2$ when
$t \ge 12 t^* \|A\| / \varepsilon$, and combining yields the
$\frac{3\varepsilon}{2} t$ bound. $\square$

## Note

The proof is purely arithmetic given the two case bounds and the single-step
$2\|A\|$ inequality. The hierarchy of constants ($6 t^* \|A\|$ absolute,
$\varepsilon t / 2$ linear, $2 \|A\| t / t^*$ from the last-term residual) is
designed so that each term is either absolutely bounded or absorbable into
$\varepsilon t$ for sufficiently large $t^*$ or $t$.

## References

- [MFoGT, Section 2.8, Exercise 12 parts (3)(c) and (3)(d)] Laraki, Renault,
  and Sorin, *Mathematical Foundations of Game Theory*. Euclidean-division pasting in
  Robinson's induction.
