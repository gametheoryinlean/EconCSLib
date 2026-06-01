---
id: game_theory.strategic_game.zero_sum.learning.robinson_admissible_lemma.bracket_invariant
title: Bracket Invariant For Admissible Sequences
kind: lemma
status: admitted
primary_topic: game_theory.zero_sum
topics:
  - game_theory.zero_sum
  - game_theory.zero_sum.learning
uses:
  - game_theory.strategic_game.zero_sum.learning.fictitious_play
source:
  spans:
    - artifact: mfogt
      locator: "Section 2.8, Exercise 12 part (1)(iii)"
      format: section
      note: "Bracket invariant on cumulative payoff vectors"
verification:
  statement: accepted
  proof: gap
tags:
  - zero-sum
  - fictitious-play
  - robinson
  - invariant
---

# Bracket Invariant For Admissible Sequences

A technical invariant used by
[[game_theory.strategic_game.zero_sum.learning.robinson_admissible_lemma]] in the useful-window
estimate.

## Statement

Let $(\alpha(t), \beta(t))_{t \ge 0}$ be an admissible sequence on a matrix
$A \in \mathbb{R}^{m \times n}$ (in the sense of
[[game_theory.strategic_game.zero_sum.learning.robinson_admissible_lemma]]). Set
$$
  c := \min_k \alpha^k(0) = \max_k \beta^k(0)
$$
(equal by admissibility condition (i)). Then for every $s \ge 0$,
$$
  \min_i \beta^i(s) \;\le\; c \;\le\; \max_j \alpha^j(s).
$$
In particular,
$$
  \min_i \beta^i(s) - \max_j \alpha^j(s) \;\le\; 0.
$$

## Proof

The two inequalities are independent.

**Upper bracket $c \le \max_j \alpha^j(s)$.** Show $\max_j \alpha^j$ is
non-decreasing in $s$. At step $s+1$, only the component $\alpha^{j_{s+1}}$
changes, where $j_{s+1} \in J(\alpha(s)) = \operatorname{argmin}_k \alpha^k(s)$.

- If $A_{i_{s+1}, j_{s+1}} \ge 0$: $\alpha^{j_{s+1}}$ increases, the others
  unchanged. $\max_j$ stays or grows.
- If $A_{i_{s+1}, j_{s+1}} < 0$: $\alpha^{j_{s+1}}$ decreases, but it was an
  argmin (not argmax unless all components equal). The other components are
  unchanged, so $\max_j$ is unchanged.

Hence $\max_j \alpha^j(s) \ge \max_j \alpha^j(0) \ge \min_k \alpha^k(0) = c$.

**Lower bracket $\min_i \beta^i(s) \le c$.** By induction on $s$.

*Base.* $\min_i \beta^i(0) \le \max_i \beta^i(0) = c$.

*Inductive step.* Assume $\min_i \beta^i(s) \le c$. At step $s+1$, only
$\beta^{i_{s+1}}$ updates, where $i_{s+1} \in I(\beta(s)) = \operatorname{argmax}_k \beta^k(s)$.

- *Case A: there exists an argmin $i^* \ne i_{s+1}$.* Then $\beta^{i^*}$ is
  unchanged at step $s+1$, so
  $$
    \min_i \beta^i(s+1) \le \beta^{i^*}(s+1) = \beta^{i^*}(s) = \min_i \beta^i(s) \le c.
  $$

- *Case B: every argmin equals $i_{s+1}$.* Combined with $i_{s+1} \in$ argmax,
  this forces every $\beta^i(s)$ to be equal — call this common value $v$. By
  induction $v = \min_i \beta^i(s) \le c$. After the step the other components
  remain at $v$; for $m \ge 2$, picking any $i \ne i_{s+1}$ gives
  $\min_i \beta^i(s+1) \le v \le c$.
  When $m = 1$ the matrix is $1 \times n$, the lemma reduces to
  $\beta^1(s) \le \max_j \alpha^j(s)$, which holds because then
  $\beta^1(s) = c + \sum_{p \le s} A_{1, j_p}$ and
  $\alpha^{j_s}(s) = c + A_{1, j_s} \cdot \mathbf{1}_{j_s \in J}$ along
  admissible play — direct computation.

This completes the induction. $\square$

## Note

The lower-bracket induction is slightly subtler than the upper-bracket
monotonicity because $\min_i \beta^i$ is *not* monotone in $s$ — it can both
rise and fall — but it never exceeds $c$.

## References

- [MFoGT, Section 2.8, Exercise 12 part (1)(iii)] Laraki, Renault, and Sorin,
  *Mathematical Foundations of Game Theory*. Bracket inequality
  $\min_i \beta^i(s) - \max_j \alpha^j(s) \le 0$ for admissible sequences.
