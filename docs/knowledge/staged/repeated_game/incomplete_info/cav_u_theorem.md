---
id: game_theory.repeated_game.incomplete_info.cav_u_theorem
title: Aumann-Maschler Cav-u Theorem
kind: theorem
status: staged
primary_topic: game_theory.repeated_game
topics:
  - game_theory.repeated_game
  - game_theory.repeated_game.incomplete_info
uses:
  - game_theory.repeated_game.core.repeated_game
  - game_theory.strategic_game.zero_sum.core.value
verification:
  statement: accepted
  proof: gap
tags:
  - repeated-game
  - incomplete-information
  - zero-sum
  - aumann-maschler
---

# Aumann-Maschler Cav-u Theorem

For a finite zero-sum repeated game with **lack of information on one
side** — only player 1 knows the realised state $k \in K$, drawn once
from a prior $p \in \Delta(K)$ — let $u(p)$ denote the value of the
*nonrevealing* one-shot game at prior $p$.

The Aumann-Maschler theorem (1968, published 1995) says that the values
of the $T$-stage games converge to the concavification of $u$:
$$
v_T(p) \longrightarrow (\operatorname{cav} u)(p) \quad \text{as } T \to \infty.
$$

The same limit is obtained by the discounted-value sequence $v_\gamma$
as $\gamma \to 1$, and equals the uniform value when it exists. In
each case the limit is the smallest concave function dominating $u$ on
$\Delta(K)$.

## Strategic interpretation

The informed player faces a fundamental tradeoff:

- **Pool**: ignore the private information and play a nonrevealing
  strategy; obtain $u(p)$ per stage.
- **Reveal**: split the prior $p$ as a convex combination
  $p = \sum_k \lambda_k p_k$ and play strategy adapted to which
  posterior the play has signalled; this delivers
  $\sum_k \lambda_k u(p_k)$ to the long-run average. Optimisation over
  such splittings gives exactly $\operatorname{cav} u$.

The opponent (uninformed player 2) can prevent doing strictly better
than $\operatorname{cav} u$ by an approachability argument (Blackwell
approachability of a vector-payoff set, see
[[game_theory.strategic_game.zero_sum.approachability.blackwell_b_set_approachability]]).

## Generalizations

- *Lack of information on both sides* (Mertens-Zamir): the limit value
  is characterized as the unique solution to a system of fixed-point
  equations rather than a single concavification. The cav-u theorem
  here is the one-sided special case.
- *Stochastic games with incomplete information*: combines this
  framework with state evolution and is much more delicate.

## References

- Aumann, R. J. and Maschler, M. B. (with the collaboration of Stearns).
  *Repeated Games with Incomplete Information.* MIT Press, 1995.
  (Compiled from 1966-1968 ST reports.)
- Mertens, J.-F. and Zamir, S. (1971). "The Value of Two-Person Zero-Sum
  Repeated Games with Lack of Information on Both Sides".
  *Int. J. Game Theory* 1: 39–64.
- [MFoGT Chapter 8, Thm. 8.6.6] Laraki, Renault, and Sorin,
  *Mathematical Foundations of Game Theory*. Aumann-Maschler cav-u theorem for one-sided incomplete information.
