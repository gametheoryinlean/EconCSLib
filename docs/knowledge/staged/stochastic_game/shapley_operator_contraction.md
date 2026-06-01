---
id: game_theory.stochastic_game.value.shapley_operator_contraction
title: Shapley Operator Is a γ-Contraction
kind: theorem
status: staged
primary_topic: game_theory.stochastic_game
topics:
  - game_theory.stochastic_game
  - game_theory.stochastic_game.value
uses:
  - game_theory.stochastic_game.value.shapley_operator
  - game_theory.strategic_game.zero_sum.operators.value_operator_nonexpansive_general
verification:
  statement: accepted
  proof: accepted
tags:
  - stochastic-game
  - zero-sum
  - shapley-operator
  - contraction
---

# Shapley Operator Is a γ-Contraction

**Theorem.** For any discount factor $\gamma \in (0, 1)$, the Shapley
operator $T_\gamma$ ([[game_theory.stochastic_game.value.shapley_operator]]) is a
$\gamma$-contraction on $L^\infty(S)$ in the supremum norm:
$$
\|T_\gamma f - T_\gamma g\|_\infty \;\le\; \gamma\, \|f - g\|_\infty.
$$

## Proof

Pin a state $s$ and a pair of functions $f, g$. The defining
$\operatorname{val}$ at $s$ uses matrix-game entries
$$
M_f(a_1, a_2) = (1 - \gamma) r(s, a_1, a_2) + \gamma\, (q f)(s, a_1, a_2),
$$
where $(qf)(s, a_1, a_2) = \sum_{s'} q(s'|s, a_1, a_2)\, f(s')$ is the
linear continuation operator applied to $f$.

Subtracting:
$$
M_f(a_1, a_2) - M_g(a_1, a_2) = \gamma\, (q (f - g))(s, a_1, a_2).
$$

Because $q$ is a probability kernel (row sums to 1, non-negative
entries), $|q(f-g)| \le \|f - g\|_\infty$ pointwise. Hence
$|M_f - M_g| \le \gamma \|f - g\|_\infty$ entry-wise.

The value operator $\operatorname{val}$ on matrix games is
1-Lipschitz in the supremum norm of the matrix entries (a standard
consequence of zero-sum saddle-point characterisation; see
[[game_theory.strategic_game.zero_sum.operators.value_operator_nonexpansive_general]] for the
abstract version). Therefore
$$
|(T_\gamma f)(s) - (T_\gamma g)(s)|
  = |\operatorname{val}(M_f) - \operatorname{val}(M_g)|
  \le \|M_f - M_g\|_\infty
  \le \gamma\, \|f - g\|_\infty.
$$

Taking the supremum over $s \in S$ gives the claim. $\square$

## Consequence

By Banach's fixed-point theorem (any complete metric space, here
$L^\infty(S)$ with sup norm and $S$ finite, $L^\infty(S) = \mathbb{R}^S$):

- $T_\gamma$ has a **unique fixed point** $v_\gamma$.
- For any starting $f_0$, the iterates $f_{n+1} = T_\gamma(f_n)$
  converge to $v_\gamma$ geometrically at rate $\gamma$.

This is the foundation of **value iteration** for zero-sum stochastic
games, and identifies $v_\gamma$ as the discounted value
([[game_theory.stochastic_game.value.discounted_value]],
[[game_theory.stochastic_game.value.discounted_value_fixed_point]]).

## References

- Shapley, L. S. (1953). "Stochastic Games". *PNAS* 39: 1095–1100.
- [MFoGT Chapter 8, §8.6.2] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*.
