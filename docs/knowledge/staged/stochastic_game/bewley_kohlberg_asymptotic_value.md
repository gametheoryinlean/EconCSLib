---
id: game_theory.stochastic_game.asymptotic.bewley_kohlberg_asymptotic_value
title: Bewley-Kohlberg Asymptotic Value
kind: theorem
status: staged
primary_topic: game_theory.stochastic_game
topics:
  - game_theory.stochastic_game
  - game_theory.stochastic_game.asymptotic
uses:
  - game_theory.stochastic_game.value.discounted_value_fixed_point
verification:
  statement: accepted
  proof: gap
tags:
  - stochastic-game
  - zero-sum
  - asymptotic-value
  - bewley-kohlberg
---

# Bewley-Kohlberg Asymptotic Value

**Theorem (Bewley-Kohlberg 1976).** For every finite-state, finite-action
two-player zero-sum stochastic game, the discounted-value function
$v_\gamma$ ([[game_theory.stochastic_game.value.discounted_value]]) converges as
$\gamma \to 1^-$ to a limit function $v_\infty : S \to \mathbb{R}$, the
**asymptotic value**:
$$
v_\infty(s) = \lim_{\gamma \to 1^-} v_\gamma(s).
$$

Equivalently, the average-reward value of the $T$-stage games
$v_T = \frac{1}{T} \sum_{t=0}^{T-1} \mathbb{E}[r(s_t, a_t)]$
converges to the same limit:
$\lim_T v_T(s) = v_\infty(s)$.

## Proof idea (semialgebraic geometry)

The discounted-value map $\gamma \mapsto v_\gamma$ is **semialgebraic**:
the fixed-point equation $v_\gamma = T_\gamma(v_\gamma)$
([[game_theory.stochastic_game.value.discounted_value_fixed_point]]) writes
$v_\gamma$ as the solution of a polynomial system in $\gamma$ and the
data of the game. By Tarski-Seidenberg (or basic semialgebraic
geometry over $\mathbb{R}$), $v_\gamma(s)$ is a *rational function* of
$\gamma$ in a punctured neighbourhood of $1$.

A rational function has a limit as $\gamma \to 1$, completing the
proof. The argument also gives a **Puiseux expansion**
$v_\gamma(s) = \sum_{k \ge 0} c_k(s) (1 - \gamma)^{k / d}$ valid in a
right-neighbourhood of $\gamma = 1$.

## Significance

- This is the *first* theorem establishing existence of an
  undiscounted (long-run-average) value for general finite zero-sum
  stochastic games. Earlier work handled only special cases
  (irreducible chains, perfect information).
- The semialgebraic-geometry technique inspired the much harder uniform
  value theorem
  ([[game_theory.stochastic_game.asymptotic.mertens_neyman_uniform_value]]).
- The Puiseux expansion is sharp: there exist games (Big Match
  [[game_theory.stochastic_game.examples.big_match_uniform_value]] is the
  canonical one) where the leading exponent is not an integer.

## What is *not* claimed

Bewley-Kohlberg gives **convergence of the value functions** but not
that there are uniformly $\varepsilon$-optimal strategies. The
uniform-value question — whether players have strategies guaranteeing
$v_\infty$ up to $\varepsilon$ *uniformly over all sufficiently large
horizons* — is the much harder Mertens-Neyman 1981 theorem.

## References

- Bewley, T. and Kohlberg, E. (1976). "The Asymptotic Theory of
  Stochastic Games". *Math. Oper. Res.* 1: 197–208.
- Mertens, J.-F. and Neyman, A. (1981). "Stochastic Games".
  *Int. J. Game Theory* 10: 53–66.
- [MFoGT Chapter 8] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*.
