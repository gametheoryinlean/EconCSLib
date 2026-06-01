---
id: game_theory.stochastic_game.asymptotic.mertens_neyman_uniform_value
title: Mertens-Neyman Uniform Value
kind: theorem
status: staged
primary_topic: game_theory.stochastic_game
topics:
  - game_theory.stochastic_game
  - game_theory.stochastic_game.asymptotic
uses:
  - game_theory.stochastic_game.asymptotic.bewley_kohlberg_asymptotic_value
verification:
  statement: accepted
  proof: gap
tags:
  - stochastic-game
  - zero-sum
  - uniform-value
  - mertens-neyman
---

# Mertens-Neyman Uniform Value

**Theorem (Mertens-Neyman 1981).** Every finite-state, finite-action
two-player zero-sum stochastic game has a **uniform value**: there
exists $v(s) : S \to \mathbb{R}$ (necessarily equal to the asymptotic
value $v_\infty$ of
[[game_theory.stochastic_game.asymptotic.bewley_kohlberg_asymptotic_value]]) such
that for every $\varepsilon > 0$ there are strategies
$\sigma_1^\varepsilon, \sigma_2^\varepsilon$ guaranteeing $v$ up to
$\varepsilon$ **uniformly over all sufficiently long horizons** $T$
and all sufficiently large discount factors $\gamma$:
$$
\begin{aligned}
\sigma_1^\varepsilon \text{ guarantees}\quad &
  \tfrac{1}{T}\,\mathbb{E}_{\sigma_1^\varepsilon, \sigma_2}\!\left[\sum_{t < T} r_t\right] \;\ge\; v(s) - \varepsilon \\
\sigma_2^\varepsilon \text{ guarantees}\quad &
  \tfrac{1}{T}\,\mathbb{E}_{\sigma_1, \sigma_2^\varepsilon}\!\left[\sum_{t < T} r_t\right] \;\le\; v(s) + \varepsilon
\end{aligned}
$$
for all sufficiently large $T$ and all opposing strategies.

## Why it is much harder than Bewley-Kohlberg

Bewley-Kohlberg
([[game_theory.stochastic_game.asymptotic.bewley_kohlberg_asymptotic_value]])
proves convergence of *values*; Mertens-Neyman additionally produces
*strategies* that achieve those values uniformly. The Big Match
([[game_theory.stochastic_game.examples.big_match_uniform_value]]) is the
prototypical example showing that *stationary* $\gamma$-discounted
optimal strategies need not work for the uniform value — Mertens-Neyman
must construct history-dependent strategies with delicate concentration
arguments based on Bewley-Kohlberg's Puiseux expansion.

## Proof technique (very high level)

1. Start from the Bewley-Kohlberg Puiseux expansion of $v_\gamma$ near
   $\gamma = 1$.
2. Design **history-dependent** strategies whose play in stage $t$
   depends on a slowly-varying threshold tied to the discount-factor
   parametrisation.
3. Use a martingale concentration argument to show empirical averages
   stay close to $v_\infty$ with high probability.
4. Translate uniform-in-$\gamma$ bounds into uniform-in-$T$ bounds.

The original paper is a tour-de-force ~30 pages with intricate
combinatorial estimates.

## Open generalisations

- **Definable games**: extending uniform-value existence beyond finite
  state spaces is an active area, with positive results for
  "definable" parametrisations and negative results for arbitrary
  Borel state spaces (Ziliotto 2016).
- **General-sum**: a corresponding uniform-equilibrium-payoff
  characterisation is open in general (Vrieze-Tijs conjecture territory).

## References

- Mertens, J.-F. and Neyman, A. (1981). "Stochastic Games".
  *Int. J. Game Theory* 10: 53–66.
- Bewley, T. and Kohlberg, E. (1976). "The Asymptotic Theory of
  Stochastic Games". *Math. Oper. Res.* 1: 197–208.
- Renault, J. (2014). "General Limit Value in Dynamic Programming".
  *J. Dynam. Games* 1: 471–484.
- [MFoGT Chapter 8] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*.
