---
id: game_theory.repeated_game.core.payoff_aggregation
title: Repeated Game Payoff Aggregation
kind: definition
status: staged
primary_topic: game_theory.repeated_game
topics:
  - game_theory.repeated_game
  - game_theory.repeated_game.core
uses:
  - game_theory.repeated_game.core.history
verification:
  definition: accepted
  proof: not_applicable
tags:
  - repeated-game
  - payoff-aggregation
---

# Repeated Game Payoff Aggregation

Repeated games come with several **payoff aggregation rules** that
collapse the per-stage payoff sequence
$(u_i(a_0), u_i(a_1), \dots)$ into a single number for player $i$.

## T-stage average

For finite horizon $T$:
$$
\Pi_T^i(a_0, a_1, \dots) = \frac{1}{T} \sum_{t = 0}^{T - 1} u_i(a_t).
$$

The $T$-stage Nash equilibrium of the finitely repeated game often
collapses to a one-shot equilibrium by backward induction (e.g.\
finitely repeated prisoner's dilemma).

## $\gamma$-discounted

For discount factor $\gamma \in (0, 1)$:
$$
\Pi_\gamma^i = (1 - \gamma) \sum_{t = 0}^{\infty} \gamma^t \, u_i(a_t).
$$

The leading $(1 - \gamma)$ normalizes constant per-stage payoffs to
average to themselves, putting $\Pi_\gamma$ on the scale of $u_i$.

## Undiscounted (limit-of-means)

$$
\Pi_\infty^i = \liminf_{T \to \infty} \Pi_T^i.
$$

The $\liminf$ form is the cautious convention; symmetric variants use
$\limsup$ or require the limit to exist. Both players' aggregation
choices must be compatible for the resulting game to have a well-defined
value.

## Uniform evaluation

A payoff is *uniformly* guaranteed if it is guaranteed simultaneously
for all sufficiently large $T$ (or for $\gamma$ in a neighbourhood of
$1$). Uniform values are the strongest notion and the technically
hardest to establish — see Mertens-Neyman 1981
([[game_theory.stochastic_game.asymptotic.mertens_neyman_uniform_value]]) for the
stochastic-game version; the analog in pure repeated games is much
easier (no state dynamics).

## Relations

- For the **zero-sum** case, the discounted value $v_\gamma$ converges
  to the limit-of-means value as $\gamma \to 1$ whenever the latter is
  well-defined. Even when uniform value fails, $v_\gamma$ may still
  have a limit (Hardy-Littlewood-style Abelian / Tauberian theorems).
- For the **general-sum** case, the Folk Theorem (e.g.\ Friedman 1971
  for discounted) characterises which payoff vectors arise in Nash
  equilibrium under each aggregation.

## References

- [MSZ Chapters 13–14] Maschler, Solan, and Zamir, *Game Theory*.
- Aumann, R. J. and Shapley, L. S. (1976/1994). "Long-Term Competition".
- Mailath, G. and Samuelson, L. (2006). *Repeated Games and Reputations.* Oxford.
