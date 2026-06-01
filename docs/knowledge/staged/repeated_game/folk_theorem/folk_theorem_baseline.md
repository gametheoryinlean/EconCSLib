---
id: game_theory.repeated_game.folk_theorem.folk_theorem_baseline
title: Folk Theorem (Baseline Statement)
kind: theorem
status: staged
primary_topic: game_theory.repeated_game
topics:
  - game_theory.repeated_game
  - game_theory.repeated_game.folk_theorem
uses:
  - game_theory.repeated_game.core.payoff_aggregation
verification:
  statement: accepted
  proof: gap
tags:
  - repeated-game
  - folk-theorem
---

# Folk Theorem (Baseline Statement)

**Theorem (Nash Folk Theorem; classical).** Consider an $N$-player
stage game $G$ with finite action sets, and the infinitely repeated
game with limit-of-means payoffs
([[game_theory.repeated_game.core.payoff_aggregation]]). Every payoff vector
$v \in V^*$ — where $V^*$ is the set of feasible and *individually
rational* payoff vectors of $G$ — is a Nash equilibrium payoff of the
infinitely repeated game.

**Feasible**: $v \in \operatorname{conv}\{u(a) : a \in A\}$ (a convex
combination of stage-game payoff vectors).
**Individually rational**: for each player $i$, $v_i$ is at least
player $i$'s **minmax value** in $G$:
$v_i \ge \min_{\sigma_{-i}} \max_{\sigma_i} u_i(\sigma_i, \sigma_{-i})$.

## Proof intuition (grim trigger)

For any feasible payoff $v$ achievable by a strategy profile $\bar\sigma$
(possibly correlated through a public randomisation device), build the
following infinite-horizon strategy for each player:

1. **Cooperative phase**: play $\bar\sigma_i$ as long as no deviation
   has been observed.
2. **Punishment phase**: if any player $j$ has deviated, switch
   permanently to a strategy profile that minmaxes player $j$.

The threat of permanent reversion to a minmax-yielding profile makes
the cooperative phase incentive-compatible (per-stage gain from
deviating is finite; per-stage loss from punishment is permanent).

## Refinements

The Nash Folk Theorem above is "easy"; the much harder refinements
strengthen the equilibrium concept:

- **Aumann-Shapley / Rubinstein 1979–1994** — Folk Theorem for
  *subgame-perfect equilibrium* with limit-of-means payoffs.
- **Friedman 1971** — Folk Theorem for *discounted* SPE with
  $\gamma$ close to $1$, under a slightly stronger feasibility condition
  ("Pareto-dominates a Nash payoff").
- **Fudenberg-Maskin 1986** — full-dimensionality conditions for
  discounted SPE Folk Theorem in general.
- **Fudenberg-Levine-Maskin 1994** — Folk Theorem under public
  imperfect monitoring.

## Status in this blueprint

This node states the baseline result and exists as a placeholder for
the full Folk-theorem subtree. Detailed refinements (Friedman, FLM,
FLM-Tirole) and the Lean proof remain to be developed.

## References

- Aumann, R. J. and Shapley, L. S. (1976/1994). "Long-Term Competition
  — A Game-Theoretic Analysis".
- Friedman, J. W. (1971). "A Non-Cooperative Equilibrium for Supergames".
  *Rev. Econ. Stud.* 38: 1–12.
- Fudenberg, D. and Maskin, E. (1986). "The Folk Theorem in Repeated
  Games with Discounting or with Incomplete Information".
  *Econometrica* 54: 533–554.
- [MSZ Chapter 14] Maschler, Solan, and Zamir, *Game Theory*.
- Mailath, G. and Samuelson, L. (2006). *Repeated Games and Reputations.* Oxford.
