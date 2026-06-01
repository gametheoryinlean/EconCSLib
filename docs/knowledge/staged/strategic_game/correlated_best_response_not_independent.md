---
id: game_theory.strategic_game.correlated.correlated_best_response_not_independent
primary_topic: game_theory.strategic_game
topics:
  - game_theory.strategic_game
  - game_theory.strategic_game.bayesian_correlated
title: Correlated Best Response Need Not Be Independent
kind: example
status: staged
uses:
  - game_theory.strategic_game.best_response
  - game_theory.strategic_game.correlated.correlated_strategy
verification:
  proof: not_applicable
tags:
  - strategic-game
  - best-response
  - correlation
  - example
---

# Correlated Best Response Need Not Be Independent

In two-player games, being a best response to an opponent mixed strategy and
being a best response to an opponent correlated strategy coincide. MFoGT Rem.
4.3.3 shows that this fails with three or more players.

Let players 1 and 2 have pure strategies $T,B$ and $L,R$, and let player 3 have
pure strategies $M_1,M_2,M_3,M_4$. Player 3's payoffs are:

- $M_1$ gives payoff $8$ at $(T,L)$ and $0$ otherwise.
- $M_2$ gives payoff $4$ at $(T,L)$ and $(B,R)$ and $0$ otherwise.
- $M_3$ gives payoff $8$ at $(B,R)$ and $0$ otherwise.
- $M_4$ gives payoff $3$ at every profile of players 1 and 2.

Then $M_2$ is a best response to the correlated distribution
$$
  \frac12(T,L)+\frac12(B,R),
$$
but $M_2$ is never a best response to any independent mixed profile of players 1
and 2.

Indeed, if player 1 plays $T$ with probability $x$ and player 2 plays $L$ with
probability $y$, then $M_2$ can tie both $M_1$ and $M_3$ only when
$xy=(1-x)(1-y)$, equivalently $x+y=1$. In that case its payoff is at most $2$,
while $M_4$ gives payoff $3$.

## References

- [MFoGT, Rem. 4.3.3] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Three-player example where M_2 is a best response to a correlated opponent strategy but never to an independent mixed profile.
