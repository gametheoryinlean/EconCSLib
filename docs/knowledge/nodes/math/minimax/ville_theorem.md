---
id: math.minimax.ville_theorem
title: Ville Theorem
kind: theorem
status: admitted
primary_topic: math
topics:
  - math
  - math.minimax
uses:
  - game_theory.strategic_game.zero_sum.von_neumann_minimax
source:
  spans:
    - artifact: mfogt
      locator: "Theorem 2.5.3"
      format: section
      note: "Continuous zero-sum game on [0,1] has a value in mixed strategies"
verification:
  statement: accepted
  proof: accepted
tags:
  - zero-sum
  - minimax
  - continuous-game
---

# Ville Theorem

Let $I=J=[0,1]$ and let $f:I\times J\to\mathbb{R}$ be continuous.  The mixed
extension over Borel probability measures on $[0,1]$ has a value, and each
player has an optimal strategy.  Moreover, for every $\varepsilon>0$, each
player has an $\varepsilon$-optimal strategy with finite support.

The mixed payoff is
$$
  f(\sigma,\tau)=\int_{[0,1]\times[0,1]} f(x,y)\,d\sigma(x)\,d\tau(y),
$$
where $\sigma$ and $\tau$ are Borel probability measures on $[0,1]$.

*Proof.* One discretizes the square
$[0,1]\times[0,1]$ by finer and finer grids, applies finite minimax to each
matrix game, and then extracts weakly convergent subsequences of optimal
probability measures. Uniform continuity transfers the finite-grid guarantees to
the continuous game. The finite-support $\varepsilon$-optimal strategies come
from the same grid approximations.

## References

- [MFoGT, Thm. 2.5.3] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Continuous zero-sum game on [0,1] has a value in mixed strategies.
