---
id: game_theory.strategic_game.zero_sum.learning.continuous_fictitious_play_gap
title: Continuous Fictitious Play Closes The Duality Gap
kind: proposition
status: admitted
primary_topic: game_theory.zero_sum
topics:
  - game_theory.zero_sum
  - game_theory.zero_sum.learning
uses:
  - game_theory.strategic_game.zero_sum.learning.fictitious_play
  - game_theory.strategic_game.zero_sum.core.duality_gap
  - game_theory.strategic_game.zero_sum.maximin_le_minimax
source:
  spans:
    - artifact: mfogt
      locator: "Proposition 2.7.3"
      format: section
      note: "Continuous fictitious play duality gap convergence"
verification:
  statement: accepted
  proof: gap
tags:
  - zero-sum
  - learning
  - fictitious-play
---

# Continuous Fictitious Play Closes The Duality Gap

Continuous fictitious play is the continuous-time analogue of the empirical
frequency recursion. In logarithmic time it is the best-response differential
inclusion
$$
  \dot x(t)\in BR_1(y(t))-x(t),
  \qquad
  \dot y(t)\in BR_2(x(t))-y(t).
$$
Equivalently, for some
$$
  \alpha(t)=x(t)+\dot x(t)\in BR_1(y(t)),
  \qquad
  \beta(t)=y(t)+\dot y(t)\in BR_2(x(t)).
$$

For continuous fictitious play in a finite matrix game, the duality gap
$$
  W(x,y)=L(y)-M(x)
$$
converges to $0$ at speed $O(1/t)$ in the original time scale.

*Proof.* MFoGT's proof differentiates the duality gap along the time-changed
trajectory. Using the envelope theorem and bilinearity of $g(x,y)=xAy$,
$$
  \dot W(t)
  =g(\alpha(t),\dot y(t))-g(\dot x(t),\beta(t))
  =M(x(t))-L(y(t))
  =-W(t).
$$
Thus $W(t)=W(0)e^{-t}$ after the logarithmic time change, which gives the
$O(1/t)$ rate in the original continuous fictitious-play process. Since the
optimal-strategy set is exactly the zero set of $W$, convergence of the gap
implies convergence toward $X(A)\times Y(A)$.

## References

- [MFoGT, Prop. 2.7.3] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Continuous fictitious play duality gap convergence.
