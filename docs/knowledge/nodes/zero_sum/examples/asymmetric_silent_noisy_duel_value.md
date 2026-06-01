---
id: game_theory.strategic_game.zero_sum.examples.asymmetric_silent_noisy_duel_value
title: Silent Versus Noisy One-Bullet Duel Value
kind: proposition
status: admitted
primary_topic: game_theory.zero_sum
topics:
  - game_theory.zero_sum
  - game_theory.zero_sum.examples
uses:
  - game_theory.strategic_game.zero_sum.examples.silent_duel_no_pure_value
source:
  spans:
    - artifact: mfogt
      locator: "Section 3.5, Exercise 1(4)"
      format: section
      note: "One silent gun versus one noisy gun, with p1(t)=p2(t)=t"
    - artifact: mfogt
      locator: "Section 9.3, Exercise 1(4) hints"
      format: section
      note: "Confirms the displayed strategies form a saddle point"
verification:
  statement: accepted
  proof: accepted
tags:
  - zero-sum
  - duel
  - continuous-game
  - mixed-strategy
---

# Silent Versus Noisy One-Bullet Duel Value

Consider the one-bullet duel where player 1's gun is silent and player 2's gun
is noisy, with $p_1(t)=p_2(t)=t$. MFoGT Exercise 3.5.1(4) states that the game
has a mixed value
$$
  v=1-2a,\qquad a=\sqrt 6-2.
$$

Player 1 guarantees this value by using the density
$$
  f(x)=
  \begin{cases}
    0, & 0\le x<a,\\
    \frac{\sqrt{2a}}{(x^2+2x-1)^{3/2}}, & a\le x\le 1.
  \end{cases}
$$
Player 2 guarantees the same bound with cumulative distribution function
$$
  G(y)=\frac{2}{2+a}\int_0^y f(x)\,dx
       +\frac{a}{2+a}I_1(y),
$$
where $I_1$ is the distribution function of a Dirac mass at $1$.

The example records an asymmetric timing game where the informational difference
between silent and noisy shots changes the mixed value and optimal distributions.

*Proof.* The pure payoff to player 1 is
$$
  g(x,y)=
  \begin{cases}
    x-y+xy, & x<y,\\
    0, & x=y,\\
    1-2y, & x>y.
  \end{cases}
$$
The displayed density for player 1 and distribution function for player 2 are
probability distributions when $a=\sqrt6-2$. Substituting them into the three
pieces of $g$ and integrating on $[a,1]$ gives
$$
  \int g(x,y)\,f(x)\,dx\ge 1-2a
  \quad\text{for every pure }y,
$$
with equality on the support of player 2's mixed strategy. The dual computation
with $G$ gives
$$
  \int g(x,y)\,dG(y)\le 1-2a
  \quad\text{for every pure }x,
$$
with equality on the support of $f$. Hence the displayed pair is a saddle point
and the value is $1-2a$.

## References

- [MFoGT, Section 3.5, Exercise 1(4)] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. One silent gun versus one noisy gun, with p1(t)=p2(t)=t.
- [MFoGT, Section 9.3, Exercise 1(4) hints] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Confirms the displayed strategies form a saddle point.
