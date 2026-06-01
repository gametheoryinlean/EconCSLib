---
id: game_theory.strategic_game.zero_sum.examples.silent_duel_no_pure_value
title: Silent One-Bullet Duel Has No Pure Value
kind: proposition
status: admitted
primary_topic: game_theory.zero_sum
topics:
  - game_theory.zero_sum
  - game_theory.zero_sum.examples
uses:
  - game_theory.strategic_game.zero_sum.core.value
source:
  spans:
    - artifact: mfogt
      locator: "Section 3.5, Exercise 1(3)"
      format: section
      note: "Silent one-bullet duel with p1(t)=p2(t)=t"
    - artifact: mfogt
      locator: "Section 9.3, Exercise 1(3) hints"
      format: section
      note: "Constructs a mixed strategy with density C y^{-3} on [a,1]"
verification:
  statement: accepted
  proof: accepted
tags:
  - zero-sum
  - duel
  - continuous-game
  - mixed-strategy
---

# Silent One-Bullet Duel Has No Pure Value

In the silent one-bullet duel, each player chooses a shooting time
$x\in[0,1]$, but a player does not observe whether the opponent has already
shot. Assume $p_1(t)=p_2(t)=t$.

The pure-strategy game has no value. However, player 1 can guarantee a
non-negative payoff by using a mixed strategy supported on $[1/3,1]$ with
density
$$
  f(y)=\frac14 y^{-3}\mathbf 1_{y\ge 1/3}.
$$
By symmetry, player 2 can guarantee the opposite bound. Thus the silent
one-bullet duel has mixed value $0$ even though it has no pure value.

This exercise is a useful warning that pure values can fail in timing games even
when a natural mixed guarantee exists.

*Proof.* For pure shooting times $x,y$, the symmetric silent-duel payoff is
$$
  g(x,y)=
  \begin{cases}
    x-(1-x)y, & x<y,\\
    0, & x=y,\\
    x-(1+x)y, & x>y.
  \end{cases}
$$
If $y>0$, player 1 can shoot just before $y$ and obtain payoff arbitrarily close
to $y^2$. If $y<1$, player 1 can shoot at $1$ and obtain $1-2y$. Hence
$$
  \inf_y\sup_x g(x,y)>0.
$$
But the game is symmetric and zero-sum, so a pure value, if it existed, would
have to be $0$. Therefore there is no pure value.

Now let $\sigma$ have density $f(y)=\frac14y^{-3}$ on $[1/3,1]$. This is a
probability density because
$$
  \int_{1/3}^1 \frac14y^{-3}\,dy=1.
$$
For $y\ge 1/3$, direct integration gives
$$
  \int g(x,y)\,d\sigma(x)=0.
$$
For $y<1/3$, every $x$ in the support satisfies $x>y$, so
$$
  \int g(x,y)\,d\sigma(x)
  =(1-y)\int x\,d\sigma(x)-y
  =(1-y)\frac12-y
  =\frac{1-3y}{2}\ge0.
$$
Thus player 1 guarantees at least $0$. By symmetry the same distribution lets
player 2 hold player 1 to at most $0$, so the mixed value is $0$.

## References

- [MFoGT, Section 3.5, Exercise 1(3)] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Silent one-bullet duel with p1(t)=p2(t)=t.
- [MFoGT, Section 9.3, Exercise 1(3) hints] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Constructs a mixed strategy with density C y^{-3} on [a,1].
