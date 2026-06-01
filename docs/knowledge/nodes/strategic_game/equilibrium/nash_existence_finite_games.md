---
id: game_theory.strategic_game.equilibrium.nash_existence_finite_games
title: Nash Existence For Finite Games
kind: theorem
status: proved
primary_topic: game_theory.strategic_game
topics:
  - game_theory.strategic_game
  - game_theory.strategic_game.equilibrium
uses:
  - math.fixed_point.brouwer_compact_convex
  - game_theory.strategic_game.equilibrium.mixed_nash_equilibrium
source:
  spans:
    - artifact: mfogt
      locator: "Theorem 4.6.2"
      format: section
      note: "Every finite game has a mixed Nash equilibrium; Brouwer-based proof via the Nash gain map"
lean:
  modules:
    - EconCSLib.GameTheory.StrategicGame.Nash
  declarations:
    - StrategicGame.exists_mixed_nash_equilibrium_finite
verification:
  statement: accepted
  proof: accepted
  alignment: aligned
tags:
  - strategic-game
  - nash-equilibrium
  - existence
---

# Nash Existence For Finite Games

**Theorem.** Every finite strategic game $G=(I,(S^i)_{i\in I},(g^i)_{i\in I})$ has
a mixed-strategy Nash equilibrium.

## Proof

Let $\Delta=\prod_{i\in I}\Delta(S^i)$ be the product of the mixed-strategy
simplices — a nonempty, compact, convex subset of a finite-dimensional space.
For a profile $\sigma\in\Delta$, player $i$, and pure strategy $s^i\in S^i$,
define the **gain**
$$
  c^i_{s^i}(\sigma)=\bigl(g^i(s^i,\sigma^{-i})-g^i(\sigma)\bigr)^+,
$$
the nonnegative part of the payoff improvement from deviating to the pure
strategy $s^i$, where $g^i(\sigma)=\sum_{s^i}\sigma^i(s^i)\,g^i(s^i,\sigma^{-i})$
is $i$'s expected payoff. Define the **Nash map** $f:\Delta\to\Delta$ by
$$
  f^i(\sigma)(s^i)=\frac{\sigma^i(s^i)+c^i_{s^i}(\sigma)}
                        {1+\sum_{t^i\in S^i}c^i_{t^i}(\sigma)} .
$$
Each $c^i_{s^i}$ is continuous (expected payoffs are multilinear and $(\cdot)^+$
is continuous) and the denominator is $\ge 1$, so $f$ is continuous; its $i$-th
block is nonnegative and sums to $1$, hence $f(\sigma)\in\Delta$. As $\Delta$ is
nonempty, compact and convex, **Brouwer's fixed-point theorem**
([[math.fixed_point.brouwer_compact_convex]]) yields a $\sigma$ with
$f(\sigma)=\sigma$.

Such a fixed point is a Nash equilibrium. Fix $i$. If
$\sum_{t^i}c^i_{t^i}(\sigma)=0$, every gain vanishes, so
$g^i(\sigma)\ge g^i(t^i,\sigma^{-i})$ for all $t^i$ and $i$ best-responds.
Otherwise $\sum_{t^i}c^i_{t^i}(\sigma)>0$. Since $g^i(\sigma)$ is the
$\sigma^i$-average of the values $g^i(s^i,\sigma^{-i})$, some pure strategy in
the support has $\sigma^i(s^i)>0$ and $g^i(s^i,\sigma^{-i})\le g^i(\sigma)$,
whence $c^i_{s^i}(\sigma)=0$. The fixed-point equation then reads
$$
  \sigma^i(s^i)=\frac{\sigma^i(s^i)}{1+\sum_{t^i}c^i_{t^i}(\sigma)},
$$
and as the denominator exceeds $1$ this forces $\sigma^i(s^i)=0$, contradicting
$\sigma^i(s^i)>0$. Hence no player has a profitable pure deviation, so $\sigma$
is a mixed Nash equilibrium
([[game_theory.strategic_game.equilibrium.mixed_nash_equilibrium]]). Conversely,
every mixed equilibrium is a fixed point of $f$, since all gains vanish.
$\qquad\blacksquare$

## Formalization

`StrategicGame.exists_mixed_nash_equilibrium_finite` formalizes this argument.
The Brouwer step is discharged by `Brouwer_Product` (a product-of-simplices form
of Brouwer), itself reduced to Brouwer on the simplex via **Scarf's combinatorial
lemma** (`EconCSLib.Math.FixedPoint.Brouwer`, `EconCSLib.Math.FixedPoint.Scarf`),
ported from the [math-xmum/Brouwer](https://github.com/math-xmum/Brouwer)
development. The chain is `sorry`-free: `#print axioms` on the theorem reports
only `propext`, `Classical.choice`, `Quot.sound`.

## References

- [MFoGT, Thm. 4.6.2] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*, Universitext, Springer 2019, §4.6 (). Existence of a mixed Nash equilibrium in finite games via Brouwer's fixed-point theorem.
- Nash, J. F. (1951). "Non-Cooperative Games". *Annals of Mathematics* 54(2), 286–295.
