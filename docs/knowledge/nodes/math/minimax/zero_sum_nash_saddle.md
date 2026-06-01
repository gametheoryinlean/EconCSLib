---
id: math.minimax.zero_sum_nash_saddle
title: Zero-Sum Nash Equilibria As Saddle Points
kind: theorem
status: proved
primary_topic: math
topics:
  - math
  - math.minimax
uses:
  - game_theory.strategic_game.zero_sum.core.saddle_point
  - game_theory.strategic_game.zero_sum.matrix_game_nash_equilibrium
lean:
  modules:
    - EconCSLib.GameTheory.StrategicGame.ZeroSum.MatrixGame
  declarations:
    - MatrixGame.isMixedNashEq_iff_isSaddlePoint
source:
  spans:
    - artifact: mfogt
      locator: "Proposition 2.4.1(d), proof paragraph"
      format: section
      note: "Saddle points express the identity between optimal strategies and Nash equilibria"
verification:
  statement: accepted
  proof: accepted
  alignment: aligned
tags:
  - zero-sum
  - nash-equilibrium
  - saddle-point
---

# Zero-Sum Nash Equilibria As Saddle Points

In a zero-sum game, a pair of mixed strategies is a Nash equilibrium exactly
when it is a saddle point of the matrix payoff.

*Proof.* Write $u(x,y)=xAy$ for player I's payoff and $-u(x,y)$ for player
II's payoff. A mixed pair $(x^*,y^*)$ is a Nash equilibrium exactly when
$$
  u(x,y^*)\le u(x^*,y^*)\quad\text{for all }x
$$
and
$$
  -u(x^*,y)\le -u(x^*,y^*)\quad\text{for all }y.
$$
The second inequality is equivalent to $u(x^*,y^*)\le u(x^*,y)$ for all
$y$. Together these are precisely the saddle-point inequalities.

In the Lean formalisation this equivalence is *definitional*: the predicate
`MatrixGame.IsSaddlePoint` is an `abbrev` for `MatrixGame.IsMixedNashEq`, so
`isMixedNashEq_iff_isSaddlePoint` is closed by `Iff.rfl`.  The
strategic-game-level form ([[node:game_theory.strategic_game.zero_sum.matrix_game_nash_equilibrium]])
follows from the same definitional identity combined with the profile
expansion lemmas.

## References

- [MFoGT, Prop. 2.4.1(d), proof paragraph] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Saddle points express the identity between optimal strategies and Nash equilibria.
