---
id: game_theory.strategic_game.zero_sum.examples.noisy_duel_multiple_bullets_value
title: Noisy Duel With Multiple Bullets
kind: theorem
status: admitted
primary_topic: game_theory.zero_sum
topics:
  - game_theory.zero_sum
  - game_theory.zero_sum.examples
uses:
  - game_theory.strategic_game.zero_sum.examples.noisy_duel_one_bullet_value
source:
  spans:
    - artifact: mfogt
      locator: "Section 3.5, Exercise 1(2)"
      format: section
      note: "Noisy duel with m bullets versus n bullets"
verification:
  statement: accepted
  proof: accepted
tags:
  - zero-sum
  - duel
  - continuous-game
---

# Noisy Duel With Multiple Bullets

In the noisy duel with $m$ bullets for player 1 and $n$ bullets for player 2,
assuming $p_1(t)=p_2(t)=t$, the game has value
$$
  \frac{m-n}{m+n}.
$$
It is optimal for the player with $\max\{m,n\}$ bullets to shoot the first bullet
at time
$$
  t_0=\frac1{m+n}.
$$

*Proof.* The proof is by induction on $m+n$. The one-bullet case is the noisy
one-bullet duel. Assume the statement known for all pairs with total bullet
count at most $K$, and consider $(m+1,n)$ with $m+n+1=K+1$.

If player 1 has more bullets, player 1 shoots first at time
$1/(m+n+1)$. If player 2 has not shot before then and player 1 misses, the
continuation is the already solved $(m,n)$ game. If player 2 shoots first and
misses, the continuation is the already solved $(m+1,n-1)$ game. If both shoot
at that time and miss, the continuation is the $(m,n-1)$ game. Substituting the
induction values of these continuation games gives the guarantee
$$
  \frac{m+1-n}{m+n+1}.
$$
The column player uses the dual strategy: randomize the first shot in a small
interval immediately after $1/(m+n+1)$ and then switch to the corresponding
optimal continuation game. Letting the interval length tend to $0$ gives the
matching upper bound. The equal-bullet case is symmetric and gives value $0$;
the case where player 2 has more bullets is the same argument with the players
interchanged. Thus the induction proves the value formula and the stated first
shot time.

## References

- [MFoGT, Section 3.5, Exercise 1(2)] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Noisy duel with m bullets versus n bullets.
