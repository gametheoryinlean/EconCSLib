---
id: math.minimax.ville_discretization_proof
title: Ville Theorem By Discretization
kind: proof-plan
status: admitted
primary_topic: math
topics:
  - math
  - math.minimax
target: math.minimax.ville_theorem
plan_status: selected
uses:
  - game_theory.strategic_game.zero_sum.von_neumann_minimax
source:
  spans:
    - artifact: mfogt
      locator: "Section 2.8, Exercise 3"
      format: section
      note: "Proof of Ville's theorem by finite discretizations and weak convergence"
verification:
  proof: accepted
tags:
  - zero-sum
  - ville
  - continuous-game
  - proof-plan
---

# Ville Theorem By Discretization

Let $X=Y=[0,1]$ and let $f:X\times Y\to\mathbb R$ be continuous. For each
$n\ge1$, form the finite grid
$$
  X_n=Y_n=\{0,1,\ldots,2^n\}
$$
and the finite matrix game
$$
  G_n(i,j)=f(i/2^n,j/2^n).
$$
Let $v_n$ be the mixed value of $G_n$.

*Proof.* The proof of Ville's theorem has two steps.

First, use uniform continuity of $f$ to transfer guarantees from sufficiently fine
grid games to the original continuous game. If player 1 plays an optimal mixed
strategy on a fine grid, interpreted as a finitely supported Borel probability
measure on $[0,1]$, then player 1 guarantees $\limsup_n v_n$ up to any prescribed
$\varepsilon>0$. Dually, player 2 guarantees $\liminf_n v_n$ from above. These
two inequalities force existence of a value.

Second, regard optimal grid strategies as Borel probability measures on the
compact interval $[0,1]$. By compactness of probability measures in the weak
topology, extract weakly convergent subsequences. Continuity of $f$ lets the
payoff functional pass to the limit, and the limiting measures are optimal
strategies. The finite grid strategies also give the finite-support
$\varepsilon$-optimal strategies.

## References

- [MFoGT, Section 2.8, Exercise 3] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Proof of Ville's theorem by finite discretizations and weak convergence.
