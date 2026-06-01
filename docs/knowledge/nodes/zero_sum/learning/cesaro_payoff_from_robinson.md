---
id: game_theory.strategic_game.zero_sum.learning.cesaro_payoff_from_robinson
title: Cesàro Payoff Convergence From Robinson Lemma
kind: lemma
status: admitted
primary_topic: game_theory.zero_sum
topics:
  - game_theory.zero_sum
  - game_theory.zero_sum.learning
uses:
  - game_theory.strategic_game.zero_sum.learning.robinson_admissible_lemma
  - game_theory.strategic_game.zero_sum.core.value
lean:
  modules:
    - EconCSLib.GameTheory.StrategicGame.ZeroSum.Learning.Cesaro
  declarations:
    - MatrixGame.realisedCumPayoff
source:
  spans:
    - artifact: mfogt
      locator: "Theorem 2.7.2, part 2 (average-payoff conclusion)"
      format: section
      note: "Telescoping derivation of Cesaro average convergence from Robinson's gap bound"
verification:
  statement: accepted
  proof: gap
tags:
  - zero-sum
  - fictitious-play
  - robinson
  - cesaro
---

# Cesàro Payoff Convergence From Robinson Lemma

The average realised payoff along a fictitious-play trajectory converges to the
value of the game. The proof is an elementary telescoping identity that uses
the Robinson admissible-sequence lemma
[[game_theory.strategic_game.zero_sum.learning.robinson_admissible_lemma]] only as a black box.

## Setup

Let $A \in \mathbb{R}^{m \times n}$ be a matrix game with value $v := v(A)$
established by [[game_theory.strategic_game.zero_sum.learning.robinson_admissible_lemma]]
(equivalently, by the minimax theorem). Let $(i_n, j_n)_{n \ge 1}$ be a
fictitious-play realisation
([[game_theory.strategic_game.zero_sum.learning.fictitious_play]]).

Define the **realised cumulative payoff** $R_n$ and the **counterfactual
cumulative payoffs** $U_m^i$ for each pure row $i$:
$$
  R_n := \sum_{p=1}^n A_{i_p, j_p},
  \qquad
  U_m^i := \sum_{k=1}^m A_{i, j_k}.
$$
$U_m^i$ is the payoff player I would have accrued by always playing pure $i$
against player II's actual sequence $j_1, \ldots, j_m$.

## Statement

$$
  \frac{1}{n} R_n \;\longrightarrow\; v \quad \text{as } n \to \infty.
$$

## Proof

**Telescoping identity.** For every $n \ge 1$,
$$
  R_n \;=\; U_n^{i_n} \;+\; \sum_{p=1}^{n-1} (U_p^{i_p} - U_p^{i_{p+1}}).
$$
*Verification.* Note $U_n^{i_n} = \sum_{k=1}^n A_{i_n, j_k}$. Then
$$
  R_n - U_n^{i_n}
   = \sum_{k=1}^n (A_{i_k, j_k} - A_{i_n, j_k})
   = \sum_{p=1}^{n-1} (U_p^{i_p} - U_p^{i_{p+1}})
$$
by reindexing — each term on the right corresponds to the "switch" from row
$i_p$ to $i_{p+1}$ at step $p+1$, which redefines what the counterfactual
cumulative would have been.

**Sign of the telescoping increments.** By the fictitious-play best-response
condition, $i_{p+1} \in \operatorname{argmax}_i (Ay_p)^i = \operatorname{argmax}_i \frac{1}{p} U_p^i$,
hence $U_p^{i_{p+1}} \ge U_p^{i_p}$. Therefore
$$
  U_p^{i_p} - U_p^{i_{p+1}} \;\le\; 0, \quad p = 1, \ldots, n-1.
$$

**Upper bound on $R_n / n$.** The telescoping identity together with the sign
gives
$$
  R_n \;\le\; U_n^{i_n}.
$$
Since $i_n \in \operatorname{argmax}_i U_n^i / n$ (with $U_n^i / n = (A y_n)^i$ where $y_n$
is player II's empirical frequency), we have
$U_n^{i_n} / n = \max_i (A y_n)^i$. The minimax bracket together with
$\mu(n)/n \to 0$ from
[[game_theory.strategic_game.zero_sum.learning.robinson_admissible_lemma]] yields
$\max_i (A y_n)^i \to v$. Hence
$$
  \limsup_{n \to \infty} \frac{R_n}{n} \;\le\; v.
$$

**Lower bound on $R_n / n$.** Apply the dual telescoping identity (player II's
perspective):
$$
  R_n = V_n^{j_n} + \sum_{p=1}^{n-1} (V_p^{j_p} - V_p^{j_{p+1}}),
$$
where $V_m^j := \sum_{k=1}^m A_{i_k, j}$. The best-response condition for II
makes the telescoping increments $\ge 0$, giving $R_n \ge V_n^{j_n}$. By the
analogous limit, $V_n^{j_n} / n = \min_j (x_n A)^j \to v$, hence
$\liminf R_n / n \ge v$.

Combining, $R_n / n \to v$. $\square$

## Note

This proof is **independent** of the internal combinatorial structure of
Robinson's induction
([[game_theory.strategic_game.zero_sum.learning.robinson_admissible_lemma.bracket_invariant]],
[[game_theory.strategic_game.zero_sum.learning.robinson_admissible_lemma.useful_window]],
[[game_theory.strategic_game.zero_sum.learning.robinson_admissible_lemma.subgame_reduction]],
[[game_theory.strategic_game.zero_sum.learning.robinson_admissible_lemma.induction_step]]). It uses
the parent lemma only via its conclusion $\mu(n)/n \to 0$.

Practically, this makes it the **shortest formalisable item** in the Robinson
chain — a natural first Lean target.

## References

- [MFoGT, Chapter 2, Section 2.7] Laraki, Renault, and Sorin,
  *Mathematical Foundations of Game Theory*. Cesàro average-payoff
  convergence along fictitious play; see the `source` block above for
  the precise locator.
