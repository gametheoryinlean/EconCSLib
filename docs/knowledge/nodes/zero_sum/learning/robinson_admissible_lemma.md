---
id: game_theory.strategic_game.zero_sum.learning.robinson_admissible_lemma
title: Robinson Admissible Sequence Lemma
kind: lemma
status: admitted
primary_topic: game_theory.zero_sum
topics:
  - game_theory.zero_sum
  - game_theory.zero_sum.learning
uses:
  - game_theory.strategic_game.zero_sum.learning.robinson_admissible_lemma.induction_step
lean:
  modules:
    - EconCSLib.GameTheory.StrategicGame.ZeroSum.Learning.Robinson
  declarations:
    - MatrixGame.AdmissibleSequence
source:
  spans:
    - artifact: mfogt
      locator: "Section 2.8, Exercise 12"
      format: section
      note: "Robinson's admissible-sequence proof of fictitious play convergence"
    - artifact: robinson-1951
      locator: "Annals of Mathematics 54 (1951), 296–301"
      format: section
      note: "Original publication; Theorem of the paper"
verification:
  statement: accepted
  proof: gap
tags:
  - zero-sum
  - fictitious-play
  - robinson
---

# Robinson Admissible Sequence Lemma

## Setup

Let $A \in \mathbb{R}^{m \times n}$ be a matrix-game payoff. Write
$\|A\| := \max_{i,j}|A_{i,j}|$.

For $\alpha \in \mathbb{R}^n$ and $\beta \in \mathbb{R}^m$ define
$$
  J(\alpha) := \{j : \alpha^j = \min_k \alpha^k\}, \qquad
  I(\beta)  := \{i : \beta^i = \max_k \beta^k\}.
$$

An **admissible sequence** is $(\alpha(t), \beta(t))_{t \ge 0}$ in
$\mathbb{R}^n \times \mathbb{R}^m$ satisfying

- (i) $\min_k \alpha^k(0) = \max_k \beta^k(0)$;
- (ii) at each $t \ge 0$, $\exists i_{t+1} \in I(\beta(t))$,
  $j_{t+1} \in J(\alpha(t))$ with
  $$
    \alpha(t+1) = \alpha(t) + e_{i_{t+1}}^T A, \qquad
    \beta(t+1)  = \beta(t)  + A e_{j_{t+1}}.
  $$

This is a cumulative-payoff encoding of fictitious play
([[game_theory.strategic_game.zero_sum.learning.fictitious_play]]): writing
$x(t) := \frac1t \sum_{s \le t} e_{i_s}$ and
$y(t) := \frac1t \sum_{s \le t} e_{j_s}$ for the empirical frequencies,
$$
  \frac{\alpha(t) - \alpha(0)}{t} = x(t) A, \qquad
  \frac{\beta(t) - \beta(0)}{t}  = A y(t).
$$

The central quantity is the **cumulative duality gap**
$$
  \mu(t) := \max_i \beta^i(t) - \min_j \alpha^j(t).
$$

## Statement

**Lemma (Robinson 1951).** For every matrix $A$ and every $\varepsilon > 0$,
there exists $s_0 = s_0(A, \varepsilon)$ such that
$$
  \mu(t) \le \varepsilon \cdot t, \quad \forall t \ge s_0,
$$
for every admissible sequence on $A$.

Equivalently, $\mu(t) = o(t)$, uniformly over admissible sequences.

## Proof

By induction on the matrix size $N := m + n$.

**Base** $N = 2$ (i.e., a $1 \times 1$ matrix): the entry is a constant $a$,
so $\alpha(t) = \alpha(0) + t \cdot a$ and $\beta(t) = \beta(0) + t \cdot a$.
Admissibility (i) gives $\beta(0) = \alpha(0)$, hence $\mu(t) \equiv 0$.

**Inductive step.** Assume the lemma for every strict submatrix of $A$ and
fix $\varepsilon > 0$. Set $\eta := \varepsilon / 3$. The proof orchestrates the
three sub-lemmas, then applies the pasting lemma with $\varepsilon$ replaced by
$2\eta = 2\varepsilon/3$ (this is the cleaner constant choice — see Note at end).

1. **Submatrix bound from the IH.** For every strict submatrix $A' \subsetneq A$,
   the inductive hypothesis supplies $s(A', \eta)$ such that $\mu_{A'}(t) \le \eta t$
   for every admissible sequence on $A'$ and every $t \ge s(A', \eta)$. There
   are finitely many strict submatrices, so
   $$
     t^* \;:=\; \max\!\left( \max_{A' \subsetneq A} s(A', \eta),\; \tfrac{6 \|A\|}{\varepsilon} \right)
   $$
   is finite. (The second argument forces $2\|A\|/t^* \le \eta$, which is needed
   to control the pasting residual.)

2. **Window dichotomy on every $[s, s + t^*]$.** Either:

   - **(a)** every row $i \in I$ and every column $j \in J$ is *useful* in
     $[s, s + t^*]$ (i.e., each appears in $I(\beta(\cdot))$ or
     $J(\alpha(\cdot))$ at some step inside the window). By
     [[game_theory.strategic_game.zero_sum.learning.robinson_admissible_lemma.useful_window]] —
     which internally uses
     [[game_theory.strategic_game.zero_sum.learning.robinson_admissible_lemma.bracket_invariant]] —
     $$
       \mu(s + t^*) \;\le\; 4 t^* \|A\|
     $$
     (an *absolute* endpoint bound, independent of $\mu(s)$); **or**

   - **(b)** some row or column is not useful. By
     [[game_theory.strategic_game.zero_sum.learning.robinson_admissible_lemma.subgame_reduction]]
     the window is governed by admissible play on a strict submatrix $A'$, so
     the submatrix bound from step 1 applies. Combined with admissibility's
     $2\|A\|$ per-step Lipschitz control on $\mu$, this gives
     $$
       \mu(s + t^*) - \mu(s) \;\le\; \eta t^* + 2 \|A\|
     $$
     (an *increment* bound).

3. **Pasting via Euclidean division.** Write $t = q t^* + r$ with $0 \le r < t^*$.
   Apply
   [[game_theory.strategic_game.zero_sum.learning.robinson_admissible_lemma.induction_step]] with
   $\varepsilon_{\text{step}} := 2\eta = 2\varepsilon/3$ (so that the step's
   "$\frac{\varepsilon_{\text{step}} t^*}{2}$" matches the subgame-case increment
   $\eta t^*$ from step 2). The pasting lemma yields, for all $t \ge t^*$,
   $$
     \mu(t) \;\le\; 6 t^* \|A\|
       \;+\; \tfrac{\varepsilon_{\text{step}}\, t}{2}
       \;+\; \tfrac{2 \|A\|\, t}{t^*}
     \;=\; 6 t^* \|A\| \;+\; \tfrac{\varepsilon t}{3} \;+\; \tfrac{2 \|A\|\, t}{t^*}.
   $$

4. **Constant absorption.** By the choice $t^* \ge 6\|A\|/\varepsilon$,
   the last term $\frac{2\|A\| t}{t^*} \le \frac{\varepsilon t}{3}$. Hence
   $$
     \mu(t) \;\le\; 6 t^* \|A\| + \tfrac{2 \varepsilon t}{3}.
   $$
   Setting
   $$
     s_0 \;:=\; \max\!\left(t^*,\; \tfrac{18\, t^* \|A\|}{\varepsilon}\right),
   $$
   the residual $6 t^* \|A\| \le \frac{\varepsilon t}{3}$ for every $t \ge s_0$,
   giving the stated bound $\mu(t) \le \varepsilon t$. $\square$

## Note on the constant choice

The pasting lemma's "natural" constant ladder produces an end bound of
$\frac{3 \varepsilon_{\text{step}}}{2} t$ for $t$ large enough. Solving
$\frac{3 \varepsilon_{\text{step}}}{2} = \varepsilon$ for the step's $\varepsilon_{\text{step}}$
gives $\varepsilon_{\text{step}} = 2\varepsilon/3$, hence $\eta = \varepsilon_{\text{step}}/2 = \varepsilon/3$
for the IH (since the subgame-reduction increment uses the IH's $\eta$ directly).
A looser choice such as $\eta = \varepsilon/4$ (with $\varepsilon_{\text{step}} = \varepsilon/2$)
also works and gives the cleaner $\mu(t) \le \frac{3 \varepsilon}{4} t \le \varepsilon t$
bound, at the cost of slightly larger $t^*$ and $s_0$. Either is fine; we
record the tighter $\varepsilon/3$ choice for definiteness.

## Consequence

Combined with the trivial bracket
$\min_j x(t)Ay \le \underline v(A) \le \overline v(A) \le \max_i x(t) A^i$,
the lemma yields the existence of a value $v(A) = \underline v = \overline v$
and gives that every accumulation point of $(x(t), y(t))$ is an optimal-strategy
pair. This is the content of
[[game_theory.strategic_game.zero_sum.learning.fictitious_play_convergence]].

For the Cesàro average payoff statement
$\frac1n \sum_{p \le n} A_{i_p, j_p} \to v$, see the independent telescoping
argument in
[[game_theory.strategic_game.zero_sum.learning.cesaro_payoff_from_robinson]].

## References

- [Robinson 1951] J. Robinson, "An iterative method of solving a game",
  *Annals of Mathematics* 54 (1951), 296–301.
- [MFoGT, Section 2.8, Exercise 12] Laraki, Renault, and Sorin, *Mathematical
  Foundations of Game Theory*.
  Hint-decomposition of Robinson's proof into the four internal lemmas cited
  above.
