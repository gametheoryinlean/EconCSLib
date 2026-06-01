---
id: game_theory.strategic_game.zero_sum.learning.robinson_admissible_lemma.subgame_reduction
title: Subgame Reduction For Non-Useful Indices
kind: lemma
status: admitted
primary_topic: game_theory.zero_sum
topics:
  - game_theory.zero_sum
  - game_theory.zero_sum.learning
uses:
  - game_theory.strategic_game.zero_sum.learning.fictitious_play
source:
  spans:
    - artifact: mfogt
      locator: "Section 2.8, Exercise 12 part (3)(b)"
      format: section
      note: "Reduction of a non-useful-row window to admissible play on a strict submatrix"
verification:
  statement: accepted
  proof: gap
tags:
  - zero-sum
  - fictitious-play
  - robinson
---

# Subgame Reduction For Non-Useful Indices

A reduction step used by
[[game_theory.strategic_game.zero_sum.learning.robinson_admissible_lemma]] inside the main
induction's "some row/column is not useful" case. It is the mechanism by which
the inductive hypothesis on strict submatrices is invoked.

## Setup

For an admissible sequence on $A \in \mathbb{R}^{m \times n}$ and a window
$[s, s+t^*] \subseteq \mathbb{N}$, define usefulness as in
[[game_theory.strategic_game.zero_sum.learning.robinson_admissible_lemma.useful_window]].

For a subset $I' \subseteq I$ let $A|_{I' \times J}$ denote the submatrix
formed by the rows in $I'$. Admissibility on $A|_{I' \times J}$ uses the same
condition (i)–(ii) but with $I$ replaced by $I'$ throughout.

## Statement

Suppose row $i \in I$ is **not** useful in $[s, s+t^*]$, i.e.,
$i \notin I(\beta(t))$ for every $t \in [s, s+t^*]$. Let
$I' := I \setminus \{i\}$ and $A' := A|_{I' \times J}$.

Then the trajectory $(\alpha(t), \beta(t)|_{I'})_{t \in [s, s+t^*]}$, with
suitable initial-condition adjustment of size at most $2\|A\|$, is an
admissible sequence on $A'$. Consequently, if the lemma
[[game_theory.strategic_game.zero_sum.learning.robinson_admissible_lemma]] holds for $A'$ with
constant $s'(A', \varepsilon/2)$ such that
$\mu'(t) \le (\varepsilon/2) t$ for $t \ge s'$, and if
$t^* \ge s'(A', \varepsilon/2)$, then
$$
  \mu(s + t^*) - \mu(s) \;\le\; \frac{\varepsilon t^*}{2} + 2\|A\|.
$$

The same statement holds with rows and columns swapped (some $j \in J$ not
useful, restricting to $J' := J \setminus \{j\}$ and $A|_{I \times J'}$).

## Proof

Since $i$ is not useful in $[s, s+t^*]$, at every step $t+1 \in [s+1, s+t^*]$
the chosen index $i_{t+1} \in I(\beta(t))$ lies in $I'$. Therefore:

- the component $\beta^i$ is **not updated** anywhere in the window;
- every update $\alpha(t+1) = \alpha(t) + e_{i_{t+1}}^T A$ uses
  $i_{t+1} \in I'$, so the row used belongs to $A'$;
- $j_{t+1} \in J(\alpha(t))$ depends only on $\alpha$ (unchanged formula).

Define $\beta'(t) := \beta(t)|_{I'} \in \mathbb{R}^{m-1}$ and
$\alpha'(t) := \alpha(t) \in \mathbb{R}^n$ for $t \in [s, s+t^*]$. Then
$(\alpha', \beta')$ evolves on the window exactly by the admissible rule
for $A'$, except possibly for the initial bracket condition.

For the initial bracket on $A'$ at time $s$: we need
$\min_k \alpha'^k(s) = \max_k \beta'^k(s)$. This may not hold exactly for the
inherited values, but shifting both vectors by a common constant restores it
(admissibility is translation-invariant in this sense), and the constant
absorbed at the end contributes at most $2\|A\|$ to the gap $\mu(s+t^*) -
\mu(s)$ — the maximum single-step jump within the window can deviate by this
margin once.

Now apply the lemma on $A'$ with $\varepsilon/2$: there exists
$s'(A', \varepsilon/2)$ such that $\mu'(t-s) \le (\varepsilon/2)(t-s)$ for
$t - s \ge s'$. Choosing the parent's $t^*$ to dominate $s'(A', \varepsilon/2)$
gives at the window endpoint
$$
  \mu'(t^*) \le \frac{\varepsilon t^*}{2}.
$$

Finally relate $\mu$ and $\mu'$ on the window. Because $i \notin I(\beta(t))$
throughout, $\max_k \beta^k(t) = \max_{k \in I'} \beta^k(t) = \max \beta'(t)$
for every $t \in [s, s+t^*]$. Since $\alpha$ is unchanged,
$\min_j \alpha^j(t) = \min_j \alpha'^j(t)$ as well. Hence $\mu(t) = \mu'(t)$ on
the window, and combining with the $2\|A\|$ initial-bracket adjustment:
$$
  \mu(s+t^*) - \mu(s) \le \frac{\varepsilon t^*}{2} + 2\|A\|.
$$
$\square$

## Note

The strict submatrix $A'$ has size $(m-1) + n = m + n - 1 < m + n$, which is
exactly the inductive parameter in the main lemma. This is why the induction
closes.

## References

- [MFoGT, Section 2.8, Exercise 12 part (3)(b)] Laraki, Renault, and Sorin,
  *Mathematical Foundations of Game Theory*. Non-useful-row reduction to a
  strict submatrix.
