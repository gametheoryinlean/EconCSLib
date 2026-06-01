---
id: game_theory.strategic_game.zero_sum.continuous.monotone_decreasing_values_limit
title: Monotone Decreasing Values Limit
kind: proposition
status: admitted
primary_topic: game_theory.zero_sum
topics:
  - game_theory.zero_sum
  - game_theory.zero_sum.continuous
uses:
  - game_theory.strategic_game.zero_sum.core.value
  - game_theory.strategic_game.zero_sum.continuous.quasi_concavity_semicontinuity
source:
  spans:
    - artifact: mfogt
      locator: "Section 3.5, Exercise 3"
      format: section
      note: "Limit of values for a decreasing family of upper-semicontinuous zero-sum games"
verification:
  statement: accepted
  proof: accepted
tags:
  - zero-sum
  - value
  - limit
---

# Monotone Decreasing Values Limit

Let $G_n=(S,T,f_n)$ be a family of zero-sum games such that:

1. $(f_n)$ is a weakly decreasing sequence of uniformly bounded functions
   $S\times T\to\mathbb R$;
2. each $f_n$ is upper semicontinuous in the first variable;
3. each $G_n$ has a value $v_n$;
4. $S$ is compact.

Let $f=\inf_n f_n$. Then the game $G=(S,T,f)$ has value
$$
  v=\inf_n v_n,
$$
and player 1 has an optimal strategy in $G$.

*Proof.* The values $v_n$ form a decreasing bounded sequence, so
$v=\inf_n v_n$ exists. For each $n$, let $S_n(\varepsilon)$ be the closed set of
strategies in $S$ that guarantee at least $v_n-\varepsilon$ in game $G_n$.
Upper semicontinuity in the first variable and compactness of $S$ make these
sets compact, and monotonicity of the payoffs makes them nested after replacing
$\varepsilon$ by a summable sequence. Compactness gives a common limit strategy
$s^*$. Since $f=\inf_n f_n$, this strategy guarantees at least $v$ in the limit
game. Conversely, every strategy's guarantee in $f$ is bounded above by its
guarantee in each $f_n$, hence by $v_n$; taking the infimum over $n$ gives an
upper bound $v$. Thus $G$ has value $v$ and $s^*$ is optimal for player $1$.

## References

- [MFoGT, Section 3.5, Exercise 3] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Limit of values for a decreasing family of upper-semicontinuous zero-sum games.
