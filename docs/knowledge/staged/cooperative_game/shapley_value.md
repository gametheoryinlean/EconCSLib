---
id: game_theory.cooperative_game.shapley_value
title: Shapley Value
kind: definition
status: staged
primary_topic: game_theory.cooperative_game
topics:
  - game_theory.cooperative_game
  - game_theory.cooperative_game.shapley_value
uses:
  - game_theory.cooperative_game.marginal_contribution
  - game_theory.cooperative_game.shapley_axioms
lean:
  modules:
    - EconCSLib.GameTheory.CoalitionalGame.ShapleyValue
  declarations:
    - CoalitionalGame.shapleyValue
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
tags:
  - coalitional-game
  - shapley-value
---

# Shapley Value

The **Shapley value** assigns to each player their average marginal
contribution over all possible orders in which the grand coalition can form.
Equivalently,
$$
  \operatorname{Sh}_i(v)
  =
  \sum_{S \subseteq N\setminus\{i\}}
  \frac{|S|!(|N|-|S|-1)!}{|N|!}
  \bigl(v(S \cup \{i\})-v(S)\bigr).
$$

The factorial coefficient is the probability that exactly the players in
$S$ precede $i$ in a uniformly random ordering of $N$.

## Lean Status

Lean defines this formula as `CoalitionalGame.shapleyValue`. The main
properties of the formula are separate theorem nodes: efficiency,
uniqueness, and convex-core membership.

## References

- [MSZ Ch.18, Def 18.14 and Thm 18.17] Maschler, Solan, Zamir,
  *Game Theory*.
