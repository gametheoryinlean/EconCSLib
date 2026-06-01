---
id: game_theory.cooperative_game.balanced_collection
title: Balanced Collection Of Coalitions
kind: definition
status: staged
primary_topic: game_theory.cooperative_game
topics:
  - game_theory.cooperative_game
  - game_theory.cooperative_game.core
uses:
  - game_theory.cooperative_game.tu_game
lean:
  modules:
    - EconCSLib.GameTheory.CoalitionalGame.Core
  declarations:
    - CoalitionalGame.IsBalanced
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
tags:
  - coalitional-game
  - balancedness
---

# Balanced Collection Of Coalitions

A finite collection of coalitions $\mathcal{D}$ is **balanced** if its
coalitions can be assigned positive weights $\delta_S>0$ so that every
player is covered with total weight one:
$$
  \sum_{\substack{S \in \mathcal{D}\\ i \in S}} \delta_S = 1
  \quad\text{for every } i \in N.
$$

The condition says that the weighted incidence vectors of the coalitions in
$\mathcal{D}$ add up to the incidence vector of the grand coalition.

Balanced collections are the combinatorial input to the
Bondareva-Shapley theorem ([[game_theory.cooperative_game.bondareva_shapley]]).

## References

- [MSZ Ch.17, Def 17.11] Maschler, Solan, Zamir, *Game Theory*.
