---
id: game_theory.strategic_game.zero_sum.learning.no_internal_regret_correlated_convergence
primary_topic: game_theory.zero_sum
topics:
  - game_theory.zero_sum
  - game_theory.zero_sum.learning
title: No Internal Regret Converges To Correlated Equilibrium
kind: theorem
status: staged
uses:
  - game_theory.strategic_game.zero_sum.learning.internal_regret
  - game_theory.strategic_game.zero_sum.learning.no_c_regret_set
  - game_theory.strategic_game.correlated.correlated_equilibrium
lean:
  modules:
    - EconCSLib.GameTheory.StrategicGame.NoRegret.EmpiricalDistribution
    - EconCSLib.GameTheory.StrategicGame.NoRegret.Process
  declarations:
    - StrategicGame.noInternalRegret_empiricalDistribution_approaches_playerSet
    - StrategicGame.NoRegretProbability.noInternalRegret_empiricalDistribution_approaches_playerSet_ae
    - StrategicGame.allPlayersNoInternalRegretSet_eq_CED
    - StrategicGame.noInternalRegret_allPlayers_empiricalDistribution_approaches_CED
    - StrategicGame.NoRegretProbability.noInternalRegret_allPlayers_empiricalDistribution_approaches_CED_ae
    - StrategicGame.NoRegretProbability.allPlayersInternalRegret_empiricalDistribution_approaches_CED_ae
    - StrategicGame.NoRegretProbability.correlatedEquilibriumDistributions_nonempty_of_internalRegretProcess
verification:
  statement: accepted
  proof: accepted
  alignment: aligned
tags:
  - strategic-game
  - learning
  - regret
  - correlated-equilibrium
  - convergence
---

# No Internal Regret Converges To Correlated Equilibrium

In repeated play of a finite strategic game, suppose every player follows a
procedure with no internal regret. Then the empirical distribution of realized
action profiles approaches the set of correlated-equilibrium distributions.

## Proof Sketch

For each player $i$ and each replacement pair $a_i\mapsto b_i$, the corresponding
internal-regret inequality can be written as
$$
  \sum_{a_{-i}} q(a_i,a_{-i})
  (g_i(b_i,a_{-i})-g_i(a_i,a_{-i}))\le 0,
$$
where $q$ is the empirical distribution. These are exactly the obedience
inequalities for a correlated equilibrium. Since there are finitely many such
linear inequalities, vanishing positive internal regret for all players forces
the empirical distributions toward their common feasible set.

The generated-process theorem constructs the simultaneous joint action kernel
as the product of the players' prescribed mixed actions. Conditional on the
past, it averages each player's internal-regret vector over the opponents'
fresh actions and uses invariant-measure orthogonality before applying the
almost-sure Blackwell argument. This is the product-mixture calculation needed
for simultaneous fresh draws. The same construction also yields nonemptiness
of the correlated-equilibrium set.

## References

- [MFoGT, Chapter 7, Section 7.3] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. If each player has no internal regret, empirical distributions converge to the correlated-equilibrium set.
