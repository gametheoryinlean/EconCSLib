---
id: game_theory.strategic_game.zero_sum.learning.no_c_regret_set
primary_topic: game_theory.zero_sum
topics:
  - game_theory.zero_sum
  - game_theory.zero_sum.learning
title: No-Comparison-Regret Set
kind: definition
status: staged
uses:
  - game_theory.strategic_game.zero_sum.learning.internal_regret
  - game_theory.strategic_game.zero_sum.learning.hannan_set
lean:
  modules:
    - EconCSLib.GameTheory.StrategicGame.NoRegret.EmpiricalDistribution
  declarations:
    - StrategicGame.comparisonGain
    - StrategicGame.NoCRegretSet
    - StrategicGame.noCRegretSet_subset_hannanSet
    - StrategicGame.noInternalRegret_empiricalDistribution_approaches_playerSet
    - StrategicGame.NoRegretProbability.noInternalRegret_empiricalDistribution_approaches_playerSet_ae
    - StrategicGame.NoRegretProbability.internalRegretMatchingStrategy_empiricalDistribution_approaches_playerSet_ae
verification:
  definition: accepted
  proof: accepted
  alignment: aligned
tags:
  - strategic-game
  - learning
  - internal-regret
  - correlated-equilibrium
---

# No-Comparison-Regret Set

For a joint distribution $z$ and two actions $j,k$ of the player, define
$$
  C(j,k)(z)=\sum_\ell z(j,\ell)
    \bigl(F(k,\ell)-F(j,\ell)\bigr).
$$
The no-$C$-regret set consists of the distributions for which
$C(j,k)(z)\le 0$ for every ordered pair $(j,k)$, as in MFoGT's
no-comparison-regret definition. Summing the comparison gains over the played
action $j$ gives the fixed-action external-regret inequality, so the
no-$C$-regret set is contained in the Hannan set.

## References

- [MFoGT, Definition 7.3.15] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Playerwise no-comparison-regret set and its inclusion in the Hannan set.
