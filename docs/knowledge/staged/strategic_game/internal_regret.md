---
id: game_theory.strategic_game.zero_sum.learning.internal_regret
primary_topic: game_theory.zero_sum
topics:
  - game_theory.zero_sum
  - game_theory.zero_sum.learning
title: Internal Regret
kind: definition
status: staged
uses:
  - game_theory.strategic_game.zero_sum.learning.external_regret
  - game_theory.strategic_game.correlated.correlated_equilibrium
lean:
  modules:
    - EconCSLib.GameTheory.StrategicGame.NoRegret.Internal
    - EconCSLib.GameTheory.StrategicGame.ZeroSum.StochasticMatrix
  declarations:
    - StrategicGame.internalRegretStage
    - StrategicGame.averageInternalRegret
    - StrategicGame.HasNoInternalRegret
    - StrategicGame.maximalPositiveAverageInternalRegret
    - StrategicGame.hasNoInternalRegret_iff_maximalPositiveAverageInternalRegret
    - StrategicGame.hasNoInternalRegret_iff_tendsto_maximalPositiveAverageInternalRegret_zero
    - StrategicGame.IsInvariantMeasureFor
    - StrategicGame.invariantMeasure_internalRegret_orthogonal
    - EconCSLib.StrategicGame.MatrixGame.exists_invariant_measure_nonneg
    - StrategicGame.NoRegretProbability.HasNoInternalRegretAE
    - StrategicGame.NoRegretProbability.HasNoInternalRegretOnGeneratedProcessesAE
verification:
  definition: accepted
  proof: not_applicable
tags:
  - strategic-game
  - learning
  - regret
  - correlated-equilibrium
---

# Internal Regret

Internal regret compares realized play with a counterfactual rule that replaces
one action by another whenever the first action was played.

For player $i$ and actions $a_i,b_i\in A_i$, the internal regret from replacing
$a_i$ by $b_i$ along a realized history is
$$
  \frac1n\sum_{t:a_i^t=a_i}
  (g_i(b_i,a_{-i}^t)-g_i(a_i,a_{-i}^t)).
$$
A realized path has no internal regret if the positive part of this quantity
converges to $0$ for every ordered pair $(a_i,b_i)$. Since the action set is
finite, this is equivalent to convergence to $0$ of the maximum positive entry
of the entire internal-regret matrix, a finite scalar form equivalent to
[MFoGT, Definition 7.3.5]. A randomized procedure has no internal regret in
MFoGT's sense when this holds almost surely against every admissible payoff
process.

Internal regret is the learning analogue of correlated-equilibrium obedience:
the counterfactual deviation is allowed to depend on the action actually
recommended or played.

## References

- [MFoGT, Chapter 7, Section 7.3] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. No-internal-regret procedures and their connection to correlated equilibria.
