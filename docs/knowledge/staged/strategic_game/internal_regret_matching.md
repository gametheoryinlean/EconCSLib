---
id: game_theory.strategic_game.zero_sum.learning.internal_regret_matching
primary_topic: game_theory.zero_sum
topics:
  - game_theory.zero_sum
  - game_theory.zero_sum.learning
title: Invariant-Measure Regret Matching Has No Internal Regret
kind: theorem
status: staged
uses:
  - game_theory.strategic_game.zero_sum.learning.internal_regret
  - game_theory.strategic_game.zero_sum.approachability.blackwell_projection_criterion
lean:
  modules:
    - EconCSLib.GameTheory.StrategicGame.NoRegret.Internal
    - EconCSLib.GameTheory.StrategicGame.NoRegret.Process
    - EconCSLib.GameTheory.StrategicGame.ZeroSum.StochasticMatrix
  declarations:
    - StrategicGame.IsInvariantMeasureFor
    - EconCSLib.StrategicGame.MatrixGame.exists_invariant_measure_nonneg
    - StrategicGame.invariantMeasure_internalRegret_orthogonal
    - StrategicGame.internalRegretMatchingStrategy
    - StrategicGame.NoRegretProbability.internalRegretMatchingStrategy_hasNoInternalRegretOnGeneratedProcessesAE
    - StrategicGame.NoRegretProbability.internalRegretMatchingStrategy_hasNoInternalRegretAE_against_predictable
verification:
  statement: accepted
  proof: accepted
  alignment: aligned
tags:
  - strategic-game
  - learning
  - internal-regret
  - invariant-measure
---

# Invariant-Measure Regret Matching Has No Internal Regret

Form the nonnegative matrix of positive average internal regrets. At each
stage, play an invariant probability measure $\mu$ satisfying
$$
  \sum_k\mu_k A_{k\ell}
  =\mu_\ell\sum_k A_{\ell k}.
$$
Every finite nonnegative matrix admits such a measure. The resulting online
rule has no internal regret almost surely against every bounded
nonanticipating payoff process. This is MFoGT's invariant-measure
internal-regret result.

The accompanying orthogonality identity needs only the displayed
invariance equation. Nonnegativity is required for existence of the invariant
measure, not for that algebraic identity itself; the formal API reflects this
strictly weaker hypothesis.

## References

- [MFoGT, Lemma 7.3.6 and Proposition 7.3.7] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Invariant-measure internal-regret procedure.
