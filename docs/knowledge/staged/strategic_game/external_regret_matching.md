---
id: game_theory.strategic_game.zero_sum.learning.external_regret_matching
primary_topic: game_theory.zero_sum
topics:
  - game_theory.zero_sum
  - game_theory.zero_sum.learning
title: Proportional Regret Matching Has No External Regret
kind: theorem
status: staged
uses:
  - game_theory.strategic_game.zero_sum.learning.external_regret
  - game_theory.strategic_game.zero_sum.approachability.blackwell_projection_criterion
lean:
  modules:
    - EconCSLib.GameTheory.StrategicGame.NoRegret.External
    - EconCSLib.GameTheory.StrategicGame.NoRegret.Process
  declarations:
    - StrategicGame.expected_externalRegret_orthogonal
    - StrategicGame.externalRegretMatchingStrategy
    - StrategicGame.NoRegretProbability.externalRegretMatchingStrategy_hasNoExternalRegretOnGeneratedProcessesAE
    - StrategicGame.NoRegretProbability.externalRegretMatchingStrategy_hasNoExternalRegretAE_against_predictable
verification:
  statement: accepted
  proof: accepted
  alignment: aligned
tags:
  - strategic-game
  - learning
  - regret-matching
  - approachability
---

# Proportional Regret Matching Has No External Regret

At each stage, choose an action with probability proportional to the positive
part of its current average external regret. If all positive regrets vanish,
use an arbitrary fixed fallback distribution; the formal construction uses
the uniform distribution.

For every bounded nonanticipating payoff process, this rule has no external
regret almost surely. This is MFoGT's proportional-regret result. The formalization gives
both a theorem for any process satisfying the conditional-law hypotheses and
an explicit Ionescu--Tulcea trajectory law against every finite-history
predictable payoff rule.

## Proof Sketch

The expected external-regret vector is orthogonal to the mixed action. With
probabilities proportional to positive regret, this verifies Blackwell's
projection inequality for the negative orthant. Approachability then forces
the maximum positive average regret to zero almost surely.

## References

- [MFoGT, Lemma 7.3.3 and Proposition 7.3.4] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Proportional positive-regret rule.
