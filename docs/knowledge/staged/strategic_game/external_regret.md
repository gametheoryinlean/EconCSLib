---
id: game_theory.strategic_game.zero_sum.learning.external_regret
primary_topic: game_theory.zero_sum
topics:
  - game_theory.zero_sum
  - game_theory.zero_sum.learning
title: External Regret
kind: definition
status: staged
uses:
  - game_theory.strategic_game.strategic_game
lean:
  modules:
    - EconCSLib.GameTheory.StrategicGame.NoRegret.External
  declarations:
    - StrategicGame.externalRegretStage
    - StrategicGame.averageExternalRegret
    - StrategicGame.HasNoExternalRegret
    - StrategicGame.hasNoExternalRegret_iff_maximalPositiveAverageExternalRegret
    - StrategicGame.hasNoExternalRegret_iff_tendsto_maximalPositiveAverageExternalRegret_zero
    - StrategicGame.NoRegretProbability.HasNoExternalRegretAE
    - StrategicGame.NoRegretProbability.HasNoExternalRegretOnGeneratedProcessesAE
verification:
  definition: accepted
  proof: not_applicable
tags:
  - strategic-game
  - learning
  - regret
---

# External Regret

In repeated play of a finite strategic game, the external regret of player $i$
compares the realized payoff to the payoff that would have been obtained by
using one fixed action throughout the same history.

For a realized action history $(a^1,\ldots,a^n)$, the external regret against a
fixed alternative action $b_i\in A_i$ is
$$
  \frac1n\sum_{t=1}^n
  (g_i(b_i,a_{-i}^t)-g_i(a_i^t,a_{-i}^t)).
$$
A realized path has no external regret if the positive part of this quantity
converges to $0$ for every fixed alternative action. A randomized procedure
has no external regret in MFoGT's sense when this holds
almost surely against every admissible payoff process.

MSZ writes the same no-regret condition as
`realized payoff - fixed-expert payoff` having nonnegative lower limit. Thus
the present `alternative - realized` convention is exactly its negative. The
associated approachability proof likewise replaces MSZ's nonnegative orthant
by the nonpositive orthant.

External regret is weaker than internal regret: it tests only constant
counterfactual actions, not recommendation-contingent replacements.

## References

- [MFoGT, Chapter 7, Section 7.3] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. No-external-regret procedures in repeated play.
- [MSZ, Chapter 14, Def. 14.42, Thm. 14.44, and Eqs. 14.101--14.103] Maschler, Solan, and Zamir, *Game Theory*. Expert regret and its approachability proof, in the sign-dual nonnegative-orthant convention.
