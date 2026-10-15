---
id: game_theory.strategic_game.bayesian.bayesian_equilibrium
primary_topic: game_theory.strategic_game
topics:
  - game_theory.strategic_game
  - game_theory.strategic_game.bayesian_correlated
title: Bayesian Equilibrium
kind: definition
status: staged
uses:
  - game_theory.strategic_game.bayesian.bayesian_strategy
  - game_theory.strategic_game.nash_equilibrium
lean:
  modules:
    - EconCSLib.GameTheory.StrategicGame.BayesianGame.Basic
  declarations:
    - StrategicGame.PrimitiveBayesianGame.IsBayesianEquilibrium
    - StrategicGame.PrimitiveBayesianGame.toReduced_isBayesianEquilibrium
    - StrategicGame.BayesianGame.IsBayesianEquilibrium
    - StrategicGame.BayesianGame.IsExAnteNashEquilibrium
    - StrategicGame.BayesianGame.HasFullTypeSupport
    - StrategicGame.BayesianGame.IsInterimBayesianEquilibrium
    - StrategicGame.BayesianGame.conditionalInterimBehaviorPayoffOfMixedAction
    - StrategicGame.BayesianGame.IsConditionalInterimPureActionBestResponse
    - StrategicGame.BayesianGame.interimBehaviorPayoffOfMixedAction_eq_sum_pure
    - StrategicGame.BayesianGame.isConditionalInterimBestResponse_iff_pureAction
    - StrategicGame.BayesianGame.isInterimBayesianEquilibrium_iff_pureAction
    - StrategicGame.BayesianGame.behavioralExpectedPayoff_eq_sum_typeMarginal_mul_conditionalInterim
    - StrategicGame.BayesianGame.isBayesianEquilibrium_iff_conditionalInterimBestResponses
    - StrategicGame.BayesianGame.isExAnteNashEquilibrium_iff_isInterimBayesianEquilibrium_of_fullTypeSupport
    - StrategicGame.BayesianGame.isExAnteNashEquilibrium_iff_allConditionalInterimPureActionBestResponses_of_fullTypeSupport
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
tags:
  - strategic-game
  - bayesian-game
  - bayesian-equilibrium
---

# Bayesian Equilibrium

A Bayesian strategy profile $\sigma$ is a Bayesian equilibrium if no player can
improve expected payoff by replacing their type-contingent strategy while the
other players keep theirs fixed.

In ex-ante form, for every player $i$ and every alternative type-contingent
strategy $\tau_i:T_i\to\Delta(A_i)$,
$$
  \mathbb E_p[g_i(\sigma_i(t_i),\sigma_{-i}(t_{-i}),t)]
  \ge
  \mathbb E_p[g_i(\tau_i(t_i),\sigma_{-i}(t_{-i}),t)].
$$

For every type with positive marginal probability, this is equivalent to the
interim condition that after observing $t_i$, the prescribed mixed action is
optimal against the conditional distribution of other players' types and
actions. Zero-probability types impose no ex-ante restriction. MFoGT calls the
own-type-conditioned maximization "ex-post" in this passage; the standard term
used here is "interim".

MSZ states the interim inequalities against every pure action. The reusable
Lean predicate quantifies over all mixed actions; a formal linearity theorem
now proves that these two formulations are equivalent in the finite model.

The positivity qualification is necessary: an ex-ante equilibrium cannot
restrict behavior at a type that occurs with probability zero. The Lean API
also offers a convention-totalized theorem after defining every null-type
conditional payoff to be zero, but the positive-type theorem is the
source-facing mathematical statement.

The naming conventions of the two sources differ. MFoGT calls the ex-ante
no-whole-plan-deviation predicate Bayesian equilibrium. MSZ calls that
predicate Nash equilibrium, reserves Bayesian equilibrium for the interim
constraints, and proves their equivalence under full type support. The Lean
synonyms and predicates listed above make this distinction explicit. Relative
to MSZ, every statement here is the fixed-action-family specialization
$A_i(t_i)=A_i$; MSZ allows the action set to depend on the player's type.

## References

- [MFoGT, Chapter 7, Section 7.4] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Bayesian equilibrium as the Nash-style equilibrium concept for Bayesian games.
- [MSZ, Chapter 9, Defs. 9.46 and 9.49, Thm. 9.53] Maschler, Solan, and Zamir, *Game Theory*. Ex-ante Nash equilibrium, interim Bayesian equilibrium, and their equivalence under positive type marginals.
