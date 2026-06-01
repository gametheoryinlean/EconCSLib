---
id: game_theory.extensive_game.equilibrium.reached_subgame_nash_restriction
title: Reached Subgame Nash Restriction
kind: theorem
status: staged
primary_topic: game_theory.extensive_game
topics:
  - game_theory.extensive_game
  - game_theory.extensive_game.imperfect_information
uses:
  - game_theory.extensive_game.imperfect_information.behavioral_equilibrium
  - game_theory.extensive_game.imperfect_information.reached_information_set
lean:
  repository: econcslib
  modules:
    - EconCSLib.GameTheory.ExtensiveGame.Subgame
    - EconCSLib.GameTheory.ExtensiveGame.BehaviorStrategy
  declarations:
    - ExtensiveGame.BehaviorStrategy
    - ExtensiveGame.BehaviorProfile
    - ExtensiveGame.reachableSubgameAt
    - ExtensiveGame.reachProb
    - ExtensiveGame.expectedPayoff
    - ExtensiveGame.BehaviorStrategy.restrictReachableSubgame
    - ExtensiveGame.BehaviorStrategy.liftReachableSubgame
    - ExtensiveGame.BehaviorProfile.restrictReachableSubgame
    - ExtensiveGame.BehaviorProfile.liftReachableSubgame
    - ExtensiveGame.BehaviorProfile.restrictReachableSubgame_deviate_liftReachableSubgame
    - ExtensiveGame.expectedPayoffFrom_restrictSubgame
    - ExtensiveGame.expectedPayoff_restrictSubgame_init
    - ExtensiveGame.ReachedSubgamePayoffTransfer
    - ExtensiveGame.ReachedSubgamePayoffTransfer.init
    - ExtensiveGame.IsBehaviorNashEq.restrictSubgame_of_reachProb_pos
    - ExtensiveGame.IsBehaviorNashEq.restrictSubgame_init
verification:
  statement: accepted
  proof: accepted
  alignment: pending
tags:
  - extensive-game
  - behavioral-strategy
  - nash-equilibrium
  - subgame-perfect-equilibrium
---

# Reached Subgame Nash Restriction

Let $\Gamma$ be an extensive-form game, let $\sigma^\ast$ be a Nash equilibrium
in mixed strategies or behavior strategies, and let $\Gamma(x)$ be a subgame.
If the probability of reaching $x$ under $\sigma^\ast$ is positive, then the
restriction of $\sigma^\ast$ to $\Gamma(x)$ is a Nash equilibrium of the subgame
$\Gamma(x)$.

## Lean Scope

The Lean target should reuse `ExtensiveGame.subgameAt` for $\Gamma(x)$. A faithful
formalization also needs behavior strategies, reach probabilities, expected
payoffs, profile restriction to a subgame, and a lifting lemma showing that a
profitable deviation in a positive-probability subgame induces a profitable
deviation in the original game.

The current Lean theorem
`ExtensiveGame.IsBehaviorNashEq.restrictSubgame_of_reachProb_pos` proves the
Nash-restriction step from an affine payoff-transfer interface. The root-subgame
special case `ExtensiveGame.IsBehaviorNashEq.restrictSubgame_init` is proved
without this interface. The supporting API now also includes
`ExtensiveGame.reachableSubgameAt`, a subtype subgame whose states are exactly
those reachable from the subgame root, together with local lift lemmas that keep
the original profile unchanged outside that reachable subgame. A later
strengthening can derive the affine payoff-transfer interface for arbitrary
positively reached subgames from finite-history reach probabilities and expected
payoffs.

## References

- [MSZ, Thm. 7.5] Maschler, Solan, and Zamir, *Game Theory*. A Nash equilibrium restricted to a subgame reached with positive probability remains a Nash equilibrium of that subgame.
