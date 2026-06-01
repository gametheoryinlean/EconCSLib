---
id: game_theory.extensive_game.equilibrium.completely_mixed_nash_is_subgame_perfect
title: Completely Mixed Nash Is Subgame Perfect
kind: theorem
status: staged
primary_topic: game_theory.extensive_game
topics:
  - game_theory.extensive_game
  - game_theory.extensive_game.imperfect_information
uses:
  - game_theory.extensive_game.equilibrium.reached_subgame_nash_restriction
lean:
  repository: econcslib
  modules:
    - EconCSLib.GameTheory.ExtensiveGame.BehaviorStrategy
  declarations:
    - ExtensiveGame.BehaviorStrategy.IsCompletelyMixed
    - ExtensiveGame.BehaviorProfile.IsCompletelyMixed
    - ExtensiveGame.BehaviorProfile.IsCompletelyMixedWithPositiveReach
    - ExtensiveGame.BehaviorProfile.IsCompletelyMixed.actionProb_pos
    - ExtensiveGame.IsBehaviorSubgamePerfect
    - ExtensiveGame.IsBehaviorNashEq.toSubgamePerfect_of_reachProb_pos
    - ExtensiveGame.IsBehaviorNashEq.toSubgamePerfect_of_isCompletelyMixed
verification:
  statement: accepted
  proof: accepted
  alignment: pending
tags:
  - extensive-game
  - behavioral-strategy
  - nash-equilibrium
  - subgame-perfect-equilibrium
  - completely-mixed
---

# Completely Mixed Nash Is Subgame Perfect

Let $\Gamma$ be an extensive-form game. Every Nash equilibrium in completely
mixed strategies, whether behavior strategies or mixed strategies in the
textbook statement, is a subgame-perfect equilibrium.

## Lean Scope

The current Lean theorem
`ExtensiveGame.IsBehaviorNashEq.toSubgamePerfect_of_isCompletelyMixed`
formalizes the behavior-strategy side in the same finite-fuel, Arena-based
interface used for [MSZ, Theorem 7.5]. Complete mixing is represented by
`ExtensiveGame.BehaviorProfile.IsCompletelyMixed`, and the bridge from complete
mixing to positive reach of every subgame root is packaged as
`ExtensiveGame.BehaviorProfile.IsCompletelyMixedWithPositiveReach`.

Under that positive-reach interface and the existing affine
`ExtensiveGame.ReachedSubgamePayoffTransfer` hypothesis for every subgame root,
the proof is a direct universal application of
`ExtensiveGame.IsBehaviorNashEq.restrictSubgame_of_reachProb_pos`.

The mixed-strategy version and a concrete derivation of positive reach from
finite histories with explicit chance probabilities remain future
strengthenings.

## References

- [MSZ, Cor. 7.7] Maschler, Solan, and Zamir, *Game Theory*. A completely mixed Nash equilibrium is subgame-perfect.
