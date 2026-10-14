---
id: game_theory.extensive_game.imperfect_information.subroot_subgame
title: Subroot And Subgame In Imperfect-Information Games
kind: definition
status: formalized
primary_topic: game_theory.extensive_game
topics:
  - game_theory.extensive_game
  - game_theory.extensive_game.imperfect_information
uses:
  - game_theory.extensive_game.imperfect_information.information_set
  - game_theory.extensive_game.core.history_and_subgame
lean:
  modules:
    - EconCSLib.GameTheory.ExtensiveGame.Observed.Game
  declarations:
    - ExtensiveGame.ObservedGame.IsLawfulSubgameRoot
    - ExtensiveGame.ObservedGame.SubgameSystem
    - ExtensiveGame.ObservedGame.CompleteSubgameSystem
    - ExtensiveGame.ObservedGame.CompleteSubgameSystem.canonical
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
tags:
  - extensive-game
  - subgame
  - imperfect-information
---

# Subroot And Subgame In Imperfect-Information Games

In an observed extensive game, a history $x$ is a lawful subgame root if:

1. the initial history is admitted as the whole game; otherwise, if a player
   moves at $x$, then $x$ is the unique history in that player's information
   set;
2. every player information set encountered after entering at $x$ is wholly
   contained in the continuation from $x$.

`SubgameSystem` selects a nonempty, possibly conservative collection of lawful
roots. `CompleteSubgameSystem` additionally proves that every lawful root is
selected; its canonical instance exists for every observed game. This
lawfulness is independent of presentation-designated continuation metadata.

## References

- [MFoGT, Def. 6.4.1] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Subroot definition for subgames in perfect-recall extensive games.
