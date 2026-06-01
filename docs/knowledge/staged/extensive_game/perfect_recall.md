---
id: game_theory.extensive_game.imperfect_information.perfect_recall
primary_topic: game_theory.extensive_game
topics:
  - game_theory.extensive_game
  - game_theory.extensive_game.imperfect_information
title: Perfect Recall
kind: definition
status: staged
uses:
  - game_theory.extensive_game.imperfect_information.information_set
verification:
  definition: accepted
  proof: not_applicable
tags:
  - extensive-game
  - perfect-recall
---

# Perfect Recall

An extensive game has perfect recall for player $i$ if, whenever two nodes $x$ and
$y$ lie in the same information set of player $i$, the earlier information sets of
player $i$ encountered on histories leading to $x$ and $y$ match, and the player's
own earlier actions also match as actions in the corresponding equivalence classes.

Informally, player $i$ never forgets what they knew or which actions they
previously chose.

## References

- [MFoGT, Def. 6.3.3] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. A player remembers what they knew and did in the past.
