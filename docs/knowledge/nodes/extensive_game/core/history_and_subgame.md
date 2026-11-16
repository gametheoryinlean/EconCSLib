---
id: game_theory.extensive_game.core.history_and_subgame
title: History And Subgame
kind: definition
status: formalized
primary_topic: game_theory.extensive_game
topics:
  - game_theory.extensive_game
  - game_theory.extensive_game.core
uses:
  - game_theory.extensive_game.core.game_tree
lean:
  modules:
    - EconCSLib.GameTheory.ExtensiveGame.Execution.History
    - EconCSLib.GameTheory.ExtensiveGame.Observed.Game
  declarations:
    - Arena.HistoryFrom
    - ExtensiveGame.ObservedGame.IsContinuationOf
    - ExtensiveGame.ObservedGame.IsLawfulSubgameRoot
    - ExtensiveGame.ObservedGame.SubgameSystem
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
tags:
  - extensive-game
  - subgame
---

# History And Subgame

An `Arena.HistoryFrom init` is a typed finite sequence of legal dependent
actions and successor states starting at the initial state. For an
`ObservedGame`, `IsContinuationOf root current` states reachability of one
complete history from another in the history unfolding.

A standard subgame is not obtained by state rerooting alone. Its root must
satisfy `IsLawfulSubgameRoot`: a proper player root is singleton in its
information set, and every information set reached after entry stays inside
the continuation. A `SubgameSystem` packages a nonempty selection of such
roots. The historical `ExtensiveGame.subgameAt` operation only changes the
state root and is therefore not used as the formal witness for this node.

## References

- [MFoGT, Section 6.2.1] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. History of a position and subgame G[p].
