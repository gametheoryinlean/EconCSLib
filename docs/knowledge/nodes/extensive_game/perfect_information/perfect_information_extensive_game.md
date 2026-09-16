---
id: game_theory.extensive_game.perfect_information.perfect_information_extensive_game
title: Finite Perfect-Information GameTree Presentation
kind: definition
status: formalized
primary_topic: game_theory.extensive_game
topics:
  - game_theory.extensive_game
  - game_theory.extensive_game.perfect_information
lean:
  modules:
    - EconCSLib.GameTheory.ExtensiveGame.GameTree
    - EconCSLib.GameTheory.ExtensiveGame.Compiler.GameTreeOccurrenceObserved
  declarations:
    - GameTree
    - GameTree.toOccurrenceObservedGame
    - GameTree.toOccurrenceObservedGame_perfectInformation
    - GameTree.occurrenceCompleteSubgameSystem
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
tags:
  - extensive-game
  - perfect-information
---

# Finite Perfect-Information GameTree Presentation

The canonical finite, no-chance frontend is an inductive `GameTree N U`:
leaves store payoff vectors and every decision node stores its mover and a
nonempty finite list of child trees. Finiteness and termination are structural;
the carrier does not require `N` or `U` themselves to be finite.

`GameTree.toOccurrenceObservedGame` compiles each node occurrence to a typed
history and uses the full occurrence as its information state. The theorem
`toOccurrenceObservedGame_perfectInformation` proves that every player
information set is singleton, and `occurrenceCompleteSubgameSystem` selects
all history occurrences as the complete lawful subgame system.

This node does not claim that the more general `Arena` or `ExtensiveGame`
records are finite or perfect-information structures; those records
intentionally support infinite state spaces and do not carry an information
partition.

## References

- [MFoGT, Section 6.2.1] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Description of a finite extensive form game with perfect information.
