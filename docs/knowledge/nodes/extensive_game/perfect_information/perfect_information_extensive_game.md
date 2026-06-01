---
id: game_theory.extensive_game.perfect_information.perfect_information_extensive_game
title: Finite Extensive Game With Perfect Information
kind: definition
status: formalized
primary_topic: game_theory.extensive_game
topics:
  - game_theory.extensive_game
  - game_theory.extensive_game.perfect_information
lean:
  modules:
    - EconCSLib.GameTheory.ExtensiveGame.Basic
  declarations:
    - Arena
    - ExtensiveGame
    - ExtensiveGame.isPlayerState
    - ExtensiveGame.isTerminal
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
tags:
  - extensive-game
  - perfect-information
---

# Finite Extensive Game With Perfect Information

A finite extensive form game with perfect information consists of:

1. a finite nonempty player set $I$;
2. a finite tree of nodes $Z$ with origin $\theta$ and predecessor map;
3. terminal nodes $R$ and decision positions $P=Z\setminus R$;
4. a successor set $S(p)$ for each decision position $p$;
5. a partition $(P_i)_{i\in I}$ of decision positions by the player who moves;
6. payoff functions $g_i:R\to\mathbb R$.

Play starts at $\theta$, follows successor choices at decision positions, stops at a
terminal node $r\in R$, and gives player $i$ payoff $g_i(r)$.

## References

- [MFoGT, Section 6.2.1] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Description of a finite extensive form game with perfect information.
