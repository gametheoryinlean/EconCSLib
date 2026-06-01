---
id: game_theory.strategic_game.dominance.rationalizable_strategy
primary_topic: game_theory.strategic_game
topics:
  - game_theory.strategic_game
  - game_theory.strategic_game.dominance
title: Rationalizable Strategy
kind: definition
status: staged
uses:
  - game_theory.strategic_game.best_response
lean:
  modules:
    - EconCSLib.GameTheory.StrategicGame.IESDS
  declarations:
    - StrategicGame.IsRationalizable
verification:
  definition: accepted
  proof: not_applicable
  alignment: pending
tags:
  - strategic-game
  - rationalizability
  - best-response
---

# Rationalizable Strategy

In a compact continuous game, define
$$
  S_i(1)=BR_i(S_{-i})
$$
and inductively
$$
  S_i(k+1)=BR_i(S_{-i}(k)).
$$
The rationalizable strategy set of player $i$ is
$$
  S_i^\infty=\bigcap_{k\ge 1}S_i(k).
$$
A profile $s$ is rationalizable if $s_i\in S_i^\infty$ for every player $i$.

## Lean scope

Lean's `IsRationalizable` is defined as surviving iterated elimination of
**strictly dominated** strategies (IESDS — see
[[node:game_theory.strategic_game.dominance.iterated_elimination]]), whereas the
best-response definition above (iterated elimination of strategies that are
never a best response) is the MFoGT formulation. The two coincide for finite
two-player games (Pearce's lemma) but differ in general. The Lean port
currently formalizes the IESDS version only, so this best-response node stays
`pending` until the best-response characterization is linked or proved.

## References

- [MFoGT, Section 4.4] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Rationalizability as iterated elimination of strategies that are not best responses.
