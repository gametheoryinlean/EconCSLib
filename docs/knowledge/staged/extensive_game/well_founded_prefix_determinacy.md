---
id: game_theory.extensive_game.perfect_information.well_founded_prefix_determinacy
primary_topic: game_theory.extensive_game
topics:
  - game_theory.extensive_game
  - game_theory.extensive_game.perfect_information
title: Well-Founded Prefix Determinacy
kind: theorem
status: staged
uses:
  - game_theory.extensive_game.perfect_information.determined_game
verification:
  statement: accepted
  proof: accepted
lean:
  declarations:
    - ExtensiveGame.ControlledObservedGame.WellFoundedTwoPlayerHypotheses.isTwoPlayerDetermined
    - ExtensiveGame.ControlledObservedGame.WellFoundedPrefixHypotheses.isTwoPlayerDetermined
tags:
  - backward-induction
  - determinacy
  - extensive-game
  - perfect-information
  - well-founded
---

# Well-Founded Prefix Determinacy

Let an observed logical game have exactly two players, no chance nodes,
perfect information, a total and exclusive complete-play winning condition,
and a well-founded legal-history child relation. Also supply
`BackwardInductionData`: a terminality decision procedure, certified winners
for terminal replays, a complete finite action list at every history, and an
occurrence representative for each represented information coordinate. Then
one of the two players has a total pure strategy over represented coordinates
that wins against every compatible opponent play.

The stronger prefix package additionally records a persistent, sound
prefix-decision certificate. It specializes to the same well-founded theorem
and still requires the same `BackwardInductionData`.

## Formal route

`WellFounded.fix` assigns a winner to every complete history. At a terminal
history it reads the zero-sum winner from the canonical stuttering replay. At
a decision history the mover wins if some child is winning for that mover;
otherwise the other player wins.

Finite search selects a winning child from the supplied action list; the data
also supplies a concrete representative of each represented information
coordinate. Perfect information identifies that representative
with the actual complete-history occurrence. Along the extracted strategy,
the root winner is invariant. Root well-foundedness makes every compatible
complete play eventually terminal, where the replay agrees with that play.

The recursive construction uses the supplied data. The finite determinacy
specialization constructs that data using classical choice. Neither result
uses descriptive-set theory or an arbitrary-set determinacy principle.

## Boundary

The structural hypotheses alone permit infinite branching, but the additional
complete finite action lists do not. The `UnboundedWellFounded` example has
root action type `Nat` and therefore does not instantiate this theorem.
General well-founded determinacy with arbitrary branching remains unimplemented.

This theorem does not apply to a legal infinite branch. It also does not imply
open, closed, Borel, arbitrary-set, probabilistic, or almost-sure
determinacy. Gale--Stewart-style infinite determinacy remains a separate
theorem track.

## References

- [Zermelo 1913] Ernst Zermelo, “Über eine Anwendung der Mengenlehre auf die
  Theorie des Schachspiels.” Finite terminating perfect-information
  backward-determinacy precedent.
- [Gale--Stewart 1953] David Gale and F. M. Stewart, “Infinite Games with
  Perfect Information,” pp. 245--266. Source boundary for the distinct
  infinite-game determinacy theory.
