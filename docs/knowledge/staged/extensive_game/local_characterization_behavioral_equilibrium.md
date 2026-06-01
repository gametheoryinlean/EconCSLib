---
id: game_theory.extensive_game.imperfect_information.local_characterization_behavioral_equilibrium
primary_topic: game_theory.extensive_game
topics:
  - game_theory.extensive_game
  - game_theory.extensive_game.imperfect_information
title: Local Characterization Of Behavioral Equilibrium
kind: theorem
status: staged
uses:
  - game_theory.extensive_game.imperfect_information.reached_information_set
verification:
  statement: accepted
  proof: gap
tags:
  - extensive-game
  - behavioral-strategy
  - nash-equilibrium
---

# Local Characterization Of Behavioral Equilibrium

For a finite extensive form game with perfect recall, a behavioral profile $\beta$
is a behavioral equilibrium if and only if, for every player $i$ and every reached
information set $Q_i\in Rch(\beta)$, the behavioral action $\beta_i(Q_i)$ is a best
response in the local continuation game starting at $Q_i$, with Nature choosing a
node of $Q_i$ according to $\nu_\beta(Q_i)$ and future play following $\beta$.

## Proof Sketch

If a behavioral profile is not an equilibrium, then some profitable deviation can be
localized to a reached information set, because changing off-path behavior alone
does not affect payoffs. Conversely, a profitable local deviation at a reached
information set can be inserted into the full behavioral strategy to obtain a
profitable global deviation.

## References

- [MFoGT, Thm. 6.3.8] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Behavioral equilibrium iff prescribed actions are best responses at reached information sets.
