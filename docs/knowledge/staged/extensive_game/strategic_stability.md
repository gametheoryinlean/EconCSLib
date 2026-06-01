---
id: game_theory.extensive_game.imperfect_information.strategic_stability
primary_topic: game_theory.extensive_game
topics:
  - game_theory.extensive_game
  - game_theory.extensive_game.imperfect_information
title: Strategic Stability
kind: definition
status: staged
uses:
  - game_theory.strategic_game.refinements.proper_equilibrium
  - game_theory.extensive_game.imperfect_information.forward_induction
verification:
  definition: accepted
  proof: not_applicable
tags:
  - extensive-game
  - strategic-stability
  - equilibrium-refinement
---

# Strategic Stability

A subset $C$ of Nash equilibria of an extensive or normal form game $\Gamma$ is
strategically stable if:

- $C$ is connected;
- for any normal-form game $G$ with the same reduced normal form as $\Gamma$;
- for any sufficiently nearby perturbation $G^\epsilon$ of $G$;

there is a Nash equilibrium $\sigma^\epsilon$ of $G^\epsilon$ close to $C$.

MFoGT presents this after the Kohlberg-Mertens axioms. A stable solution should
depend only on the reduced normal form, form a connected set of non-weakly
dominated equilibria, contain a proper equilibrium, and survive deletion of
weakly dominated strategies.

## References

- [MFoGT, Section 6.7] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Kohlberg-Mertens strategic stability and stable sets of Nash equilibria.
