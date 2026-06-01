---
id: game_theory.extensive_game.imperfect_information.mertens_stable_sets
primary_topic: game_theory.extensive_game
topics:
  - game_theory.extensive_game
  - game_theory.extensive_game.imperfect_information
title: Mertens Stable Sets
kind: definition
status: staged
uses:
  - game_theory.extensive_game.imperfect_information.strategic_stability
  - game_theory.strategic_game.core.br_invariance
verification:
  definition: accepted
  proof: not_applicable
tags:
  - extensive-game
  - strategic-stability
  - mertens
---

# Mertens Stable Sets

MFoGT describes Mertens stable sets as essential components obtained using a
Selten-style topology of strategy perturbations. For each $\epsilon>0$ and fully
mixed $\sigma\in\operatorname{int}\Sigma$, one considers the perturbed game
$G(\sigma;\epsilon)$ in which every player is restricted to a perturbed simplex
close to the original mixed simplex.

Mertens proved that the resulting stable sets are connected, BR-invariant,
admissible, and compatible with backward-induction and forward-induction
requirements.

The text notes that a complete uniqueness characterization of Mertens stable sets
from these desirable properties remains open in general.

## References

- [MFoGT, Section 6.7] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Mertens stable sets from Selten-style strategy perturbation topology.
