---
id: game_theory.extensive_game.imperfect_information.proper_equilibrium_induces_sequential
primary_topic: game_theory.extensive_game
topics:
  - game_theory.extensive_game
  - game_theory.extensive_game.imperfect_information
title: Proper Equilibrium Induces Sequential Equilibrium
kind: theorem
status: staged
uses:
  - game_theory.strategic_game.refinements.proper_equilibrium
  - game_theory.extensive_game.imperfect_information.sequential_equilibrium
  - game_theory.extensive_game.imperfect_information.perfect_recall_mixed_to_behavioral
verification:
  statement: accepted
  proof: gap
tags:
  - extensive-game
  - sequential-equilibrium
  - proper-equilibrium
---

# Proper Equilibrium Induces Sequential Equilibrium

Let $G$ be a finite normal-form game and let $\Gamma$ be any perfect-recall
extensive form game whose normal form is $G$. If $\sigma$ is a proper equilibrium
of $G$, then $\sigma$ induces a sequential equilibrium $(\beta,\mu)$ of $\Gamma$.

## Proof Sketch

Write $\sigma$ as the limit of completely mixed $\epsilon_n$-proper profiles
$\sigma^n$. By Kuhn's theorem, each $\sigma^n$ generates an equivalent interior
behavioral strategy $\beta^n$. Since every information set is reached with positive
probability under $\beta^n$, Bayes' rule gives beliefs $\mu^n$.

After passing to a convergent subsequence, $(\beta^n,\mu^n)\to(\beta,\mu)$. If an
action in the support of $\beta$ were not optimal at some information set, the
$\epsilon_n$-proper inequalities would force its probability to vanish, a
contradiction. Hence $(\beta,\mu)$ is sequential.

## References

- [MFoGT, Thm. 6.6.4] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. A proper equilibrium of a finite normal form induces a sequential equilibrium in every perfect-recall extensive form with that normal form.
