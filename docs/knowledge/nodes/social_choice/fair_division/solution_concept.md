---
id: social_choice.fair_division.solution_concept
title: Fair Division Solution Concept and Rule
kind: definition
status: formalized
primary_topic: social_choice
topics:
  - social_choice
  - social_choice.fair_division
  - social_choice.fair_division.core
uses:
  - social_choice.fair_division.instance
lean:
  modules:
    - EconCSLib.SocialChoice.FairDivision.Basic
  declarations:
    - SocialChoice.FairDivision.SolutionConcept
    - SocialChoice.FairDivision.Rule
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
tags:
  - fair-division
  - solution-concept
---

# Fair Division Solution Concept and Rule

Two output shapes for fair-division procedures:

- A *solution concept* is a predicate
  $\sigma : \mathrm{Instance}\ N\ R\ S \to \mathrm{Allocation}\ N\ S \to \mathrm{Prop}$
  marking the allocations that the concept deems acceptable for the
  instance. In Lean:
  `SolutionConcept N R S := Instance N R S → Allocation N S → Prop`.

- A *rule* is a deterministic procedure that, for each instance, returns
  a *feasible* allocation, packaged with its feasibility witness:
  $\rho(I) \in \{A : \mathrm{Allocation}\ N\ S \mid I.\mathrm{feasible}\ A\}.$
  In Lean: `Rule N R S := (I : Instance N R S) → {A : Allocation N S // I.feasible A}`.

These are the fair-division analogues of [[social_choice.solution_concept]],
specialized to the structured alternative space $\mathrm{Allocation}\ N\ S$.

Concrete examples that hit each shape:

- *Solution concepts*: envy-freeness
  ([[social_choice.fair_division.envy_free]]), proportionality
  ([[social_choice.fair_division.proportional]]), Pareto optimality
  ([[social_choice.fair_division.pareto_optimal]]).
- *Rules*: cut-and-choose
  ([[social_choice.fair_division.divisible.cut_and_choose_alloc]]),
  Dubins–Spanier
  ([[social_choice.fair_division.divisible.dubins_spanier_proportional]]),
  round-robin
  ([[social_choice.fair_division.indivisible.round_robin_alloc]]),
  envy-cycle elimination
  ([[social_choice.fair_division.indivisible.envy_cycle_algorithm]]).

## References

- [AGT Chapter 11] Nisan, Roughgarden, Tardos, and Vazirani, *Algorithmic Game Theory*. Fair-division rules and acceptable-allocation predicates.
