---
id: social_choice.fair_division.indivisible.envy_cycle
title: Envy Cycle
kind: definition
status: formalized
primary_topic: social_choice
topics:
  - social_choice
  - social_choice.fair_division
  - social_choice.fair_division.indivisible
  - social_choice.fair_division.indivisible.algorithms
uses:
  - social_choice.fair_division.indivisible.envies
lean:
  modules:
    - EconCSLib.SocialChoice.FairDivision.Indivisible.EnvyCycle
  declarations:
    - SocialChoice.FairDivision.Indivisible.isEnvyCycle
    - SocialChoice.FairDivision.Indivisible.hasEnvyCycle
    - SocialChoice.FairDivision.Indivisible.isEnvyCycle_length_ge_two
    - SocialChoice.FairDivision.Indivisible.isSource_not_mem_envyCycle
verification:
  definition: accepted
  proof: accepted
  alignment: aligned
tags:
  - fair-division
  - indivisible
  - envy-cycle
  - algorithms
---

# Envy Cycle

A list $[i_0, i_1, \dots, i_{k-1}]$ of distinct agents is an *envy
cycle* if each consecutive pair (cyclically) envies the next:
$$
i_0 \to_{\text{envy}} i_1, \quad i_1 \to_{\text{envy}} i_2, \quad \dots, \quad i_{k-1} \to_{\text{envy}} i_0,
$$
using the envy relation ([[social_choice.fair_division.indivisible.envies]]).

In Lean: `isEnvyCycle v A l` for the list `l`, and `hasEnvyCycle v A`
for the existential "some envy cycle exists".

## Basic structural lemmas

- **Length $\ge 2$.** `isEnvyCycle_length_ge_two`: an envy cycle has at
  least two elements (irreflexivity rules out length-1 self-cycles;
  distinctness rules out length-0).

- **Sources are not in any cycle.** `isSource_not_mem_envyCycle`: if
  agent $i$ is a source ([[social_choice.fair_division.indivisible.envies]])
  then $i$ does not appear in any envy cycle. (A cycle member is
  envied by their cyclic predecessor, hence is not a source.)

## Role in cycle elimination

Envy cycles are the obstruction to having a source agent: an acyclic
envy graph on a finite nonempty set must have a source
([[social_choice.fair_division.indivisible.acyclic_has_source]]).

The envy-cycle elimination algorithm
([[social_choice.fair_division.indivisible.envy_cycle_algorithm]])
repeatedly finds a cycle and resolves it by bundle rotation
([[social_choice.fair_division.indivisible.rotate_bundles]]), which
strictly improves utilities and is guaranteed to terminate.

## References

- Lipton, Markakis, Mossel, and Saberi (2004). "On Approximately Fair Allocations of Indivisible Goods". *EC*.
- [AGT Chapter 11] Nisan, Roughgarden, Tardos, and Vazirani, *Algorithmic Game Theory*. Envy graph and cycle elimination.
