---
id: social_choice.fair_division.instance
title: Fair Division Instance
kind: definition
status: formalized
primary_topic: social_choice
topics:
  - social_choice
  - social_choice.fair_division
  - social_choice.fair_division.core
uses:
  - social_choice.fair_division.allocation
  - social_choice.preference
lean:
  modules:
    - EconCSLib.SocialChoice.FairDivision.Basic
  declarations:
    - SocialChoice.FairDivision.Instance
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
tags:
  - fair-division
  - instance
---

# Fair Division Instance

A *fair-division instance* over a population $N$, resource type $R$, and
share type $S$ bundles:

- **Resource side**: a value `resource : R` carrying problem-specific
  parameters (the cake, the item set, capacity constraints, …).
- **Feasibility**: a predicate `feasible : Allocation N S → Prop` on
  complete allocations.
- **Preferences**: for each agent, a preference $P_i$ on the *whole
  allocation* space ($\mathrm{Pref}(\mathrm{Allocation}\ N\ S)$).

In Lean: structure `SocialChoice.FairDivision.Instance N R S`.

The generality of `pref i : Pref (Allocation N S)` lets the instance encode
*externalities* — agent $i$'s ranking can depend on every other agent's
share, not just their own. The no-externality specialization is
[[social_choice.fair_division.share_instance]].

This instance sits exactly above the generic social-choice instance shape
([[social_choice.instance]]) but with a structured alternative space
$\mathrm{Allocation}\ N\ S$ in place of an unstructured $A$.

## References

- [AGT Chapter 11] Nisan, Roughgarden, Tardos, and Vazirani, *Algorithmic Game Theory*. Fair division instances.
