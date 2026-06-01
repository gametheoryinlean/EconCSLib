---
id: social_choice.instance
title: Social Choice Instance
kind: definition
status: formalized
primary_topic: social_choice
topics:
  - social_choice
uses:
  - social_choice.preference
lean:
  modules:
    - EconCSLib.SocialChoice.Basic
  declarations:
    - SocialChoice.Instance
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
tags:
  - social-choice
  - instance
---

# Social Choice Instance

A *social choice instance* over a population $N$ and alternative space $A$
packages two pieces of data:

- a feasibility predicate $F : A \to \mathrm{Prop}$ singling out the feasible
  alternatives for this instance;
- for each agent $i \in N$, a preference $P_i \in \mathrm{Pref}(A)$.

In Lean: `SocialChoice.Instance N A` with fields `feasible : A → Prop` and
`pref : N → Pref A`.

The motivation for keeping feasibility as a per-instance predicate (rather
than restricting $A$ once and for all) is that it lets several specialized
problems share the same alternative space:

- Voting instances typically take $F$ to be `fun _ => True` and use the
  whole alternative set.
- Fair-division instances over a fixed allocation type can vary feasibility
  per resource; `ShareInstance` carries a `feasible : (N → S) → Prop`
  predicate on allocations rather than on individual outcomes.

The pair $(F, P)$ is the canonical input for any *solution concept* on the
instance ([[social_choice.solution_concept]]).

## References

- [MSZ, Chapter 21] Maschler, Solan, and Zamir, *Game Theory*. Generic social-choice setup.
