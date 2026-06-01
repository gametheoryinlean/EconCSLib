---
id: social_choice.solution_concept
title: Solution Concept, Rule, and Correspondence
kind: definition
status: formalized
primary_topic: social_choice
topics:
  - social_choice
uses:
  - social_choice.instance
lean:
  modules:
    - EconCSLib.SocialChoice.Basic
  declarations:
    - SocialChoice.SolutionConcept
    - SocialChoice.Rule
    - SocialChoice.Correspondence
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
tags:
  - social-choice
  - solution-concept
---

# Solution Concept, Rule, and Correspondence

For a fixed population $N$ and alternative space $A$, three closely related
shapes describe ways of selecting alternatives from a social choice
instance $I = (F, P)$ ([[social_choice.instance]]).

- A *solution concept* is a predicate
  $\sigma : \mathrm{Instance}\, N\, A \to A \to \mathrm{Prop}$
  marking the alternatives that the concept deems acceptable in $I$.
  In Lean: `SolutionConcept N A := Instance N A → A → Prop`.

- A *rule* is a deterministic single-valued choice that, for each instance,
  returns a *feasible* alternative:
  $\rho(I) \in \{a \in A \mid I.\mathrm{feasible}\,a\}.$
  In Lean: `Rule N A := (I : Instance N A) → {a : A // I.feasible a}` —
  the subtype carries the feasibility witness.

- A *correspondence* is a set-valued choice:
  $\Phi : \mathrm{Instance}\, N\, A \to \mathcal{P}(A).$
  In Lean: `Correspondence N A := Instance N A → Set A`.

These three shapes cover the standard styles of social choice output: a
*predicate* (e.g. "is a stable outcome"), a *function* (a deterministic
rule with a feasibility guarantee), and a *set-valued map* (a Pareto
correspondence, a choice correspondence, and so on).

Specializations appear at later layers: the voting layer instantiates
solution concepts and rules into social welfare functions and social
choice functions ([[social_choice.voting.swf]],
[[social_choice.voting.scf]]); fair division supplies rules returning a
feasible allocation.

## References

- [MSZ, Chapter 21] Maschler, Solan, and Zamir, *Game Theory*. Choice rules and correspondences.
