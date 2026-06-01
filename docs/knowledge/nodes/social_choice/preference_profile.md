---
id: social_choice.preference_profile
title: Preference Profile
kind: definition
status: formalized
primary_topic: social_choice
topics:
  - social_choice
uses:
  - social_choice.preference
lean:
  modules:
    - EconCSLib.Foundation.Preference
  declarations:
    - PrefProfile
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
tags:
  - social-choice
  - preference
  - profile
---

# Preference Profile

Given a (finite or arbitrary) population $N$ of agents and an alternative
set $A$, a *preference profile* assigns each agent $i \in N$ a weak
preference $P_i$ on $A$:

$$
P : N \to \mathrm{Pref}(A), \qquad i \mapsto P_i.
$$

In Lean: `PrefProfile N A := N → Pref A`. Each entry `P i` is a bundled
preference ([[social_choice.preference]]), so unanimity, dictatorship, and IIA can all be stated
uniformly in terms of how the entries `P i` rank pairs of alternatives.

This is the generic weak-preference profile shape. The voting layer uses a
strict finite specialization whose ballots are `LinearOrder A`.

## References

- [MSZ, Chapter 21] Maschler, Solan, and Zamir, *Game Theory*. Preference profiles as inputs to social choice rules.
