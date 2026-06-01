---
id: social_choice.preference
title: Preference Relation
kind: definition
status: formalized
primary_topic: social_choice
topics:
  - social_choice
uses: []
lean:
  modules:
    - EconCSLib.Foundation.Preference
  declarations:
    - IsPreference
    - Pref
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
tags:
  - social-choice
  - preference
---

# Preference Relation

A *weak preference* on a set $A$ of alternatives is a binary relation
$R \subseteq A \times A$ that is reflexive, transitive, and total, i.e.

$$
\forall a \in A,\ R(a,a), \qquad
R(a,b) \wedge R(b,c) \Rightarrow R(a,c), \qquad
R(a,b) \vee R(b,a).
$$

A *preference* on $A$ is a relation $R$ together with a proof that the three
axioms above hold; equivalently, $R$ is a complete preorder on $A$. We write
$R(a,b)$ to mean "$a$ is weakly preferred to $b$".

In Lean this is the typeclass `IsPreference` together with the bundled
structure `Pref A`, providing the relation field `rel` and a `CoeFun` so
`p a b` reads as $p(a,b)$.

This foundation-level `Pref` interface is the canonical single source of truth
for an agent's ordinal taste over outcomes. Social choice, fair division, and
matching all build on it.

## References

- [MSZ, Chapter 21] Maschler, Solan, and Zamir, *Game Theory*. Bundled preference vocabulary for social choice.
