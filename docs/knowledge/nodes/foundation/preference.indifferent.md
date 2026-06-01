---
id: foundation.preference.indifferent
title: Indifference Relation
kind: definition
status: formalized
primary_topic: foundation
topics:
  - foundation
  - foundation.preference
uses: []
lean:
  modules:
    - EconCSLib.Foundation.Preference
  declarations:
    - Indifferent
    - Indifferent.refl
    - Indifferent.symm
    - Indifferent.trans
verification:
  definition: accepted
  proof: accepted
  alignment: aligned
tags:
  - core
  - preference
  - indifference
---

# Indifference Relation

On any `Preorder α`, two elements are *indifferent* when each is weakly
preferred to the other:
$$
  \operatorname{Indifferent}(a, b) \quad\Longleftrightarrow\quad
  a \le b \;\text{ and }\; b \le a.
$$

Indifference is reflexive, symmetric, and transitive. It is therefore an
equivalence relation on every preorder. On a `PartialOrder` antisymmetry
collapses it to equality; on a general preorder (or total preorder) it can
relate genuinely distinct elements, which is the typical situation in utility
theory.

In Lean this is `Indifferent : α → α → Prop` together with
`Indifferent.refl / symm / trans`.

## References

- [MSZ, Chapter 2, Def. 2.5] Maschler, Solan, and Zamir, *Game Theory*. Indifference as the symmetric part of weak
  preference.
