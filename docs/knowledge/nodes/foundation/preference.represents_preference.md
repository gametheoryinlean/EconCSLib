---
id: foundation.preference.represents_preference
title: Utility Representation of a Preference
kind: definition
status: formalized
primary_topic: foundation
topics:
  - foundation
  - foundation.preference
uses:
  - foundation.preference.indifferent
  - foundation.preference.strictly_preferred
lean:
  modules:
    - EconCSLib.Foundation.Preference
  declarations:
    - RepresentsPreference
    - RepresentsPreference.lt_iff
    - RepresentsPreference.indifferent_iff
verification:
  definition: accepted
  proof: accepted
  alignment: aligned
tags:
  - core
  - preference
  - utility-representation
---

# Utility Representation of a Preference

Given preorders on `α` and `β`, a function `u : α → β` *represents* the
preference `≤` on `α` when it preserves and reflects weak preference:
$$
  \forall a,\,b,\quad a \le b \;\Longleftrightarrow\; u(a) \le u(b).
$$

A representation automatically preserves the derived strict preference and
indifference relations, witnessed by `RepresentsPreference.lt_iff` and
`RepresentsPreference.indifferent_iff`. This is the abstract scaffolding used
by ordinal-utility statements in utility theory (the `foundation.preference` topic)
and by vNM-style expected-utility theorems.

In Lean this is `structure RepresentsPreference (u : α → β) : Prop` carrying
the single field `le_iff`. The two derived `iff` lemmas are stated and proved
directly from `le_iff` using the Mathlib `Preorder` API.

## References

- [MSZ, Chapter 2, Def. 2.7] Maschler, Solan, and Zamir,
  *Game Theory*. Utility representation of a
  preference relation.
