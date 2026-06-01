---
id: foundation.preference.strictly_preferred
title: Strict Preference Relation
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
    - StrictlyPreferred
    - StrictlyPreferred.asymm
    - StrictlyPreferred.trans
    - StrictlyPreferred.irrefl
verification:
  definition: accepted
  proof: accepted
  alignment: aligned
tags:
  - core
  - preference
  - strict-preference
---

# Strict Preference Relation

On any `Preorder α`, strict preference is the strict part of the preorder:
$$
  a \succ b \quad\Longleftrightarrow\quad a < b
  \quad\Longleftrightarrow\quad a \le b \;\text{ and }\; \neg(b \le a).
$$

Strict preference is asymmetric, transitive, and irreflexive. These three
properties — asymmetry from `lt_asymm`, transitivity from `lt_trans`,
irreflexivity from `lt_irrefl` — are inherited directly from the Mathlib
`Preorder` API.

In Lean this is `abbrev StrictlyPreferred (a b : α) : Prop := a < b`. The
abbreviation exists for readability in game-theory contexts; downstream code
may also use the bare `<` notation interchangeably.

## References

- [MSZ, Chapter 2, Def. 2.5] Maschler, Solan, and Zamir, *Game Theory*. Strict preference derived from weak preference.
- [MSZ, Exercise 2.1(a)] Asymmetry, transitivity, and irreflexivity of strict
  preference.
