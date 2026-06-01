---
id: foundation.preference.relation
title: Preference Relation (MSZ Ch.2 Narrative)
kind: definition
status: staged
primary_topic: foundation
topics:
  - foundation
  - foundation.preference
uses:
  - foundation.preference.indifferent
  - foundation.preference.strictly_preferred
  - foundation.preference.total_preorder
  - foundation.preference.abstract_relation
lean:
  modules:
    - EconCSLib.Foundation.Preference
verification:
  definition: accepted
  proof: not_applicable
  alignment: pending
tags:
  - preference
---

# Preference Relation (MSZ Ch.2 Narrative)

A weak preference relation compares alternatives by the statement that one
alternative is at least as good as another. From weak preference one derives:

- *strict preference*, when one alternative is weakly preferred and the
  reverse weak preference fails;
- *indifference*, when each alternative is weakly preferred to the other.

For utility theory the natural abstract structure is a total preorder:
preference is reflexive, transitive, and complete, but it need not be
antisymmetric because distinct alternatives can be indifferent.

## Lean substrate

The Lean-level vocabulary lives in the `foundation.preference` topic; this node
is the MSZ Ch.2 domain narrative, and it cross-links into the four foundation
definitions that realize it:

- weak preference and indifference: [[foundation.preference.indifferent]]
- strict preference: [[foundation.preference.strictly_preferred]]
- total preorder (no antisymmetry required): [[foundation.preference.total_preorder]]
- relation-style axioms used by vNM: [[foundation.preference.abstract_relation]]

The `EconCSLib.Foundation.Preference` module is the single source of truth in
Lean; this node is the MSZ Ch.2 narrative wrapper and introduces no Lean
definitions of its own beyond what the `foundation.preference` topic already
provides.

## References

- [MSZ, Chapter 2, Definitions 2.1-2.7] Maschler, Solan, and Zamir,
  *Game Theory*. Preference, strict preference,
  indifference, and total preorder vocabulary.
