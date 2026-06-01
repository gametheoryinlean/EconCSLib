---
id: foundation.preference.abstract_relation
title: Abstract Preference-Relation Axioms
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
    - strict
    - indiff
    - VNM.Completeness
    - VNM.Transitivity
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
tags:
  - core
  - preference
  - vnm
---

# Abstract Preference-Relation Axioms

For arguments that quantify over an arbitrary binary relation
`pref : α → α → Prop` (rather than the bundled `Preorder` instance), the
foundation layer exposes a relation-style vocabulary:

- **Strict preference** `strict pref a b := pref a b ∧ ¬ pref b a`
- **Indifference** `indiff pref a b := pref a b ∧ pref b a`
- **Completeness** `Completeness pref := ∀ a b, pref a b ∨ pref b a`
- **Transitivity** `Transitivity pref := ∀ a b c, pref a b → pref b c → pref a c`

This vocabulary is what preference-based statements and the vNM axiom suite use
to formulate axioms about a free-standing relation argument, without
committing to the `Preorder` typeclass on `α`. Lottery-specific axioms
(Independence, Continuity, Archimedean property) are stated on top of
`Completeness` and `Transitivity` in `Utility.VNMAxioms`.

In Lean, `strict` and `indiff` are library-wide definitions.
`Completeness` and `Transitivity` remain inside `namespace VNM` because they
name axioms in the vNM suite.

## References

- [MSZ, Chapter 2] Maschler, Solan, and Zamir, *Game Theory*. Preference-relation axioms in their
  relation-style formulation.
