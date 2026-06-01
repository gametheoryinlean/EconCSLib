---
id: foundation.preference.total_preorder
title: Total Preorder
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
    - TotalPreorder
    - TotalPreorder.comparable
verification:
  definition: accepted
  proof: accepted
  alignment: aligned
tags:
  - core
  - preference
  - total-preorder
---

# Total Preorder

A *total preorder* on `α` is a `Preorder` for which `≤` is total:
$$
  \forall a,\, b \in \alpha,\quad a \le b \;\text{ or }\; b \le a.
$$

Unlike `LinearOrder`, a total preorder is **not** required to be antisymmetric
or to have decidable order. Distinct elements may be indifferent, which is
the typical situation in utility theory (multiple alternatives can yield the
same utility) and in matching theory (a doctor can rank two hospitals equally).

`TotalPreorder` is the appropriate weakening of `LinearOrder` whenever a
result needs comparability of any two elements but does not need to identify
indifferent alternatives. Every `LinearOrder` is a `TotalPreorder` via the
auto-derived `LinearOrder.toTotalPreorder` instance.

In Lean this is `class TotalPreorder (α : Type*) extends Preorder α`
together with the totality field `le_total` and the reusable lemma
`TotalPreorder.comparable`. The bridge from `LinearOrder` is supplied by
the auto-derived instance `LinearOrder.toTotalPreorder` in the same module
(declared with `instance`, not enumerated in the declaration list above).

## References

- [MSZ, Chapter 2, Definitions 2.1-2.4] Maschler, Solan, and Zamir,
  *Game Theory*. Reflexivity, transitivity,
  and completeness of weak preference.
