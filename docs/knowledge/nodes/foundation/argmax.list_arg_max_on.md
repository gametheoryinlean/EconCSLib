---
id: foundation.argmax.list_arg_max_on
title: Argmax of a List under a Total Preorder
kind: definition
status: formalized
primary_topic: foundation
topics:
  - foundation
  - foundation.argmax
uses:
  - foundation.preference.total_preorder
lean:
  modules:
    - EconCSLib.Foundation.Argmax
  declarations:
    - List.exists_argMax_on
    - List.argMaxOn
    - List.argMaxOn_mem
    - List.argMaxOn_ge
    - List.le_argMaxOn_head
verification:
  definition: accepted
  proof: accepted
  alignment: aligned
tags:
  - core
  - argmax
  - extensive-game
---

# Argmax of a List under a Total Preorder

For a function `f : α → β` valued in a `TotalPreorder β` and a non-empty
list `head :: tail : List α`, some element of the list maximizes `f`:
$$
  \exists m \in \operatorname{head} :: \operatorname{tail},\;
  \forall x \in \operatorname{head} :: \operatorname{tail},\; f(x) \le f(m).
$$

The proof is by induction on `tail`, comparing the current maximum against
the new head via `TotalPreorder.le_total`.

From the existence statement a noncomputable choice
`List.argMaxOn f head tail` picks a witnessing maximizer. Its API:

- `argMaxOn_mem` -- the chosen element lies in the list.
- `argMaxOn_ge` -- the chosen element is `≥` every list element in `f`-value.
- `le_argMaxOn_head` -- specialization: the head's value is `≤` the chosen
  element's value.

The variant exists because Mathlib's `List.argmax` is computable but requires
`[LinearOrder]`, which is too strong for ranking outcomes that may be
indifferent (the typical situation when a player's payoffs are equal across
distinct continuations). The intended consumer is
`ExtensiveGame.BackwardInduction`, where finite game trees are evaluated by
recursively picking an argmax of children.

## References

- [MSZ, Chapter 3] Maschler, Solan, and Zamir, *Game Theory*. Backward induction on finite extensive games.
