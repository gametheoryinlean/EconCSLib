---
id: foundation.cost.parallel
title: Parallel Composition in CostM
kind: definition
status: formalized
primary_topic: foundation
topics:
  - foundation
  - foundation.cost
uses:
  - foundation.cost.costm
lean:
  modules:
    - EconCSLib.Foundation.CostM
  declarations:
    - CostM.par
    - CostM.parList
verification:
  definition: accepted
  proof: accepted
  alignment: aligned
tags:
  - cost
  - parallel
  - complexity
---

# Parallel Composition in CostM

Sequential `>>=` combines cost additively; **parallel** composition combines it
by the semilattice join `⊔` instead, modelling the *depth* (branch-worst-case)
view in which independent branches run concurrently and the joint cost is the
worse of the two:
$$
  (\operatorname{par} m_1\, m_2).\mathrm{cost}
    \;=\; m_1.\mathrm{cost} \,\sqcup\, m_2.\mathrm{cost}.
$$
`par` is **not** a monadic operation: neither operand's value feeds the other,
so it is only sound when the two sides are genuinely data-independent. It
requires `[SemilatticeSup C]`.

The n-ary `parList ms` extends `par` to a `List` of independent operands:
returns are collected in order, and costs are folded with `⊔` from the
identity `⊥` (so the empty list costs `⊥`, which is `0` for `C = ℕ`):
$$
  (\operatorname{parList}\,[m_1,\dots,m_n]).\mathrm{cost}
    \;=\; m_1.\mathrm{cost} \sqcup \cdots \sqcup m_n.\mathrm{cost}.
$$
`parList` additionally needs `[OrderBot C]` for that identity. This is the
flat fan-out / fan-in, depth-1 schedule with `n` workers.

For combined work-and-depth tracking one would use `C := ℕ × ℕ` with `+` on
the work component and `⊔` on the depth component; that per-component
combinator is not provided here.

## Lean declarations

- `CostM.par` `[SemilatticeSup C]` with projection lemmas `ret_par`, `cost_par`.
- `CostM.parList` `[SemilatticeSup C] [OrderBot C]` with `ret_parList`,
  `cost_parList`, the base case `parList_nil`, and the cons recurrence
  `cost_parList_cons`.

Worked examples: balanced-tree depth in [[node:foundation.cost.examples.par_sum]]
and the n-ary `parList` bound in [[node:foundation.cost.examples.par_all]].

## References

- [Danielsson 2008] Nils Anders Danielsson, *Lightweight Semiformal Time
  Complexity Analysis for Purely Functional Data Structures*, POPL 2008. The
  underlying writer-monad cost discipline ([[node:foundation.cost.costm]]).

## Provenance

- `par` and `parList` are EconCSLib additions on top of the `TimeM`-derived
  monad core from [leanprover/cslib](https://github.com/leanprover/cslib)
  (Apache 2.0); they have no upstream counterpart at the pinned revision.
