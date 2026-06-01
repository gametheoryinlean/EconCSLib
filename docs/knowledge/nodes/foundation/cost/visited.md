---
id: foundation.cost.visited
title: Memoization Footprint via the Visited Monoid
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
    - EconCSLib.Foundation.CostM.Visited
  declarations:
    - Visited
    - Visited.toFinset
    - Visited.ofFinset
    - Visited.singleton
verification:
  definition: accepted
  proof: accepted
  alignment: aligned
tags:
  - cost
  - memoization
  - idempotent
---

# Memoization Footprint via the Visited Monoid

`Visited α` is the cost monoid that records the **set of subproblems touched**
by a recursive algorithm. It is `Finset α` with union as addition and the
empty set as zero:
$$
  s + t = s \cup t, \qquad 0 = \varnothing.
$$
The defining feature is **idempotence**, `s + s = s`: revisiting a subproblem
adds nothing. This is the algebraic shadow of memoization — under a memo table
the second visit is free, so the cost (the footprint) is exactly the set of
*distinct* subproblems, not the number of calls. A memoized algorithm's
`.cost` is therefore the set of table entries it fills.

`Visited α` is a **type synonym** for `Finset α` (`def Visited α := Finset α`),
introduced specifically to firewall Mathlib's scoped pointwise `Zero (Finset α)`
instance: the cost-monoid `0 = ∅` and `+ = ∪` must not collide with pointwise
arithmetic on finsets. `toFinset`/`ofFinset` move across the synonym boundary.

## Lean declarations

- `Visited` — the `Finset` type synonym; `Visited.toFinset`/`Visited.ofFinset`
  the round-trip maps and `Visited.singleton a` the one-point footprint.
- `Zero`/`Add [DecidableEq α]`/`AddMonoid` instances are anonymous.
- `Visited.ext` plus the `simp` lemmas `toFinset_zero`, `toFinset_singleton`,
  `toFinset_add` reduce footprint reasoning to ordinary `Finset` set algebra.

Worked examples: the 1-D memoization footprint of Fibonacci
([[node:foundation.cost.examples.memo_fib]], cost `= range (n+1)`) and the 2-D
DP-grid footprint of longest common subsequence
([[node:foundation.cost.examples.lcs]]).

## References

- [Danielsson 2008] Nils Anders Danielsson, *Lightweight Semiformal Time
  Complexity Analysis for Purely Functional Data Structures*, POPL 2008. Cost
  monoids for resource analysis ([[node:foundation.cost.costm]]).

## Provenance

- `Visited` is an EconCSLib addition (no `TimeM` counterpart upstream), built on
  the [leanprover/cslib](https://github.com/leanprover/cslib)-derived monad
  core (Apache 2.0).
