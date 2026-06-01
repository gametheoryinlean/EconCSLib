---
id: foundation.cost.costm
title: The CostM Complexity Monad
kind: definition
status: formalized
primary_topic: foundation
topics:
  - foundation
  - foundation.cost
uses: []
lean:
  modules:
    - EconCSLib.Foundation.CostM
  declarations:
    - CostM
    - CostM.pure
    - CostM.bind
    - CostM.tick
    - CostM.instMonad
    - CostM.instLawfulMonad
    - CostM.Bounded
    - CostM.IsPolyBounded
verification:
  definition: accepted
  proof: accepted
  alignment: aligned
tags:
  - cost
  - monad
  - complexity
---

# The CostM Complexity Monad

`CostM C α` is the **writer monad over an arbitrary additive monoid** `C`: a
return value of type `α` paired with an accumulated cost in `C`,
$$
  \mathrm{CostM}\,C\,\alpha \;=\; \alpha \times C.
$$
Sequential composition (`bind`, written `>>=`) adds the cost components,
$$
  \mathrm{bind}(m, f).\mathrm{cost}
    \;=\; m.\mathrm{cost} \,+\, (f\,m.\mathrm{ret}).\mathrm{cost},
  \qquad
  (\mathrm{pure}\,a).\mathrm{cost} = 0,
$$
so a program's total cost is the monoid-sum of the costs charged along its
execution.

The cost type `C` is deliberately abstract: **choosing `C` is what selects the
resource being measured**, while the monad is identical for all of them.

- `C := ℕ` (additive) — count comparisons, recursive calls, modulus
  operations: the conventional "time" instance.
- `C := A × B` — track two additive costs at once via `Prod.instAddMonoid`.
- `C := Visited α` (idempotent, `s + s = s`) — the **set** of subproblems
  touched; the algebraic shadow of memoization. See
  [[node:foundation.cost.visited]].
- `C := Cells` (tropical peak/delta) — **peak** memory, the one resource shape
  additive cost fundamentally cannot express. See [[node:foundation.cost.cells]].

## Discipline: cost annotations are trusted

The elaborator does **not** verify that `tick` calls correspond to real work.
Each algorithm file documents its own cost model — what a unit is, what is
free, whether recursive calls are charged — and the author `tick`s
accordingly. Proofs then separate cleanly along the two structure fields:

- **functional correctness** lives on `m.ret` (alias `⟪m⟫`);
- **complexity bounds** live on `m.cost`.

The two are independent: changing the cost model never disturbs a correctness
proof, and refactoring the algorithm preserves cost annotations by
construction. The Boyer–Moore example ([[node:foundation.cost.examples.boyer_moore]])
proves a cost bound while deliberately *not* proving correctness, to exhibit
the decoupling.

## Lean declarations

- `CostM` — the two-field structure (`ret`, `cost`).
- `CostM.pure` `[Zero C]`, `CostM.bind` `[Add C]` — the monad primitives;
  `CostM.instMonad` `[Zero C] [Add C]` and `CostM.instLawfulMonad`
  `[AddMonoid C]` package them as a lawful monad.
- `CostM.tick c : CostM C PUnit` charges cost `c`; the `✓[c] body` macro is
  sugar for `do tick c; body`, and `✓ body` is `✓[1] body` (needs `[OfNat C 1]`).
- `CostM.Bounded alg size bound` `[LE C]` says `∀ i, (alg i).cost ≤ bound (size i)`;
  `CostM.IsPolyBounded` specializes to `C = ℕ` with `∃ c k, cost ≤ c · size^k`.

Parallel composition (`par`, `parList`) is documented separately in
[[node:foundation.cost.parallel]].

## References

- [Danielsson 2008] Nils Anders Danielsson, *Lightweight Semiformal Time
  Complexity Analysis for Purely Functional Data Structures*, POPL 2008. The
  writer-monad-over-a-monoid pattern for cost analysis.

## Provenance

- The monad core (`structure`, `Pure`/`Bind`/`Functor`/`Seq`, `Monad`/
  `LawfulMonad`, `tick`, the `✓` notation) is **adapted from `TimeM`** in
  [leanprover/cslib](https://github.com/leanprover/cslib),
  `Cslib/Algorithms/Lean/TimeM.lean` (Apache 2.0), by Sorrachai
  Yingchareonthawornhcai and Eric Wieser. EconCSLib generalizes "time" to a
  general cost monoid `C` and adds `par`/`parList`, `Bounded`/`IsPolyBounded`,
  and the `CoeHead` projection.
