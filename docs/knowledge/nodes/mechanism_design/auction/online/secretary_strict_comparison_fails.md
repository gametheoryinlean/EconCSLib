---
id: mechanism_design.auction.online.secretary_strict_comparison_fails
title: Strict Value Comparison Breaks the Secretary Guarantee
kind: counterexample
status: proved
primary_topic: mechanism_design
topics:
  - mechanism_design
  - mechanism_design.auction
  - mechanism_design.auction.online
uses:
  - mechanism_design.auction.online.single_item_auction
  - mechanism_design.auction.online.secretary_quarter_competitive
lean:
  modules:
    - EconCSLib.Examples.Online.SingleItemAuction
  declarations:
    - Online.Auction.StrictComparison.auction
    - Online.Auction.StrictComparison.welfare_eq_zero
verification:
  statement: accepted
  proof: accepted
  alignment: aligned
tags:
  - auction
  - online-algorithm
  - secretary
  - counterexample
  - competitive-ratio
---

# Strict Value Comparison Breaks the Secretary Guarantee

**Counterexample.** If the online single-item auction
([[mechanism_design.auction.online.single_item_auction]]) uses strict
value comparison only — equivalently, sets the threshold identity
component to `⊤ : B` (`StrictComparison.auction`) so that the acceptance
condition `threshold h ≤ ↑(toLex (v, b))` degenerates to `p < v`
(since `⊤ ≤ b` fails for all `b < ⊤`) — then the secretary rule is
**not** $1/4$-competitive, even for $n = 2$ and injective identities.

## Construction

Fix any $M > 0$ and set $n = 2$, $v = (M, M)$ (two bidders with identical
value). Define the secretary auction with strict comparison (identity component `⊤`):

```
threshold h := if h.length < 1 then ⊤
               else ↑(toLex ((maxPairFold h).1, (⊤ : B)))
```

### Welfare on every permutation is zero

There are two arrival orders.

- **$\sigma = \mathrm{id}$:** Bidder $0$ arrives first (observe phase,
  price $\top$, rejected). Threshold becomes $M$. Bidder $1$ arrives
  second with value $M$; strict comparison $M < M$ fails, so bidder $1$
  is rejected. Welfare $= 0$.

- **$\sigma = (0\;1)$:** Bidder $1$ arrives first (observe phase,
  rejected). Threshold becomes $M$. Bidder $0$ arrives with value $M$;
  $M < M$ fails, rejected. Welfare $= 0$.

### The bound is violated

$$
\frac{1}{2!}\sum_{\sigma} \mathrm{welfare}(\sigma) = 0
\;<\; \frac{1}{4} \cdot M = \frac{1}{4}\cdot\max_i v_i.
$$

## Why it fails

Strict value comparison cannot distinguish between the observed bidder
and a later bidder with the **same** value. In the secretary skeleton,
the threshold is set to the maximum observed value; any later bidder
whose value equals this maximum must be accepted (they are "as good as
the best seen so far"), but strict comparison rejects them.

The lexicographic threshold
([[mechanism_design.auction.online.single_item_auction]]) resolves this:
in the secretary auction, the threshold identity component is set to the
identity of the lex-max observed bidder, so a later bidder with the same
value but a *higher* identity clears the threshold and is accepted. This
is exactly the acceptance condition
`threshold h ≤ ↑(toLex (v, b))`.

## Comparison with weak value comparison

Setting the threshold identity component to `⊥ : B` instead of `⊤`
(`WeakComparison.auction`) recovers weak comparison $p \le v$, under
which all bidders meeting the threshold are accepted. With weak
comparison and the equal-value profile above, both permutations give
welfare $= M = \max v$, so this particular failure is avoided.

However, weak comparison is **also not constant-competitive**: on the
needle profile $v = (M, 0, \ldots, 0)$, the threshold drops to $0$ and
weak comparison accepts the first phase-2 arrival unconditionally (since
$0 \le 0$), giving expected welfare only $(1/n) \cdot M$
([[mechanism_design.auction.online.secretary_weak_comparison_needle]]).
The secretary auction, which sets the identity component to the observed
lex-max identity, resolves both failure modes.

## Summary

| Acceptance rule           | Threshold identity component | Competitive? |
|---------------------------|------------------------------|--------------|
| $p < v$ (strict only)     | `⊤ : B` (`StrictComparison.auction`) | **No** — welfare $= 0$ always (this counterexample) |
| $p \le v$ (weak only)     | `⊥ : B` (`WeakComparison.auction`) | **No** — welfare $= M/n$ on needle ([[mechanism_design.auction.online.secretary_weak_comparison_needle]]) |
| lex (proper threshold)    | `(maxPairFold h).2` | **Yes** — welfare $\ge M/4$ ([[mechanism_design.auction.online.secretary_quarter_competitive]]) |

The lex acceptance rule is the unique design among these three that
achieves a constant competitive ratio with identity injectivity alone.

## References

- [Roughgarden 2016, Lecture 2, Problem 2.1(c)] Tim Roughgarden, *Twenty
  Lectures on Algorithmic Game Theory*, Cambridge University Press.
  Secretary analysis of the online auction (stated for distinct values).
