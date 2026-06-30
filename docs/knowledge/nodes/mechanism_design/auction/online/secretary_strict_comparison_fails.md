---
id: mechanism_design.auction.online.secretary_strict_comparison_fails
title: Strict Value Comparison Breaks the Secretary Guarantee
kind: example
status: proved
primary_topic: mechanism_design
topics:
  - mechanism_design
  - mechanism_design.auction
  - mechanism_design.auction.online
uses:
  - mechanism_design.auction.online.single_item_auction
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

**Counterexample.** If the secretary auction uses strict value
comparison $p < v$ as the acceptance rule (ignoring identities
entirely), it is **not** $1/4$-competitive — even for $n = 2$ bidders
with injective identities.

## Construction

Fix $M > 0$ and set $n = 2$ with $v_0 = v_1 = M$ (two bidders with
identical value). The secretary rule observes the first bidder and sets
threshold value $p = M$.

### Welfare is zero on every arrival order

- **Bidder $0$ arrives first.** Observed and rejected (observe phase).
  Threshold becomes $p = M$. Bidder $1$ arrives with value $M$; strict
  test $M < M$ is **false**. Rejected. Welfare $= 0$.

- **Bidder $1$ arrives first.** Observed and rejected. Threshold becomes
  $p = M$. Bidder $0$ arrives with value $M$; $M < M$ is **false**.
  Rejected. Welfare $= 0$.

### The competitive bound is violated

$$
\frac{1}{2!}\sum_{\sigma} \mathrm{welfare}(\sigma) = 0
\;<\; \frac{1}{4} \cdot M = \frac{1}{4} \cdot \max_i v_i.
$$

## Why it fails

Strict comparison cannot distinguish the observed bidder from a later
bidder with the **same** value. In the secretary skeleton, the threshold
is set to the maximum observed value. Any later bidder whose value
*equals* this maximum should be accepted — they are "as good as the best
seen so far" — but strict comparison $p < v$ rejects them at the tie.

## How lexicographic tie-breaking fixes this

The lexicographic acceptance rule
([[mechanism_design.auction.online.single_item_auction]]) tests
$p < v_i \lor (p = v_i \land \bar{b} \le b_i)$, where $\bar{b}$ is the
identity of the lex-max observed bidder. At the value tie $p = v_i = M$,
acceptance falls to the identity comparison $\bar{b} \le b_i$. If the
arriving bidder has a higher identity than the threshold, they clear —
breaking the $M < M$ deadlock.

## Comparison with weak comparison

Replacing strict comparison with weak comparison $p \le v$ (accept all
ties) avoids this failure: with $v_0 = v_1 = M$, both arrival orders
give welfare $M$.

However, weak comparison has its own failure mode on the needle profile
$v = (M, 0, \ldots, 0)$: the threshold drops to $0$ and the test
$0 \le 0$ accepts the first phase-2 arrival regardless of value, giving
expected welfare only $(1/n) \cdot M$
([[mechanism_design.auction.online.secretary_weak_comparison_needle]]).

## Summary

| Acceptance rule | Equal-value welfare | Needle welfare | Competitive? |
|-----------------|--------------------:|---------------:|:------------:|
| $p < v$ (strict) | $0$ always | — | **No** (this) |
| $p \le v$ (weak) | $M$ | $M/n$ | **No** |
| lex | $M$ | $\ge M/4$ | **Yes** |

The lexicographic rule is the only one among these three that achieves a
constant competitive ratio
([[mechanism_design.auction.online.secretary_quarter_competitive]]).

## Remarks

### Lean formalization

Strict comparison is modelled by `StrictComparison.auction`, which sets
the identity component of the threshold to $\top$ — since $\top \le b$
fails for all $b < \top$, the acceptance condition degenerates to
$p < v$. The theorem `welfare_eq_zero` proves welfare $= 0$ for
$n = 2$, constant values, and any identities below $\top$.

## References

- [Roughgarden 2016, Lecture 2, Problem 2.1(c)] Tim Roughgarden, *Twenty
  Lectures on Algorithmic Game Theory*, Cambridge University Press.
  Secretary analysis (stated for distinct values, which avoids this
  failure).
