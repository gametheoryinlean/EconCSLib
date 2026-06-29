---
id: mechanism_design.auction.online.secretary_weak_comparison_needle
title: Weak Value Comparison Degrades to 1/n on the Needle Profile
kind: example
status: proved
primary_topic: mechanism_design
topics:
  - mechanism_design
  - mechanism_design.auction
  - mechanism_design.auction.online
uses:
  - mechanism_design.auction.online.single_item_auction
  - mechanism_design.auction.online.secretary_quarter_competitive
  - mechanism_design.auction.online.secretary_strict_comparison_fails
lean:
  modules:
    - EconCSLib.Examples.Online.SingleItemAuction
  declarations:
    - Online.Auction.WeakComparison.auction
    - Online.Auction.WeakComparison.maxPairFold_fst_zero
    - Online.Auction.WeakComparison.welfare_eq_zero_needle_last
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
  - needle
---

# Weak Value Comparison Degrades to 1/n on the Needle Profile

**Counterexample.** If the secretary auction uses weak value comparison
$p \le v$ as the acceptance rule (accepting all ties), it achieves
expected welfare only $(1/n) \cdot \max v$ on the needle profile — which
is **not** a constant competitive ratio.

This complements the strict-comparison counterexample
([[mechanism_design.auction.online.secretary_strict_comparison_fails]]),
which gives welfare $= 0$ outright. Weak comparison avoids that extreme
failure but introduces a subtler one: it cannot distinguish a worthless
bidder who happens to match a zero threshold from the valuable bidder
who genuinely exceeds it.

## Construction

Fix $M > 0$ and $n \ge 2$. The **needle profile** is

$$
v = (M,\, 0,\, 0,\, \ldots,\, 0).
$$

One *needle* bidder has value $M$; the remaining $n - 1$ *haystack*
bidders have value $0$. The secretary rule observes
$\lfloor n/2 \rfloor$ bidders, then posts the observed maximum as the
threshold. Under weak comparison, the acceptance test is $p \le v_i$.

### Case analysis over the needle's arrival position

Under a uniformly random permutation, the needle is equally likely to
occupy any of the $n$ positions.

**Case 1: needle in the observe phase** (position
$k < \lfloor n/2 \rfloor$). The threshold value becomes $\ge M$. Every
phase-2 bidder has value $0$, and $M \le 0$ is false. Nobody clears.
Welfare $= 0$.

**Case 2: needle in phase 2, but not first** (position
$k > \lfloor n/2 \rfloor$). All observed bidders have value $0$, so the
threshold drops to $p = 0$. The first phase-2 bidder is a haystack
bidder with value $0$; the test $0 \le 0$ is **true**. This haystack
bidder is accepted with welfare $= 0$. The needle never gets a chance.

**Case 3: needle is first in phase 2** (position
$k = \lfloor n/2 \rfloor$). Threshold is $p = 0$. The needle faces
$0 \le M$, which is true. Accepted. Welfare $= M$.

### Expected welfare is $M/n$

Exactly one of $n$ equally likely positions (Case 3) gives welfare $M$;
all others give $0$. Hence

$$
\mathbb{E}[\mathrm{welfare}]
= \frac{1}{n} \cdot M
= \frac{1}{n} \cdot \max_i v_i.
$$

For any constant $c > 0$, choosing $n > 1/c$ gives
$\mathbb{E}[\mathrm{welfare}] < c \cdot \max v$.

## Why it fails

The root cause is that weak comparison **cannot distinguish** a haystack
bidder matching a zero threshold by coincidence from the needle bidder
genuinely exceeding it. When $p = 0$ and a haystack bidder has $v = 0$,
the test $0 \le 0$ is vacuously true — the first phase-2 arrival wins
regardless of value.

## How lexicographic tie-breaking fixes this

With the full lexicographic threshold
([[mechanism_design.auction.online.secretary_quarter_competitive]]),
Case 2 plays out differently:

- The threshold has value $p = 0$ and identity component
  $\bar{b} = b_{\max}$, the largest identity seen in phase 1.
- A haystack bidder $j$ arriving first in phase 2 faces the value tie
  $p = v_j = 0$, so acceptance falls to the identity test
  $\bar{b} \le b_j$. But $b_j < b_{\max} = \bar{b}$ (by identity
  injectivity — the largest-identity haystack bidder was observed in
  phase 1 on the favourable event). The haystack bidder is **rejected**.
- This rejection continues for every subsequent haystack bidder, until
  the needle arrives. The needle clears strictly: $0 < M$. Welfare
  $= M$.

On the favourable event (probability $\ge 1/4$), the lex rule rejects
all haystack bidders and accepts the needle, giving expected welfare
$\ge M/4$.

## Summary

| Acceptance rule | Needle welfare | Competitive? |
|-----------------|---------------:|:------------:|
| $p < v$ (strict) | $0$ always | **No** ([[mechanism_design.auction.online.secretary_strict_comparison_fails]]) |
| $p \le v$ (weak) | $M/n$ in expectation | **No** (this) |
| lex | $\ge M/4$ in expectation | **Yes** ([[mechanism_design.auction.online.secretary_quarter_competitive]]) |

## Remarks

### Lean formalization

Weak comparison is modelled by `WeakComparison.auction`, which sets the
identity component of the threshold to $\bot$ — since $\bot \le b$
holds for all $b$, the acceptance condition degenerates to $p \le v$.
The lemma `maxPairFold_fst_zero` shows that the threshold value is $0$
when all observed bids have value $0$. The theorem
`welfare_eq_zero_needle_last` proves welfare $= 0$ for the $n = 3$ case
with the needle at the last position (Case 2).

## References

- [Roughgarden 2016, Lecture 2, Problem 2.1(c)] Tim Roughgarden, *Twenty
  Lectures on Algorithmic Game Theory*, Cambridge University Press.
  Secretary analysis (stated for distinct values, which excludes the
  needle profile).
