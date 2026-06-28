---
id: mechanism_design.auction.online.secretary_weak_comparison_needle
title: Weak Value Comparison Degrades to 1/n on the Needle Profile
kind: counterexample
status: partly_proved
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
  proof: partly_proved
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

**Counterexample.** If the online single-item auction
([[mechanism_design.auction.online.single_item_auction]]) uses weak value
comparison $p \le v$ — equivalently, sets the threshold identity
component to `⊥ : B` (`WeakComparison.auction`) so that the acceptance
condition degenerates to $p \le v_i$ (since `⊥ ≤ b` holds for all `b`)
— then the secretary rule achieves expected welfare only
$(1/n) \cdot \max v$ on the *needle profile*, which is **not** a
constant competitive ratio.

This complements the strict-comparison counterexample
([[mechanism_design.auction.online.secretary_strict_comparison_fails]]),
which gives welfare $= 0$ outright. Weak comparison avoids that extreme
failure but introduces a subtler one: the threshold is too permissive at
value ties, letting the wrong bidder win.

## Construction

Fix $M > 0$ and set

$$
v = (M,\, 0,\, 0,\, \ldots,\, 0), \qquad n \ge 2.
$$

One *needle* bidder has value $M$; the remaining $n - 1$ *haystack*
bidders have value $0$. Define the secretary auction with weak comparison:

```
threshold h := if h.length < n / 2 then ⊤
               else ↑(toLex ((maxPairFold h).1, (⊥ : B)))
```

Since the identity component is `⊥` and `⊥ ≤ b` holds for all `b : B`,
the acceptance condition `threshold h ≤ ↑(toLex (v, b))` simplifies to
$p \le v$.

### Case analysis over the needle's arrival position

Under a uniformly random permutation $\sigma$, the needle bidder is
equally likely to occupy any of the $n$ positions.

**Case 1: needle in the observe phase** (position $k < \lfloor n/2 \rfloor$).

`maxPairFold` processes the needle's entry $(b, M)$ and returns a pair
with first component $\ge M$. The threshold is $\ge M$. Every phase-2
bidder has value $0$, and $M \le 0$ is false. Nobody clears. Welfare
$= 0$.

**Case 2: needle in phase 2, but not first** (position
$k > \lfloor n/2 \rfloor$).

All phase-1 bidders have value $0$. `maxPairFold` returns $(0, g_{\max})$
where $g_{\max}$ is the largest observed identity. The threshold value is
$0$. The bidder at position $\lfloor n/2 \rfloor$ — a haystack bidder
with value $0$ — faces the test $0 \le 0$, which is **true**. They are
accepted immediately with welfare $= 0$. The needle never gets a chance
to bid.

**Case 3: needle is first in phase 2** (position
$k = \lfloor n/2 \rfloor$).

Threshold value is $0$. The needle faces $0 \le M$, which is true.
Accepted. Welfare $= M$.

### Expected welfare is $M/n$

Exactly one of $n$ equally likely positions gives welfare $M$; all others
give welfare $0$. Hence

$$
\mathbb{E}[\text{welfare}]
= \frac{1}{n} \cdot M
= \frac{1}{n} \cdot \max_i v_i.
$$

For any constant $c > 0$, choosing $n > 1/c$ gives
$\mathbb{E}[\text{welfare}] < c \cdot \max v$, so weak comparison
achieves **no constant competitive ratio** on this profile family.

## Why lex comparison avoids this

With the lex acceptance rule and the full threshold
`↑(toLex (maxPairFold h))`, the secretary auction
([[mechanism_design.auction.online.secretary_quarter_competitive]])
behaves differently in Case 2:

- Threshold value $= 0$, identity component $= g_{\max}$ (the largest
  identity seen in phase 1).
- A haystack bidder $j$ at position $\lfloor n/2 \rfloor$ faces the
  threshold test: `toLex (0, g_max) ≤ toLex (0, g_j)`, i.e. $g_{\max} \le g_j$.
  Since the lex-second bidder (highest-identity haystack bidder) was
  placed in phase 1 by the favourable event, $g_j < g_{\text{second}}
  \le g_{\max}$, so $g_{\max} \le g_j$ **fails**. The haystack bidder
  is **rejected**.
- This rejection continues for every subsequent haystack bidder, until
  the needle arrives and clears the value threshold strictly ($0 < M$).
  Welfare $= M$.

On the favourable event (probability $\ge 1/4$), the lex rule rejects
all haystack bidders and accepts the needle, giving welfare $= M$. The
overall guarantee is $\ge (1/4) \cdot M$.

## The mechanism of failure

The root cause is that weak comparison **cannot distinguish** between a
haystack bidder matching the threshold by coincidence and the needle
bidder genuinely exceeding it. When the threshold is $0$ and all
haystack values are $0$, the test $0 \le 0$ is vacuously true — the
first phase-2 arrival wins regardless of their value.

The identity component of the lexicographic threshold breaks this
degeneracy: by requiring the bidder's identity to also clear a threshold
derived from the observed maximum, the auction filters out haystack
bidders whose only "qualification" is matching a zero value threshold.
This is exactly the design motivation behind `SingleItemAuction`'s
single lexicographic threshold
([[mechanism_design.auction.online.single_item_auction]]).

## Summary table

| Acceptance rule | Needle profile welfare | Constant competitive? |
|-----------------|----------------------|----------------------|
| $p < v$ (strict, identity = `⊤`) | $0$ always | **No** ([[mechanism_design.auction.online.secretary_strict_comparison_fails]]) |
| $p \le v$ (weak, identity = `⊥`) | $M/n$ in expectation | **No** (this counterexample) |
| lex (proper threshold) | $\ge M/4$ in expectation | **Yes** ([[mechanism_design.auction.online.secretary_quarter_competitive]]) |

## References

- [Roughgarden 2016, Lecture 2, Problem 2.1(c)] Tim Roughgarden, *Twenty
  Lectures on Algorithmic Game Theory*, Cambridge University Press.
  Secretary analysis (stated for distinct values, which excludes the
  needle profile).
