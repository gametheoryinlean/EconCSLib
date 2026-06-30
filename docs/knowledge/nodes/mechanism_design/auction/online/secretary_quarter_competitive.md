---
id: mechanism_design.auction.online.secretary_quarter_competitive
title: Sample-Then-Threshold Rule Is 1/4-Competitive
kind: theorem
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
    - Online.Auction.SampleThenThreshold.maxPairFold
    - Online.Auction.SampleThenThreshold.auction
    - Online.Auction.SampleThenThreshold.Favorable
    - Online.Auction.SampleThenThreshold.welfare_nonneg
    - Online.Auction.SampleThenThreshold.welfare_eq_max_of_favorable
    - Online.Auction.SampleThenThreshold.favorableSet
    - Online.Auction.SampleThenThreshold.favorableSet_card_ge
    - Online.Auction.SampleThenThreshold.competitive
verification:
  statement: accepted
  proof: accepted
  alignment: aligned
tags:
  - auction
  - online-algorithm
  - sample-then-threshold
  - competitive-ratio
  - random-order
---

# Sample-Then-Threshold Rule Is 1/4-Competitive

**Theorem (Roughgarden, Problem 2.1(c)).** Under a uniformly random
arrival order, the sample-then-threshold online auction obtains expected
welfare at least one quarter of the maximum valuation.

## The sample-then-threshold auction

Given $n$ bidders with values $v_1, \ldots, v_n$ and distinct identities
$b_1, \ldots, b_n$, the **sample-then-threshold auction** proceeds in
two phases:

1. **Observe phase** (positions $0, \ldots, \lfloor n/2 \rfloor - 1$).
   Set the threshold to $\top$, rejecting every bidder unconditionally.
   Record the lexicographic maximum $(p^*, \bar{b}^*)$ of the observed
   $(v, b)$ pairs.

2. **Select phase** (positions $\lfloor n/2 \rfloor, \ldots, n-1$).
   Post the threshold $(p^*, \bar{b}^*)$. Accept the first bidder
   whose $(v_i, b_i)$ lexicographically exceeds $(p^*, \bar{b}^*)$.

## Statement

For $n \ge 2$, distinct identities $b_i$, and nonneg valuations $v_i$:

$$
\frac{1}{4} \cdot \max_i v_i
\;\le\;
\mathbb{E}_\sigma\bigl[\mathrm{welfare}(v \circ \sigma,\; b \circ \sigma)\bigr],
$$

where $\sigma$ is a uniformly random permutation of the $n$ bidders.

## Proof

Let $M = \max_i v_i$. The argument follows the classical Dynkin
optimal-stopping skeleton.

### The favourable event

Call a permutation $\sigma$ **favourable** when:
- The **lex-argmax** bidder — the bidder with the largest $(v_i, b_i)$
  under lexicographic order — arrives in the select phase.
- The **lex-second** bidder — the second-largest under the same order —
  arrives in the observe phase.

Identity injectivity guarantees a unique lex-argmax and lex-second even
when values collide.

### Welfare equals $M$ on the favourable event

On a favourable permutation, the auction sells to the lex-argmax bidder
at welfare $M$. The argument processes bidders one at a time:

- **Every pre-argmax bidder in phase 2 is rejected.** The threshold
  $(p^*, \bar{b}^*)$ is at least as large as the lex-second bidder's
  pair (since the lex-second was observed in phase 1). Every non-argmax
  bidder is lex-strictly below the lex-second (by identity injectivity),
  hence lex-strictly below the threshold.

- **The lex-argmax bidder is accepted.** Their pair $(v_a, b_a)$
  lex-exceeds the threshold, since $v_a \ge p^*$ and, at a value tie,
  $b_a > \bar{b}^*$ (the argmax has the largest identity among
  value-tied bidders).

### The favourable event has probability $\ge 1/4$

Among all $n!$ permutations, the number of favourable ones is at least

$$
\lceil n/2 \rceil \cdot \lfloor n/2 \rfloor \cdot (n-2)!.
$$

This counts permutations where the lex-argmax occupies one of
$\lceil n/2 \rceil$ select-phase positions and the lex-second occupies
one of $\lfloor n/2 \rfloor$ observe-phase positions, with the remaining
$n - 2$ bidders in any order. The elementary inequality

$$
4 \cdot \lceil n/2 \rceil \cdot \lfloor n/2 \rfloor \ge n(n-1)
$$

then gives: $4 \cdot |\text{favourable}| \ge n!$, i.e.,
$\Pr[\text{favourable}] \ge 1/4$.

### Assembly

Welfare is nonneg on every permutation and equals $M$ on the favourable
set. Hence

$$
\mathbb{E}_\sigma[\mathrm{welfare}]
\;\ge\; \Pr[\text{favourable}] \cdot M
\;\ge\; \tfrac{1}{4} M.
$$

## Why identity injectivity, not value injectivity

The hypothesis is that identities $b_i$ are distinct, **not** that
values $v_i$ are distinct. This is the mathematically natural condition:
the competitive-ratio guarantee is about the mechanism, not an
accidental assumption on the input.

The lexicographic order on $(v_i, b_i)$ has a unique argmax and
second-max even when values collide, as long as identities are distinct.
The rejection proof for pre-argmax bidders uses lex-strict inequality,
which needs identity distinctness at value ties — not global value
injectivity.

This is why the auction uses a lexicographic threshold rather than a
simple value threshold: without the identity component, the theorem
would require the unnatural hypothesis that all bidders have distinct
values
([[mechanism_design.auction.online.single_item_auction]]).

## Why it matters

Together with the deterministic impossibility
([[mechanism_design.auction.online.no_constant_competitive]]), this
closes Problem 2.1: worst-case arrival admits no constant competitive
ratio, yet random-order arrival restores one. The technique — sample a
constant fraction of the input to calibrate a threshold, then accept
the first item that exceeds it — is the single-item instance of the
broader class of online selection algorithms with random-order
guarantees.

## Remarks

### Lean formalization

The auction is `SampleThenThreshold.auction n`. The threshold in the
select phase is computed by `maxPairFold h`, which folds the rejection
history to find the lexicographic maximum of $(v, b)$ pairs. The
favourable event is a structure `Favorable g v σ` recording the
position constraints and lex-ordering witnesses. The main proof chain:
`welfare_eq_max_of_favorable` (welfare $= M$ on favourable
permutations), `favorableSet_card_ge` (counting), and `competitive`
(assembly).

## References

- [Roughgarden 2016, Lecture 2, Problem 2.1(c)] Tim Roughgarden, *Twenty
  Lectures on Algorithmic Game Theory*, Cambridge University Press.
  Random-order analysis of the online auction.
