---
id: mechanism_design.auction.online.dsic
title: Truthful Bidding Is Dominant in the Online Auction
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
    - Online.Auction.SingleItemAuction.stateBeforeStep
    - Online.Auction.SingleItemAuction.stateBeforeStep_update_self
    - Online.Auction.SingleItemAuction.dsic
verification:
  statement: accepted
  proof: accepted
  alignment: aligned
tags:
  - auction
  - online-algorithm
  - dsic
  - weakly-dominant
  - posted-price
---

# Truthful Bidding Is Dominant in the Online Auction

**Theorem (Roughgarden, Problem 2.1(a)).** In the online single-item
auction ([[mechanism_design.auction.online.single_item_auction]]) — for
*any* threshold rule — truthful bidding is a weakly dominant strategy
for every bidder.

## Statement

For every threshold rule $T$, every arrival profile of $n$ bidders with
true valuations $v_1, \ldots, v_n$, and every bidder $i$:

$$
u_i(\text{misreport}) \;\le\; u_i(\text{truthful}).
$$

That is, bidding $b_i = v_i$ weakly dominates any alternative bid,
regardless of the other bidders' actions and regardless of the threshold
rule.

## Proof

The argument has two independent parts.

### The price bidder $i$ faces is independent of $b_i$

The threshold at position $i$ is computed from the rejection history
$(b_1, v_1), \ldots, (b_{i-1}, v_{i-1})$ — the bids of bidders who
arrived *before* $i$. Replacing bidder $i$'s bid changes nothing about
this history:

$$
T\bigl((b_1,v_1),\ldots,(b_{i-1},v_{i-1})\bigr) \text{ is the same
whether $i$ bids } v_i \text{ or any } b_i'.
$$

This is the structural heart of the result: a posted-price mechanism
cannot let a bidder influence their own price.

### Single-bidder optimisation at a fixed threshold

Given a fixed threshold $(p, \bar{b})$, bidder $i$'s payoff is:

- $v_i - p$ if the lexicographic condition
  $p < b_i \lor (p = b_i \land \bar{b} \le \mathrm{id}_i)$ holds,
- $0$ otherwise.

Truthful bidding $b_i = v_i$ accepts exactly when the surplus
$v_i - p$ is nonneg: if $v_i > p$, the bidder accepts and earns a
positive surplus; if $v_i < p$, the bidder rejects and avoids a loss.
At the boundary $v_i = p$, the surplus is zero, so accepting or
rejecting are both optimal. This is the best any strategy can do.

## Why it matters

Truthfulness is **format-independent**: it holds for *every*
history-dependent threshold rule, not just a particular one. This is the
defining advantage of posted-price mechanisms over sealed-bid formats
like the second-price auction
([[mechanism_design.auction.basic.second_price_dsic]]) — truthfulness
follows from the order of moves (threshold posted first, bid observed
second) rather than from a carefully engineered payment rule.

This result licenses treating reported bids as true valuations in the
welfare analyses of parts (b)
([[mechanism_design.auction.online.no_constant_competitive]]) and (c)
([[mechanism_design.auction.online.secretary_quarter_competitive]]).

## Remarks

### Lean formalization

The price-independence step is `stateBeforeStep_update_self`: the auction
state before processing bidder $i$ is unchanged by replacing $i$'s entry
in the profile. The single-bidder optimisation is `local_dsic`, which is
parametric in the tie-breaking condition — it works for any threshold
rule. The main theorem `dsic` combines both steps.

## References

- [Roughgarden 2016, Lecture 2, Problem 2.1(a)] Tim Roughgarden, *Twenty
  Lectures on Algorithmic Game Theory*, Cambridge University Press.
  Dominant-strategy truthfulness of online posted-price auctions.
