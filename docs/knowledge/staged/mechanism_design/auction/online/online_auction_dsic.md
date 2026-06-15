---
id: mechanism_design.auction.online.dsic
title: Truthful Bidding Is Dominant in the Online Auction
kind: theorem
status: staged
primary_topic: mechanism_design
topics:
  - mechanism_design
  - mechanism_design.auction
  - mechanism_design.auction.online
uses:
  - mechanism_design.auction.online.single_item_auction
  - mechanism_design.basic.dsic_predicate
  - game_theory.strategic_game.weakly_dominant_strategy
lean:
  modules:
    - EconCSLib.Examples.Online.SingleItemAuction
  declarations:
    - Online.Auction.SingleItemAuction.stateBeforeStep
    - Online.Auction.SingleItemAuction.stateBeforeStep_update_self
    - Online.Auction.SingleItemAuction.dsic
    - Online.Auction.SingleItemAuction.mechanism
    - Online.Auction.SingleItemAuction.mechanism_isDSIC
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
*any* history-dependent pricing rule — truthful bidding $b_i = v_i$ is a
weakly dominant strategy for every bidder.

Formally, for every pricing rule $A$, every valuation/bid profile
$v, b : \mathrm{Fin}\,n \to F$, and every bidder $i$,

$$
A.\mathrm{utility}(v,\, b,\, i)
\;\le\;
A.\mathrm{utility}\bigl(v,\; b[i \mapsto v_i],\; i\bigr).
$$

## Proof

The whole argument is a locality observation, named in Lean by
`stateBeforeStep b i` — the state the auction is in *just before* bidder $i$
is processed, obtained by running only the bids of the earlier bidders
$j < i$.

1. **The posted price bidder $i$ faces is independent of $b_i$.**
   `stateBeforeStep b i` runs only the first $i$ bids, none of which is
   $b_i$, so
   $$
   \mathrm{stateBeforeStep}\,(b[i \mapsto x])\, i
   \;=\; \mathrm{stateBeforeStep}\, b\, i
   $$
   for every alternative bid $x$ (`stateBeforeStep_update_self`). This is the
   structural heart of the result: a posted-price rule cannot let a bidder
   move their own price.

2. **Single-bidder optimisation at a fixed price.** With the price $p$ thus
   fixed, bidder $i$'s payoff is $v_i - p$ if they bid at least $p$ and $0$
   otherwise. Truthful bidding $b_i = v_i$ accepts exactly when $v_i \ge p$,
   i.e. exactly when the surplus $v_i - p$ is nonnegative, so it attains
   $\max(v_i - p, 0)$ — weakly better than any deviation.

`dsic` states the inequality directly at the utility level;
`mechanism_isDSIC` lifts the same fact to the generic
`MechanismWithTransfers`-level DSIC predicate
([[mechanism_design.basic.dsic_predicate]]) for the induced direct mechanism
`A.mechanism n`.

## Why it matters

The truthfulness here is **format-independent**: it holds for *every*
history-dependent posted-price rule, not just a particular one. This is the
defining advantage of posted-price mechanisms over the sealed-bid
second-price auction ([[mechanism_design.auction.basic.second_price_dsic]]) —
truthfulness comes for free from the order of moves (price first, bid
second) rather than from a carefully engineered payment rule. It is what
licenses treating reported bids as true valuations in the welfare analyses
of parts (b) and (c).

## References

- [Roughgarden 2016, Lecture 2, Problem 2.1(a)] Tim Roughgarden, *Twenty
  Lectures on Algorithmic Game Theory*, Cambridge University Press.
  Dominant-strategy truthfulness of online posted-price auctions.
