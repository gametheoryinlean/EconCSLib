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
*any* history-dependent pricing rule — truthful bidding $b_i = v_i$ is a
weakly dominant strategy for every bidder.

Formally, for every pricing rule $A$, every arrival/bid profile
$f : \mathrm{Fin}\,n \to B \times F$, every true-valuation profile
$v : \mathrm{Fin}\,n \to F$, and every bidder $i$,

$$
A.\mathrm{utility}(f,\, v,\, i)
\;\le\;
A.\mathrm{utility}\bigl(f[i \mapsto ((f\,i).1,\, v_i)],\; v,\; i\bigr).
$$

## Proof

The argument is a locality observation followed by a single-variable
optimisation.

1. **The posted price bidder $i$ faces is independent of $b_i$.**
   `stateBeforeStep f i` runs only the first $i$ bids, none of which is
   $b_i$, so
   $$
   \mathrm{stateBeforeStep}\,(f[i \mapsto x])\, i
   \;=\; \mathrm{stateBeforeStep}\, f\, i
   $$
   for every alternative entry $x$ (`stateBeforeStep_update_self`). This
   is the structural heart of the result: a posted-price rule cannot let
   a bidder move their own price.

2. **Single-bidder optimisation at a fixed price.** With price $p$ and
   tie-breaking condition `tie_ok` fixed, bidder $i$'s payoff is
   $v_i - p$ if the lex condition $p < b_i \lor (p = b_i \land
   \mathit{tie\_ok})$ holds, and $0$ otherwise. Truthful bidding
   $b_i = v_i$ accepts exactly when the surplus is nonneg, which is
   optimal. This is the `local_dsic` lemma, parametric in `tie_ok`.

`dsic` combines the two steps: rewrite via `stateBeforeStep_update_self`,
then apply `local_dsic` with `tie_ok := A.bar h ≤ ↑(f i).1`.

## Why it matters

The truthfulness here is **format-independent**: it holds for *every*
history-dependent posted-price rule, not just a particular one. This is
the defining advantage of posted-price mechanisms over the sealed-bid
second-price auction ([[mechanism_design.auction.basic.second_price_dsic]])
— truthfulness comes for free from the order of moves (price first, bid
second) rather than from a carefully engineered payment rule. It is what
licenses treating reported bids as true valuations in the welfare analyses
of parts (b) ([[mechanism_design.auction.online.no_constant_competitive]])
and (c) ([[mechanism_design.auction.online.secretary_quarter_competitive]]).

## References

- [Roughgarden 2016, Lecture 2, Problem 2.1(a)] Tim Roughgarden, *Twenty
  Lectures on Algorithmic Game Theory*, Cambridge University Press.
  Dominant-strategy truthfulness of online posted-price auctions.
