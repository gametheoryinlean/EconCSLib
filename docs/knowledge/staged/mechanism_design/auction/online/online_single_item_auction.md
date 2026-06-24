---
id: mechanism_design.auction.online.single_item_auction
title: Online Single-Item (Posted-Price) Auction
kind: definition
status: staged
primary_topic: mechanism_design
topics:
  - mechanism_design
  - mechanism_design.auction
  - mechanism_design.auction.online
uses:
  - mechanism_design.auction.basic.formats
  - mechanism_design.transfer.mechanisms_with_transfers
lean:
  modules:
    - EconCSLib.Algorithm.Online
    - EconCSLib.Examples.Online.SingleItemAuction
  declarations:
    - Online.OnlineAlgorithm
    - Online.OnlineAlgorithm.run
    - Online.Auction.AuctionState
    - Online.Auction.SingleItemAuction
    - Online.Auction.SingleItemAuction.online
    - Online.Auction.SingleItemAuction.run
    - Online.Auction.SingleItemAuction.welfare
    - Online.Auction.SingleItemAuction.utility
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
tags:
  - auction
  - online-algorithm
  - posted-price
  - single-item
---

# Online Single-Item (Posted-Price) Auction

The **online single-item auction** sells one indivisible good to bidders
who arrive one at a time. While the item is unsold, the auctioneer posts a
take-it-or-leave-it price that may depend **only on the bids already seen**;
the current bidder either accepts (and the auction ends) or departs forever.
This is the running example of Roughgarden's *Twenty Lectures*, Problem 2.1.

The numeric type $F$ is any linearly ordered field; bids, posted prices,
valuations, and utilities all live in $F$.

## Model

A run is driven by the generic online-algorithm framework
`Online.OnlineAlgorithm Input State Output`, whose single field
`step : State → Input → State × Output` consumes one input and emits the
next state together with an optional output. The "no lookahead" discipline
is encoded in the **state**, not by an external promise: the auction state

$$
\mathrm{AuctionState}\,F \;=\; \mathsf{unsold}\,(\text{history} : \mathrm{List}\,F)
\;\mid\; \mathsf{sold}\,(\text{winner} : \mathbb{N})\,(\text{price} : F)
$$

carries in the `unsold` case exactly the list of previously rejected bids —
the only thing the pricing rule is allowed to read.

A `SingleItemAuction F` is then a single datum: a pricing rule
`price : List F → F` mapping the rejection history to the next posted price.
Its embedding into the framework is the field-free definition

```
A.online : OnlineAlgorithm F (AuctionState F) F
  init := .unsold []
  step
    | .unsold h, some b => let p := A.price h;
                           if p ≤ b then (.sold h.length p, some p)
                           else (.unsold (h ++ [b]), none)
    | .unsold h, none   => (.unsold h, none)
    | .sold w p, _      => (.sold w p, none)
```

The current bidder's $0$-indexed position equals `history.length`. The
winning rule is the weak inequality $p \le b$: a bidder clears the price iff
their bid is at least the posted price. `A.run bids` extracts the realised
sale price (`some p` if some bidder cleared, `none` if all were rejected)
by folding `A.online` over the bid list.

## Welfare and utility

For game-theoretic statements the $n$ bidders are indexed by
$\mathrm{Fin}\,n$, with a valuation profile $v : \mathrm{Fin}\,n \to F$ and a
bid profile $b : \mathrm{Fin}\,n \to F$ presented in arrival order.

- `A.welfare v b` is the **social welfare**: the valuation $v_j$ of whichever
  bidder $j$ first clears the posted price, or $0$ if every bidder is
  rejected. It is defined by a direct two-argument recursion `welfareFrom`
  over the `(vᵢ, bᵢ)` stream (carrying the rejection history separately) so
  that small concrete profiles reduce cleanly under `simp` — this is what
  makes the adversarial and secretary analyses tractable.
- `A.utility v b i` is bidder $i$'s quasi-linear payoff $v_i - p$ when $i$
  wins at price $p$, and $0$ otherwise. It factors through the state reached
  *before* bidder $i$ is processed, isolating $i$'s local view from the
  global trajectory.

## Why this shape

Keeping the entire embedding in the one `A.online` definition means the
auction inherits the framework's `run`, `runStatus`, and generic
`run_cons_*` recursion lemmas directly, with no duplicated step logic. The
two indexing conventions coexist on purpose: `List F` is the natural type
for the *streaming* input, while $\mathrm{Fin}\,n \to F$ is the natural type
for the *game-theoretic* layer (fixed agents, single-bidder deviations via
`Function.update`, random arrival via `Equiv.Perm (Fin n)`); the two are
bridged by `List.ofFn`.

Concrete instantiations fix the pricing rule and feed the three results of
Problem 2.1: truthfulness ([[mechanism_design.auction.online.dsic]]), the
deterministic impossibility
([[mechanism_design.auction.online.no_constant_competitive]]), and the
secretary guarantee
([[mechanism_design.auction.online.secretary_quarter_competitive]]).

## References

- [Roughgarden 2016, Lecture 2, Problem 2.1] Tim Roughgarden, *Twenty
  Lectures on Algorithmic Game Theory*, Cambridge University Press. Online
  posted-price single-item auction and its analysis.
- [AGT, Chapter 1, Section 1.3.2] Nisan, Roughgarden, Tardos, and Vazirani,
  *Algorithmic Game Theory*. Sealed-bid single-item auctions as the basic
  algorithmic game theory example.
