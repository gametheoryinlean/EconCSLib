---
id: mechanism_design.auction.online.single_item_auction
title: Online Single-Item (Posted-Price) Auction
kind: definition
status: formalized
primary_topic: mechanism_design
topics:
  - mechanism_design
  - mechanism_design.auction
  - mechanism_design.auction.online
uses:
  - mechanism_design.auction.basic.formats
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
    - Online.Auction.SingleItemAuction.welfareAux
    - Online.Auction.SingleItemAuction.welfare
    - Online.Auction.SingleItemAuction.stateBeforeStep
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
who arrive one at a time. While the item is unsold, the auctioneer posts
a take-it-or-leave-it price that may depend **only on the bids already
seen**; the current bidder either accepts (and the auction ends) or departs
forever. This is the running example of Roughgarden's *Twenty Lectures*,
Problem 2.1.

## Model

The type `SingleItemAuction B F` is parameterised by an identity type `B`
and a numeric type `F` (any linearly ordered field). Each bidder presents
a pair `(b, v) : B × F`, and the auction is defined by a single field:

- `threshold : List (B × F) → WithTop (Lex (F × B))` — a lexicographic
  threshold combining value and identity.

The field reads the full history of rejected `(identity, value)` pairs.
The threshold `⊤` rejects unconditionally; `↑(toLex (p, b))` accepts
when `threshold h ≤ ↑(toLex (v_i, b_i))`, which by `Prod.Lex.le_iff`
gives the **lexicographic** condition:

$$
p < v_i \;\lor\; (p = v_i \;\land\; b \le b_i).
$$

A run is driven by the generic online-algorithm framework
`Online.OnlineAlgorithm Input State Output`, whose single field
`step : State → Option Input → State × Option Output` consumes one input
and emits the next state together with an optional output. The auction
state

$$
\mathrm{AuctionState}\,B\,F \;=\; \mathsf{unsold}\,(\text{history} :
\mathrm{List}\,(B \times F))
\;\mid\; \mathsf{sold}\,(\text{winner} : \mathbb{N})\,(\text{price} : F)
$$

carries in the `unsold` case exactly the list of previously rejected
$(identity, value)$ pairs — the only thing the pricing rule is allowed to
read. The embedding into the framework is `A.online`:

```
step
  | .unsold h, some (bi, vi) => match A.threshold h with
                           | ⊤     => (.unsold (h ++ [(bi, vi)]), none)
                           | ↑t    => if t ≤ toLex (vi, bi)
                                      then (.sold h.length (ofLex t).1, some (ofLex t).1)
                                      else (.unsold (h ++ [(bi, vi)]), none)
  | .unsold h, none   => (.unsold h, none)
  | .sold w p, _      => (.sold w p, none)
```

## Welfare and utility

For game-theoretic statements the $n$ bidders are indexed by
$\mathrm{Fin}\,n$, with a profile $f : \mathrm{Fin}\,n \to B \times F$
presented in arrival order.

- `A.welfare f` is the **social welfare**: the value $(f\,j).2$ of
  whichever bidder $j$ first clears the posted price (lexicographically),
  or $0$ if every bidder is rejected. It is defined via `welfareAux`,
  a direct recursion carrying the rejection history, so that small
  concrete profiles reduce cleanly under `simp`.
- `A.utility f v i` is bidder $i$'s quasi-linear payoff $v_i - p$ when
  $i$ wins at price $p$, and $0$ otherwise. It factors through
  `stateBeforeStep`, the state reached *before* bidder $i$ is processed,
  isolating $i$'s local view from the global trajectory.

## Remarks

### Why a single lexicographic threshold?

A natural first design would use a simpler threshold in `WithTop F`
(value only) and require **value injectivity** (`Function.Injective v`)
in the secretary theorem. But value injectivity is mathematically
unnatural: the competitive-ratio guarantee is about the mechanism, not
about an accidental distinctness hypothesis on valuations.

An earlier design used two separate fields (`price` and `bar`) to encode
the value threshold and identity tie-breaker independently. The current
single-field design `threshold : List (B × F) → WithTop (Lex (F × B))`
is equivalent but cleaner: `Lex (F × B)` packages both components into
a single lexicographic pair, and the acceptance test reduces to a single
comparison `threshold h ≤ ↑(toLex (v_i, b_i))`.

The secretary auction
([[mechanism_design.auction.online.secretary_quarter_competitive]])
requires **identity injectivity** (`Function.Injective g`) — a
structural property of the bidder-labelling system, not a restriction
on valuations. The lex acceptance rule resolves value ties by comparing
identities, so:

- **Tie-breaking is internal.** Value ties at the threshold are
  resolved by the identity component of the threshold, without an
  external tie-breaking oracle or an arbitrary selection.
- **DSIC is format-independent.** The `local_dsic` lemma abstracts
  the tie-breaking condition as a `Prop` parameter `tie_ok`; truthful
  bidding is optimal regardless of how ties are broken
  ([[mechanism_design.auction.online.dsic]]).
- **The secretary analysis uses `g`-injectivity, not `v`-injectivity.**
  The lex order on `(v i, g i)` guarantees a unique argmax and
  second-max even with value ties, and the rejection proof reduces to
  showing that pre-argmax bids are **lex-strictly** below the threshold.

Setting the identity component to `⊤ : B` (requiring `[OrderTop B]`)
forces strict value comparison: `threshold h ≤ ↑(toLex (v, b))` with
identity component `⊤` degenerates to `p < v` since `⊤ ≤ b` fails
for all `b < ⊤`. This is the `StrictComparison.auction`. It is
**fatal** for the secretary guarantee: with $v = (M, M)$ and $n = 2$,
the threshold equals $M$ and the strict test $M < M$ rejects every
remaining bidder, giving welfare $= 0$ on **all** arrival orders
([[mechanism_design.auction.online.secretary_strict_comparison_fails]]).

Setting the identity component to `⊥ : B` recovers weak comparison
$p \le v_i$ (since `⊥ ≤ b` holds for all `b`). This is the
`WeakComparison.auction`. It avoids the equal-value failure, but is
**also not constant-competitive**: on the needle profile
$v = (M, 0, \ldots, 0)$, the threshold drops to $0$ and weak comparison
accepts the **first** phase-2 arrival (since $0 \le 0$), regardless of
whether it is the needle. The needle is first in phase 2 with
probability $1/n$, so expected welfare is $(1/n) \cdot M$ — not a
constant fraction of $\max v$
([[mechanism_design.auction.online.secretary_weak_comparison_needle]]).

The secretary auction sets the identity component to the observed
lex-max identity, navigating between the two pitfalls: it rejects
haystack bidders whose identities fall below the threshold, while still
accepting the needle whose value strictly exceeds the threshold.

### Why two type parameters?

The two-type-parameter design `SingleItemAuction B F` keeps the identity
type `B` abstract and separate from the value type `F`. This enables
identity-aware pricing (needed for the secretary analysis) while keeping
the core auction theory generic. The two indexing conventions coexist:
`List (B × F)` is the natural type for the *streaming* input, while
$\mathrm{Fin}\,n \to B \times F$ is the natural type for the
*game-theoretic* layer (fixed agents, single-bidder deviations via
`Function.update`, random arrival via `Equiv.Perm (Fin n)`); the two are
bridged by `List.ofFn`.

## Position in the library

Concrete instantiations fix the pricing rule and feed the three results
of Problem 2.1:
- truthfulness ([[mechanism_design.auction.online.dsic]]),
- deterministic impossibility
  ([[mechanism_design.auction.online.no_constant_competitive]]),
- secretary guarantee
  ([[mechanism_design.auction.online.secretary_quarter_competitive]]).

## References

- [Roughgarden 2016, Lecture 2, Problem 2.1] Tim Roughgarden, *Twenty
  Lectures on Algorithmic Game Theory*, Cambridge University Press. Online
  posted-price single-item auction and its analysis.
- [AGT, Chapter 1, Section 1.3.2] Nisan, Roughgarden, Tardos, and
  Vazirani, *Algorithmic Game Theory*. Sealed-bid single-item auctions as
  the basic algorithmic game theory example.
