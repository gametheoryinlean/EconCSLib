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

An **online single-item auction** sells one indivisible good to $n$
bidders who arrive sequentially. Each bidder $i$ has a private value
$v_i \ge 0$ and a distinct identity $b_i$. While the item is unsold,
the auctioneer posts a take-it-or-leave-it threshold that depends
**only on bids already rejected**; the current bidder either clears the
threshold (and the auction ends) or departs forever.

This is the running example of Roughgarden's *Twenty Lectures*,
Problem 2.1.

## Model

A **single-item auction** is specified by a threshold rule

$$
T : \underbrace{(b_1, v_1), \ldots, (b_{k-1}, v_{k-1})}_{\text{rejected history}} \;\longmapsto\; (p,\, \bar{b}) \in (F \times B)_\top
$$

that reads the history of rejected (identity, value) pairs and returns
either $\top$ (reject unconditionally) or a **lexicographic threshold**
$(p, \bar{b})$.

Bidder $i$ with value $v_i$ and identity $b_i$ **clears** the threshold
$(p, \bar{b})$ when

$$
p < v_i \quad\lor\quad (p = v_i \;\land\; \bar{b} \le b_i).
$$

The first bidder to clear the threshold wins the item; the auction pays
welfare equal to the winner's value. If every bidder is rejected, welfare
is zero.

**Social welfare** of a profile $f = ((b_0, v_0), \ldots, (b_{n-1},
v_{n-1}))$ presented in arrival order is the value $v_j$ of the first
bidder $j$ to clear the running threshold, or $0$ if no bidder clears.

**Utility** of bidder $i$ is quasi-linear: $v_i - p$ if $i$ wins at
threshold value $p$, and $0$ otherwise.

## Why tie-breaking is essential

A simpler design would threshold on values alone, accepting when
$p < v_i$ or when $p \le v_i$. Both fail.

### Strict comparison fails on equal values

If the acceptance rule is $p < v_i$ (no tie-breaking), consider $n = 2$
bidders with $v_0 = v_1 = M$. The sample-then-threshold rule
sets $p = M$ after observing the first bidder. The second bidder faces
$M < M$, which is false. Both arrival orders give welfare $= 0$, while
$\max v = M$. The mechanism is not competitive at all
([[mechanism_design.auction.online.secretary_strict_comparison_fails]]).

### Weak comparison fails on the needle profile

If the acceptance rule is $p \le v_i$ (accept all ties), consider the
*needle profile*: $v_0 = M$, $v_1 = \cdots = v_{n-1} = 0$. All
observed bidders have value $0$, so the threshold drops to $p = 0$.
The test $0 \le 0$ passes for the first phase-2 arrival, regardless of
whether it is the needle. The needle is first in phase 2 with
probability $1/n$, giving expected welfare $(1/n) \cdot M$ — not a
constant fraction of $\max v$
([[mechanism_design.auction.online.secretary_weak_comparison_needle]]).

### Lexicographic tie-breaking resolves both

The key insight is to attach an **identity** component $\bar{b}$ to the
threshold. At a value tie ($p = v_i$), the auction compares identities:
accept if $\bar{b} \le b_i$, reject otherwise.

This navigates between the two failure modes:

- **Equal-value profiles.** At the tie $p = v_i = M$, the identity
  comparison $\bar{b} \le b_i$ distinguishes the observed bidder from a
  later arrival. A bidder with a higher identity than the threshold
  clears; one with a lower identity does not. The strict-comparison
  deadlock ($M < M$ always false) is broken.

- **Needle profile.** When $p = 0$ and a haystack bidder with value $0$
  arrives, the value test $0 < 0$ fails, so acceptance falls to the
  identity test $\bar{b} \le b_i$. The sample-then-threshold rule sets $\bar{b}$ to
  the maximum identity seen in phase 1. Haystack bidders from phase 2
  have identities below this maximum (by identity injectivity), so they
  are rejected. The needle, whose value $M > 0$ strictly exceeds the
  threshold, is accepted unconditionally.

The combined acceptance condition is the **lexicographic order** on
$(v, b)$: this is the mathematical content of the threshold design. The
sample-then-threshold auction with this rule is $1/4$-competitive
([[mechanism_design.auction.online.secretary_quarter_competitive]]).

## The three parts of Problem 2.1

Concrete threshold rules yield the three results:

1. **Truthfulness (Problem 2.1(a)).** Every single-item auction of this
   form is DSIC: truthful bidding $v_i$ weakly dominates any
   misreport, regardless of the threshold rule
   ([[mechanism_design.auction.online.dsic]]).

2. **Deterministic impossibility (Problem 2.1(b)).** Under adversarial
   arrival order, no deterministic threshold rule achieves a constant
   competitive ratio
   ([[mechanism_design.auction.online.no_constant_competitive]]).

3. **Random-order guarantee (Problem 2.1(c)).** Under uniformly random
   arrival, the sample-then-threshold rule is $1/4$-competitive
   ([[mechanism_design.auction.online.secretary_quarter_competitive]]).

## Remarks

### Lean formalization

The auction is formalised as `SingleItemAuction B F` with a single field
`threshold : List (B × F) → WithTop (Lex (F × B))`. The type
`Lex (F × B)` is Lean's lexicographic product; `WithTop` adjoins $\top$.
The acceptance test is a single comparison
`threshold h ≤ ↑(toLex (v_i, b_i))`, which by `Prod.Lex.le_iff`
unfolds to $p < v_i \lor (p = v_i \land \bar{b} \le b_i)$.

The auction is embedded into a generic online-algorithm framework
(`OnlineAlgorithm`) via `SingleItemAuction.online`. The state is either
$\mathsf{unsold}(\text{history})$ or $\mathsf{sold}(\text{winner},
\text{price})$. Welfare is computed by `welfareAux`, a direct recursion
carrying the rejection history, chosen so that small concrete profiles
reduce cleanly under `simp`. Utility factors through `stateBeforeStep`
to isolate each bidder's local view.

### Identity injectivity, not value injectivity

The competitive-ratio theorem requires `Function.Injective g` (distinct
identities), **not** `Function.Injective v` (distinct values). This is
the mathematically natural hypothesis: the competitive-ratio guarantee
is about the mechanism design, not an accidental distinctness condition
on valuations. The lexicographic order on $(v_i, b_i)$ has a unique
argmax and second-max even when values collide, as long as identities
are distinct.

### The two type parameters

`SingleItemAuction B F` keeps the identity type $B$ and the value type
$F$ abstract and separate. The streaming input is typed as
$\mathrm{List}(B \times F)$; the game-theoretic layer uses
$\mathrm{Fin}\,n \to B \times F$ with single-bidder deviations via
`Function.update` and random arrival via `Equiv.Perm (Fin n)`. The two
views are bridged by `List.ofFn`.

## References

- [Roughgarden 2016, Lecture 2, Problem 2.1] Tim Roughgarden, *Twenty
  Lectures on Algorithmic Game Theory*, Cambridge University Press. Online
  posted-price single-item auction and its analysis.
- [AGT, Chapter 1, Section 1.3.2] Nisan, Roughgarden, Tardos, and
  Vazirani, *Algorithmic Game Theory*. Sealed-bid single-item auctions as
  the basic algorithmic game theory example.
