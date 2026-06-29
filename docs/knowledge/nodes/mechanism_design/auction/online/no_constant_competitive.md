---
id: mechanism_design.auction.online.no_constant_competitive
title: No Deterministic Constant Competitive Ratio
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
    - Online.Auction.SingleItemAuction.welfare_can_be_zero
    - Online.Auction.SingleItemAuction.no_constant_competitive_ratio
verification:
  statement: accepted
  proof: accepted
  alignment: aligned
tags:
  - auction
  - online-algorithm
  - competitive-ratio
  - impossibility
  - posted-price
  - counterexample
---

# No Deterministic Constant Competitive Ratio

**Theorem (Roughgarden, Problem 2.1(b)).** For any deterministic online
single-item auction
([[mechanism_design.auction.online.single_item_auction]]) with a
positive opening threshold and any number of bidders $n \ge 1$, there
exists a valuation profile on which the auction captures **zero**
welfare while the optimum is positive.

## Statement

For every threshold rule $T$ with opening threshold value $p_0 > 0$ and
every $n \ge 1$, there exists an $n$-bidder profile $f$ such that

$$
\mathrm{welfare}_T(f) = 0 \quad\text{and}\quad \max_i v_i > 0.
$$

**Corollary.** No deterministic online auction achieves a constant
competitive ratio: for every $c > 0$ and every $n \ge 1$, some profile
gives $\mathrm{welfare}_T(f) = 0 < c \cdot \max_i v_i$.

## Proof

The adversary probes the opening threshold and exploits it.

**Case 1: the opening threshold is $\top$** (reject unconditionally).
The adversary sends one bidder with value $1$ and $n - 1$ bidders with
value $0$. Threshold $\top$ rejects everyone, so welfare is $0$ while
$\max v = 1$.

**Case 2: the opening threshold has value $p_0 > 0$.** The adversary
sends all $n$ bidders with value $p_0 / 2$, then sets all but the first
bidder's value to $0$.

- Bidder $0$ faces threshold value $p_0$ and bids $p_0/2$. Since
  $p_0/2 < p_0$, the lexicographic acceptance condition fails — bidder
  $0$ is rejected.
- Every remaining bidder has value $0$ and cannot clear any nonneg
  threshold. All are rejected.

Welfare is $0$, while $\max v = p_0/2 > 0$.

The corollary is immediate since $0 < c \cdot \max v$.

## Why the quantifiers matter

- **Per $n$, not just $n = 2$.** A threshold rule may depend on the
  number of bidders (the secretary auction
  [[mechanism_design.auction.online.secretary_quarter_competitive]]
  splits at $\lfloor n/2 \rfloor$), so refuting competitiveness on
  $2$-bidder inputs says nothing about $3$-bidder inputs. The
  impossibility holds for **every** $n$.
- **Positive opening threshold is the natural assumption.** With a
  non-positive opening threshold, a lone first bidder would win the item
  for free — an auction that gives the item away is trivially
  competitive but economically vacuous.

## Why it matters

This impossibility motivates the escape used in the positive result:
randomise over arrival orders. Under adversarial arrivals, the auctioneer
must commit to the opening threshold before seeing any bid, and the
adversary can exploit this. Under uniformly random arrival order, the
secretary-style threshold rule recovers a constant $1/4$ guarantee
([[mechanism_design.auction.online.secretary_quarter_competitive]]).

The contrast is the standard online-algorithms story: worst-case
competitive analysis is hopeless, but average-case (random-order)
analysis remains informative.

## Remarks

### Lean formalization

The main statement is `welfare_can_be_zero`. The hypothesis on the
opening threshold takes the form: for all $t$ with $T([]) = \uparrow t$,
the value component of $t$ is positive. The corollary
`no_constant_competitive_ratio` is immediate. The proof for Case 2 uses
`welfareAux_all_zero` to show that after the first bidder is rejected,
all remaining zero-value bidders are also rejected.

## References

- [Roughgarden 2016, Lecture 2, Problem 2.1(b)] Tim Roughgarden, *Twenty
  Lectures on Algorithmic Game Theory*, Cambridge University Press.
  Lower bound against deterministic online auctions.
