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

**Theorem (`welfare_can_be_zero`, Roughgarden Problem 2.1(b)).** Any
deterministic online single-item auction
([[mechanism_design.auction.online.single_item_auction]]) with a positive
opening price can be forced to capture **zero** welfare while the optimum
is positive.

For every $A$ with $0 < A.\mathrm{price}\,[\,]$ and every $n \ge 1$,
there exists an $n$-bidder profile $f$ with $\mathrm{maxV}\,f > 0$ and

$$
A.\mathrm{welfare}(f) \;=\; 0 .
$$

**Corollary (`no_constant_competitive_ratio`).** Hence $A$ has no
constant competitive ratio: for every $c > 0$ and every $n \ge 1$ some
profile gives $A.\mathrm{welfare}(f) = 0 < c \cdot \mathrm{maxV}\,f$.

## Proof

Fix $A$ with $p_0 = A.\mathrm{price}\,[\,] > 0$. Two cases:

- **$p_0 = \top$.** The adversary sends bidder $0$ with value $1$ and
  every later bidder with value $0$. Price $\top$ rejects everything, so
  welfare is $0$ while $\mathrm{maxV} \ge 1 > 0$.
- **$p_0 = \uparrow p$ with $p > 0$.** Bidder $0$ values the item at
  $p/2$ and every later bidder values it at $0$. Bidder $0$ faces price
  $p$ and bids $p/2 < p$, so the lex acceptance condition
  $p < p/2 \lor (p = p/2 \land \ldots)$ fails — they are rejected. Every
  remaining bidder has value $0$, so welfare is $0$ by the structural
  lemma `welfareAux_all_zero`.

The corollary is immediate since $0 < c \cdot \mathrm{maxV}$.

## Why the quantifiers are exactly these

- **Per $n$, not just $n = 2$.** A posted-price auction may depend on the
  number of bidders (the secretary auction
  [[mechanism_design.auction.online.secretary_quarter_competitive]] splits
  at $\lfloor n/2 \rfloor$), so refuting competitiveness on $2$-bidder
  inputs says nothing about $3$-bidder inputs. The impossibility must —
  and does — hold for **every** $n$.
- **Positive opening price, and $n \ge 1$ is then tight.** With
  $A.\mathrm{price}\,[\,] \le 0$ a lone first bidder wins the item for
  free, so a single-bidder auction would capture full welfare. Requiring a
  positive opening price — the natural assumption for an auction — removes
  exactly that obstruction.

## Why it matters

This is the impossibility half of Problem 2.1, and it motivates the
escape used in the positive result:

- **Randomise the input** (rather than the mechanism): under uniformly
  random arrival order the secretary-style threshold rule recovers a
  constant guarantee, the $1/4$ bound of
  [[mechanism_design.auction.online.secretary_quarter_competitive]].
- The contrast is the standard online-algorithms story: worst-case
  competitive analysis is hopeless because the algorithm must commit to
  the opening price before seeing any bid, while average-case
  (random-order) analysis remains informative.

## References

- [Roughgarden 2016, Lecture 2, Problem 2.1(b)] Tim Roughgarden, *Twenty
  Lectures on Algorithmic Game Theory*, Cambridge University Press.
  Lower bound against deterministic online auctions.
