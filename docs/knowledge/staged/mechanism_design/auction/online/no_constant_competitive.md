---
id: mechanism_design.auction.online.no_constant_competitive
title: No Deterministic Constant Competitive Ratio
kind: theorem
status: staged
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
---

# No Deterministic Constant Competitive Ratio

The sharp content of Problem 2.1(b) is that a deterministic online auction
can be forced to capture **zero** welfare while the optimum is positive.

**Theorem (`welfare_can_be_zero`).** Let $A$ be any deterministic online
single-item auction that posts a positive opening price,
$0 < A.\mathrm{price}\,[\,]$. Then for every $n \ge 1$ there is an
$n$-bidder valuation profile $v$ with $\mathrm{maxV}\,v > 0$ and

$$
A.\mathrm{welfare}(v,\, v) \;=\; 0 .
$$

**Corollary (`no_constant_competitive_ratio`).** Hence $A$ has no constant
competitive ratio: for every $c > 0$ and every $n \ge 1$ some profile gives
$A.\mathrm{welfare}(v,\,v) = 0 < c \cdot \mathrm{maxV}\,v$.

## Why the quantifiers are exactly these

- **Per `n`, not just $n = 2$.** A posted-price auction may depend on the
  number of bidders (the secretary auction
  [[mechanism_design.auction.online.secretary_quarter_competitive]] splits at
  $\lfloor n/2 \rfloor$), so refuting competitiveness on a $2$-bidder input
  says nothing about $3$-bidder inputs. The impossibility must — and does —
  hold for **every** $n$. The same one-line adversary works at all $n$.
- **Positive opening price, and $n \ge 1$ is then tight.** With
  $A.\mathrm{price}\,[\,] \le 0$ a lone first bidder wins the item for free,
  so a single-bidder auction would capture full welfare; the impossibility
  genuinely fails at $n = 1$ for such giveaways. Requiring a positive
  opening price — the natural assumption for an auction — removes exactly
  that obstruction, and then a single bidder already suffices.

## Proof

Fix $A$ with $p_0 = A.\mathrm{price}\,[\,] > 0$. The adversary is one
construction, independent of $n$: bidder $0$ values the item at $p_0 / 2$
and every later bidder values it at $0$.

- $\mathrm{maxV}\,v \ge v_0 = p_0/2 > 0$.
- Bidder $0$ faces the posted price $p_0$ and bids $p_0/2 < p_0$, so they are
  rejected (the winning rule is $p_0 \le \mathrm{bid}$). Every remaining
  bidder values the item at $0$, so whoever — if anyone — wins later
  contributes welfare $0$. Hence $A.\mathrm{welfare}(v,v) = 0$.

The valuation-zero tail is handled by the structural lemma
`welfareFrom_eq_zero`: once the only positive bidder is rejected, the
recursion runs over a list of zero valuations and can only output $0$. The
corollary is immediate, since $\mathrm{welfare} = 0 < c \cdot \mathrm{maxV}$.

## Why it matters

This is the impossibility half of Problem 2.1, and it motivates the escape
used in the positive result:

- **Randomise the input** (rather than the mechanism): under uniformly
  random arrival order the secretary-style threshold rule recovers a
  constant guarantee, the $1/4$ bound of
  [[mechanism_design.auction.online.secretary_quarter_competitive]].
- The contrast is the standard online-algorithms story: worst-case
  competitive analysis is hopeless precisely because the algorithm must
  commit to the opening price before seeing any bid, while average-case
  (random-order) analysis remains informative.

## References

- [Roughgarden 2016, Lecture 2, Problem 2.1(b)] Tim Roughgarden, *Twenty
  Lectures on Algorithmic Game Theory*, Cambridge University Press.
  Lower bound against deterministic online auctions.
