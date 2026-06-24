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

**Theorem (Roughgarden, Problem 2.1(b)).** No deterministic online
single-item auction guarantees a constant fraction of the highest
valuation against adversarial inputs. For every constant $c > 0$ and every
pricing rule $A$ there is a valuation profile $v$ (two bidders already
suffice) with $\max(v_0, v_1) > 0$ and

$$
A.\mathrm{welfare}(v,\, v) \;<\; c \cdot \max(v_0,\, v_1).
$$

## Proof

Fix the pricing rule $A$ and the constant $c$. Only the first posted price
$p_0 = A.\mathrm{price}\,[\,]$ matters, and the adversary plays against it
with two bidders:

- **If $p_0 > 0$:** present a first bidder with a tiny valuation
  $v_0 \in (0, p_0)$, below the price, who is rejected; then a second bidder
  whose valuation is also small. The high value the mechanism *could* have
  captured never materialises, so realised welfare is a vanishing fraction
  of the maximum.
- **If $p_0 \le 0$:** the first bidder (with any positive valuation) clears
  the price immediately, so the item is sold to an arbitrarily low bidder
  while a much higher second valuation is locked out.

In both branches the adversary drives the welfare ratio below the target
$c$, because the deterministic price $p_0$ is committed *before any bid is
seen* and the adversary tailors the two valuations to that single number.

## Why it matters

This is the impossibility half of Problem 2.1, and it motivates the two
escapes used elsewhere in the example file:

- **Randomise the input** (rather than the mechanism): under uniformly
  random arrival order the secretary-style threshold rule recovers a
  constant guarantee, the $1/4$ bound of
  [[mechanism_design.auction.online.secretary_quarter_competitive]].
- The contrast is the standard online-algorithms story: worst-case
  competitive analysis can be hopeless precisely when the algorithm must
  commit before seeing the data, while average-case (random-order) analysis
  remains informative.

## References

- [Roughgarden 2016, Lecture 2, Problem 2.1(b)] Tim Roughgarden, *Twenty
  Lectures on Algorithmic Game Theory*, Cambridge University Press.
  Lower bound against deterministic online auctions.
