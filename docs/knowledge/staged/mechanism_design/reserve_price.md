---
id: mechanism_design.myerson.reserve_price
title: Myerson Reserve-Price Characterisation
kind: theorem
status: staged
primary_topic: mechanism_design
topics:
- mechanism_design
- mechanism_design.myerson
uses:
- mechanism_design.myerson.optimal_auction
verification:
  statement: accepted
  proof: gap
tags:
- mechanism-design
- myerson
- reserve-price
- second-price-auction
- symmetric-ipv
---

# Myerson Reserve-Price Characterisation

**Corollary (MSZ Cor 12.37).** In the **symmetric IPV** selling
environment — all bidders draw their types from the same regular prior
$F$, with identical value functions — the optimal auction
([[mechanism_design.myerson.optimal_auction]]) is the **second-price
auction with reserve price** $r^* = \psi^{-1}(0)$:

1. Solicit sealed bids $b = (b_1, \dots, b_n)$ from all bidders.
2. If $\max_i b_i < r^*$: no sale.
3. Otherwise: the highest bidder wins and pays
   $\max\big(r^*, \; \text{second-highest bid}\big)$.

## Two notable corollaries

- **Reserve price depends only on the prior**, *not* on the number of
  bidders. The same $r^* = \psi^{-1}(0)$ is optimal whether there are
  2 or 200 bidders, as long as the distribution is unchanged.

- **No-sale is sometimes optimal**: when all bids fall below the
  reserve, the seller intentionally keeps the object. This trades
  realised revenue against incentivising future-period high bids — a
  static one-shot reflection of monopoly pricing.

## Proof outline

Specialise the Myerson optimal auction
([[mechanism_design.myerson.optimal_auction]]) to symmetric $F_i = F$:

1. By symmetry of $\psi$, $\arg\max_i \psi_i(t_i) = \arg\max_i t_i$
   (same monotone $\psi$ across bidders, so argmax is preserved).
2. Hence the optimal allocation gives to the highest bidder, subject to
   $\psi(\text{winner}) \ge 0 \iff \text{winner's bid} \ge r^*$.
3. The Myerson payment formula computes the winner's payment as
   $\max(r^*, \text{second-highest bid})$, matching the second-price
   structure with reserve.

## Lean port (deferred — see #176)

Planned additions to
`EconCSLib/MechanismDesign/Auction/MyersonOptimalAuction.lean`:

- `optimalReservePrice` (def: $\psi^{-1}(0)$ via implicit-function /
  monotone-inverse)
- `optimalReservePrice_independent_of_n` (the n-independence
  corollary)
- `myersonOptimalAuction_symmetric_eq_secondPriceWithReserve`
  (the structural equivalence)

Depends on the underlying optimal-auction port (#175).

## References

- [MSZ Cor 12.37] Maschler, Solan, Zamir, *Game Theory*.
- Myerson, R. B. (1981). "Optimal Auction Design".
  *Math. Oper. Res.* 6, §6.
- Krishna, V. (2010). *Auction Theory*, §5.2..
