---
id: mechanism_design.auction.basic.second_price_dsic
title: Vickrey Truth-Telling Is Dominant
kind: theorem
status: proved
primary_topic: mechanism_design
topics:
  - mechanism_design
  - mechanism_design.auction
  - mechanism_design.auction.basic
uses:
  - mechanism_design.auction.basic.second_price_mechanism
  - mechanism_design.basic.dsic_predicate
  - game_theory.strategic_game.weakly_dominant_strategy
lean:
  modules:
    - EconCSLib.MechanismDesign.Auction.Vickrey
  declarations:
    - Auction.SecondPrice.valuation_is_dominant
    - Auction.SecondPrice.truthful_weakly_dominant
    - Auction.SecondPrice.mechanism_isDSIC
verification:
  statement: accepted
  proof: accepted
  alignment: aligned
tags:
  - auction
  - vickrey
  - dsic
  - weakly-dominant
---

# Vickrey Truth-Telling Is Dominant

**Theorem (Vickrey 1961).** In the second-price auction
([[mechanism_design.auction.basic.second_price_mechanism]]), truthful bidding $b_i = v_i$ is
a weakly dominant strategy for every bidder $i$.

Formally: for every valuation profile $v : I \to U$, every bidder $i \in I$,
and every opposing bid profile $b : I \to U$,
$$
u_i\bigl(v,\; b\bigr) \;\le\; u_i\bigl(v,\; b[i \mapsto v_i]\bigr).
$$

## Proof sketch

The key observation is that $\mathrm{maxBidExcluding}(b, i)$ is invariant
under replacing $b_i$ — the second-highest-bid computation ignores bidder
$i$'s own bid. Split on whether $i$ is the original winner:

- If $i$ wins under $b$: replacing $b_i$ with $v_i$ either keeps $i$ as the
  winner (if $v_i \ge $ all other bids) with the same price, or makes $i$
  lose with payoff $0$. Either way, payoff does not decrease, because under
  $b$ the payoff was $v_i - p$ for $p = \mathrm{maxBidExcluding}(b,i) \ge 0$
  in the unfavourable case.
- If $i$ loses under $b$: payoff is $0$. After truthful bidding, $i$ either
  still loses (payoff $0$) or wins at price $\mathrm{maxBidExcluding}(b,i)
  \le v_i$, giving payoff $\ge 0$.

In both cases the truthful payoff weakly dominates.

## Lean form

- `valuation_is_dominant v i b : utility v b i ≤ utility v (Function.update b i (v i)) i`
  states the inequality directly at the utility-function level.
- `truthful_weakly_dominant v i` packages the same fact as
  `IsWeaklyDominant` in the strategic game `game v`
  ([[game_theory.strategic_game.weakly_dominant_strategy]]).
- `mechanism_isDSIC` lifts the result to the
  `MechanismWithTransfers`-level DSIC predicate
  ([[mechanism_design.basic.dsic_predicate]]):
  `Auction.SecondPrice.mechanism.isDSIC Auction.SecondPrice.utility`.

## Why it matters

The Vickrey auction is the canonical example of a non-trivial DSIC
mechanism. It is the single-item specialisation of VCG
([[mechanism_design.vcg.truthfulness_and_ir]]): when there is only one
item, the Clarke pivot payment equals the second-highest bid, and the
allocation rule chooses the bidder with the highest reported value.

The contrast with first-price auctions
([[mechanism_design.auction.basic.first_price_no_dsic]]) — where truthful bidding is
*not* dominant — motivates the broader truthful-mechanism design programme.

## References

- [Vickrey 1961] William Vickrey, "Counterspeculation, Auctions, and
  Competitive Sealed Tenders", *Journal of Finance* 16(1):8–37. Original
  proof of weak dominance.
- [AGT, Chapter 9, Section 9.3.2, Prop 9.13] Nisan, Roughgarden, Tardos,
  and Vazirani, *Algorithmic Game Theory*. Truthfulness of the second-price
  auction.
- [MFoGT, Chapter 1, Section 1.2.4] Maschler, Solan, and Zamir, *Game
  Theory*. Vickrey weak-dominance discussion.
- [Krishna, Chapter 2, Section 2.2] Vijay Krishna, *Auction Theory*, 2nd
  ed.. Second-price auction equilibrium
  analysis.
