---
id: mechanism_design.auction.basic.first_price_no_dsic
title: First-Price Fails DSIC
kind: theorem
status: proved
primary_topic: mechanism_design
topics:
  - mechanism_design
  - mechanism_design.auction
  - mechanism_design.auction.basic
uses:
  - mechanism_design.auction.basic.first_price_mechanism
  - mechanism_design.basic.dsic_predicate
  - game_theory.strategic_game.weakly_dominant_strategy
lean:
  modules:
    - EconCSLib.MechanismDesign.Auction.FirstPrice
  declarations:
    - Auction.FirstPrice.no_dominant_strategy
    - Auction.FirstPrice.mechanism_not_isDSIC
verification:
  statement: accepted
  proof: accepted
  alignment: aligned
tags:
  - auction
  - first-price
  - dsic
  - counterexample
---

# First-Price Fails DSIC

**Theorem.** The first-price auction
([[mechanism_design.auction.basic.first_price_mechanism]]) is *not* dominant-strategy
incentive compatible: for every bidder $i$ and every bid $b_i$, there
exists an opposing bid profile that makes $b_i$ strictly worse than some
other bid for $i$.

Formally: assuming the bid space `U` contains a positive element
($\exists a : U.\; 0 < a$), no constant bid is weakly dominant in the
strategic-game `game v` for any valuation profile $v$.

## Proof sketch

Given a candidate bid $b_i$ for bidder $i$, choose a positive $a > 0$ and
construct opponents' bids at the level $b_i - 2a$. Then:

- Bidding $b_i$, bidder $i$ wins and pays $b_i$, yielding payoff
  $v_i - b_i$.
- Bidding $b_i - a$, bidder $i$ still wins (since $b_i - a > b_i - 2a$)
  but pays $b_i - a$, yielding payoff $v_i - (b_i - a) = v_i - b_i + a$.

The deviation $b_i \mapsto b_i - a$ raises payoff by exactly $a > 0$, so
$b_i$ cannot be weakly dominant.

## Lean form

- `no_dominant_strategy v i bi ha : ¬ IsWeaklyDominant (game v) i bi`
  states that no bid $b_i \in U$ is a weakly dominant strategy for $i$ in
  the first-price game, under the bid-space-has-positives hypothesis `ha`.
- `mechanism_not_isDSIC` lifts this to the mechanism-level negation
  `¬ Auction.FirstPrice.mechanism.isDSIC Auction.FirstPrice.utility`.

## Why it matters

The first-price auction is the canonical example of a *non-truthful*
single-item mechanism. Equilibrium analysis in first-price requires moving
to the Bayesian setting and computing a symmetric strictly-increasing
Bayes–Nash equilibrium of the form $b^*(t) = E[Y_1 \mid Y_1 < t]$, where
$Y_1$ is the maximum opponent valuation
([[mechanism_design.auction.bayesian.symmetric_first_price_equilibrium]]). This contrasts
sharply with the second-price auction
([[mechanism_design.auction.basic.second_price_dsic]]), where truthful bidding is dominant
without any distributional assumption.

The first-price/second-price contrast is the simplest concrete instance of
the dominant-strategy vs. Bayes–Nash gap that motivates much of
mechanism-design theory.

## References

- [AGT, Chapter 9, Section 9.3.1] Nisan, Roughgarden, Tardos, and
  Vazirani, *Algorithmic Game Theory*.
  Non-truthfulness of first-price as motivation for VCG.
- [Krishna, Chapter 2, Section 2.3] Vijay Krishna, *Auction Theory*, 2nd
  ed.. Strategic analysis of first-price
  auctions.
- [MFoGT, Chapter 12] Maschler, Solan, and Zamir, *Game Theory*. First-price auction discussion in the
  private-values chapter.
