---
id: mechanism_design.auction.bayesian.symmetric_first_price_equilibrium
title: Symmetric IPV First-Price Equilibrium
kind: theorem
status: staged
primary_topic: mechanism_design
topics:
  - mechanism_design
  - mechanism_design.auction
  - mechanism_design.auction.bayesian
uses:
  - mechanism_design.auction.basic.first_price_mechanism
  - mechanism_design.auction.bayesian.single_item_framework
  - mechanism_design.auction.bayesian.interim_and_ic
verification:
  statement: accepted
  proof: gap
tags:
  - auction
  - first-price
  - bayes-nash
  - symmetric-equilibrium
  - ipv
---

# Symmetric IPV First-Price Equilibrium

**Theorem (MSZ Thm 12.9–12.11; Krishna Thm 2.2).** In the symmetric
independent-private-values first-price auction with $n$ bidders,
common type distribution $F$ on $[0, \omega]$ with continuous density
$f > 0$, the unique symmetric strictly-increasing Bayes–Nash
equilibrium ([[mechanism_design.auction.bayesian.interim_and_ic]]) is
$$
\beta(t) \;=\; \mathbb{E}\bigl[\, Y_1 \mid Y_1 \le t \,\bigr]
\;=\; t \;-\; \frac{\int_0^t F(z)^{n-1}\, dz}{F(t)^{n-1}},
$$
where $Y_1 = \max_{j \ne i} t_j$ is the highest opponent valuation.

## Setup

- $n$ bidders, each with type $t_i$ drawn i.i.d. from CDF $F$ on
  $[0, \omega]$.
- First-price sealed-bid auction
  ([[mechanism_design.auction.basic.first_price_mechanism]]): highest bidder wins and
  pays own bid.
- Pure strategies: bid functions $\beta_i : [0, \omega] \to \mathbb{R}_{\ge 0}$.
- *Symmetric* equilibrium: a single bid function $\beta$ used by every
  bidder.

## Equilibrium derivation

The standard derivation has two ingredients:

1. **First-order condition.** Assuming all opponents use $\beta$
   strictly increasing, a bidder with type $t$ choosing bid $b$ wins
   iff $b > \beta(t_j)$ for all $j \ne i$, i.e. iff
   $\max_{j \ne i} t_j < \beta^{-1}(b)$. The probability of winning is
   $F(\beta^{-1}(b))^{n-1}$, and the expected payoff is
   $(t - b) F(\beta^{-1}(b))^{n-1}$. Differentiating with respect to $b$
   and setting $b = \beta(t)$ yields the FOC.
2. **Solving the ODE.** The FOC reduces to the linear ODE
   $$
   F(t)^{n-1} \beta'(t) + (n-1) F(t)^{n-2} f(t) \beta(t)
   \;=\; (n-1) t\, F(t)^{n-2} f(t),
   $$
   whose solution with boundary $\beta(0) = 0$ is the conditional
   expectation formula above.

The conditional-expectation form $\beta(t) = \mathbb{E}[Y_1 \mid Y_1 \le t]$
makes manifest the *shading* phenomenon: each bidder bids strictly below
their valuation, with the shade equal to the expected gap between
their type and the highest competitor type *conditional on winning*.

## Properties

- **Strict monotonicity.** $\beta$ is strictly increasing on
  $(0, \omega]$ (every type bids strictly more than every lower type).
- **Boundary**. $\beta(0) = 0$.
- **Limit behaviour**. As $n \to \infty$, $\beta(t) \to t$ — first-price
  bidding approaches truthful as competition increases.
- **Comparison to second-price**. At every type $t > 0$ in the symmetric
  IPV setting, $\beta(t) < t$ — first-price bidders shade strictly
  below the type, whereas second-price bidders bid truthfully.

## Why it matters

The symmetric IPV first-price equilibrium is the canonical positive
result in Bayesian auction theory and the *concrete instance* of:

- The interim machinery from
  [[mechanism_design.auction.bayesian.interim_and_ic]]: $\beta$ induces interim
  allocation probability $q(t) = F(t)^{n-1}$ and interim expected
  payment $m(t) = \beta(t) q(t)$.
- The Myerson payment formula
  ([[mechanism_design.myerson.payment_formula]]): the implied expected
  payment matches the single-parameter envelope identity.
- Revenue equivalence
  ([[mechanism_design.myerson.revenue_equivalence]]): expected revenue
  equals expected second-highest type $\mathbb{E}[Y_1]$, identical to
  the second-price auction's expected revenue.

## Lean port (deferred)

Planned Lean module:
`EconCSLib/Auction/SymmetricFirstPriceEquilibrium.lean`.

Planned declarations:

- `symmetricFirstPriceBid` (the function $\beta$).
- `symmetricFirstPriceBid_monotone`,
  `symmetricFirstPriceBid_lt_id`,
  `symmetricFirstPriceBid_bne` (the BNE certification).

Dependencies on yet-to-formalise pieces: the ODE solution machinery
or a direct integral-comparison proof, plus a symmetric-IPV
instantiation of [[mechanism_design.auction.bayesian.single_item_framework]]. Tracked in
the MSZ Ch.12 auction gap review.

## References

- [MSZ Chapter 12, Thm 12.9–12.11] Maschler, Solan, and Zamir, *Game
  Theory*. Symmetric IPV first-price BNE.
- [Krishna, Chapter 2, Theorem 2.2 and Proposition 2.3] Vijay Krishna,
  *Auction Theory*, 2nd ed..
  Equilibrium bid formula and shading.
- [Vickrey 1961] William Vickrey, "Counterspeculation, Auctions, and
  Competitive Sealed Tenders". Original equilibrium analysis for the
  uniform-distribution case.
- [Riley-Samuelson 1981] John Riley and William Samuelson, "Optimal
  Auctions", *AER* 71(3):381–392. General symmetric-IPV equilibrium
  derivation.
