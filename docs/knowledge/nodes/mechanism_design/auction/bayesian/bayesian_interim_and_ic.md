---
id: mechanism_design.auction.bayesian.interim_and_ic
title: Bayesian Single-Item Auction Interim Quantities And IC
kind: definition
status: formalized
primary_topic: mechanism_design
topics:
  - mechanism_design
  - mechanism_design.auction
  - mechanism_design.auction.bayesian
uses:
  - mechanism_design.auction.bayesian.single_item_framework
  - mechanism_design.bayesian.ex_ante_expected_utility
lean:
  modules:
    - EconCSLib.MechanismDesign.Auction.BayesianSingleItem
  declarations:
    - BayesianSingleItemAuction.reportProfile
    - BayesianSingleItemAuction.interimAllocProb
    - BayesianSingleItemAuction.interimExpectedPayment
    - BayesianSingleItemAuction.interimQuasiLinearUtility
    - BayesianSingleItemAuction.equilibriumPayoff
    - BayesianSingleItemAuction.IsIncentiveCompatible
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
tags:
  - auction
  - bayesian
  - interim
  - incentive-compatibility
  - bnic
---

# Bayesian Single-Item Auction Interim Quantities And IC

This node assembles the *interim* quantities — winning probability,
expected payment, quasi-linear utility, equilibrium payoff — and the
Bayesian incentive-compatibility predicate for a Bayesian single-item
auction ([[mechanism_design.auction.bayesian.single_item_framework]]).

Throughout, fix a `BayesianSingleItemAuction I` denoted $A$ and an agent
$i \in I$. All expectations are taken against the auction's explicit
opponent-type prior $\mu_i$, which is independent of any density-level
independence assumption.

## Report profiles

`reportProfile i z_i t` glues agent $i$'s report $z_i$ with an opponent
type profile $t : \mathrm{OpponentTypeProfile}\,I\,i$ into a full report
profile in $\prod_{j} \mathbb{R}$, via `reportProfile` and the lower-level
`profileInsert` helper. It is the
input to the auction's allocation and payment rules when agent $i$ is
deviating to report $z_i$ while every opponent reports truthfully.

## Interim winning probability and expected payment

Let $x_i(t) = A.\mathrm{allocationRule}(t, i)$ and
$p_i(t) = A.\mathrm{paymentRule}(t, i)$.

- **Interim allocation probability** (`interimAllocProb i z_i`):
  $$q_i(z_i) \;=\; \mathbb{E}_{t_{-i} \sim \mu_i}\bigl[x_i(\mathrm{reportProfile}(i, z_i, t_{-i}))\bigr].$$
- **Interim expected payment** (`interimExpectedPayment i z_i`):
  $$m_i(z_i) \;=\; \mathbb{E}_{t_{-i} \sim \mu_i}\bigl[p_i(\mathrm{reportProfile}(i, z_i, t_{-i}))\bigr].$$

Both are scalar functions $\mathbb{R} \to \mathbb{R}$ of the report
$z_i$, with the opponents' uncertainty integrated out.

## Interim quasi-linear utility and equilibrium payoff

- **Interim quasi-linear utility** (`interimQuasiLinearUtility i t_i z_i`):
  $$u_i(t_i, z_i) \;=\; q_i(z_i)\, t_i \;-\; m_i(z_i),$$
  the expected payoff to a type-$t_i$ agent who reports $z_i$ while
  opponents report truthfully.
- **Equilibrium payoff** (`equilibriumPayoff i t_i`):
  $$U_i(t_i) \;=\; u_i(t_i, t_i) \;=\; q_i(t_i)\, t_i - m_i(t_i),$$
  the truthful payoff.

These are the standard objects that appear in the Myerson envelope
identity and in the revenue-equivalence theorem.

## Incentive compatibility

`IsIncentiveCompatible A` asserts that for every agent $i$ and every
true type $t_i$ and reported type $z_i$,
$$u_i(t_i, z_i) \;\le\; U_i(t_i),$$
i.e. truthful reporting is interim-utility-maximising for every type.
This is the standard Bayesian-incentive-compatibility (BIC) predicate
specialised to the single-item setting.

## Why these definitions

By integrating against an *explicit* opponent prior $\mu_i$, the
definitions stay valid in the absence of full joint independence at the
measure-theoretic level. Density-based formulas (e.g.
$q_i(z_i) = \int x_i(z_i, t_{-i})\, f_{-i}(t_{-i})\, dt_{-i}$) can be
derived as theorems on top, under independence assumptions encoded in
$\mu_i$ and `jointDensity`.

## Position in the library

These interim quantities are the auction-side specialisation of the
generic Bayesian ex-ante / interim machinery in
([[mechanism_design.bayesian.ex_ante_expected_utility]]). They
feed into:

- The Myerson payment identity at the interim level
  ([[mechanism_design.myerson.payment_formula]]).
- The revenue-equivalence theorem
  ([[mechanism_design.myerson.revenue_equivalence]]).
- Myerson's optimal auction
  ([[mechanism_design.myerson.optimal_auction]]).

## References

- [MFoGT, Chapter 12, Section 12.2] Maschler, Solan, and Zamir, *Game
  Theory*. Interim quantities and BIC in
  Bayesian auctions.
- [Krishna, Chapter 5] Vijay Krishna, *Auction Theory*, 2nd ed.. Mechanism design with interim
  allocation and payment functions.
- [AGT, Chapter 9, Section 9.5.4] Nisan, Roughgarden, Tardos, and
  Vazirani, *Algorithmic Game Theory*. Interim allocation rule and
  BIC for single-parameter mechanisms.
- [Myerson 1981, Section 2] Roger Myerson, "Optimal Auction Design",
  *Math. Oper. Res.* 6(1):58–73. Canonical interim characterisation.
