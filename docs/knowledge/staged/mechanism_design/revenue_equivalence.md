---
id: mechanism_design.myerson.revenue_equivalence
title: Revenue Equivalence Theorem
kind: theorem
status: staged
primary_topic: mechanism_design
topics:
- mechanism_design
- mechanism_design.myerson
uses:
- mechanism_design.bayesian.selling_problem
- mechanism_design.myerson.payment_formula
- mechanism_design.bayesian.ex_ante_expected_utility
verification:
  statement: accepted
  proof: gap
tags:
- mechanism-design
- myerson
- revenue-equivalence
- bayesian
---

# Revenue Equivalence Theorem

**Theorem (Myerson 1981; MSZ Thm 12.21).** Let $M$ and $M'$ be two
Bayesian Incentive Compatible (BIC) selling mechanisms over the same
IPV selling problem ([[mechanism_design.bayesian.selling_problem]]).
If

1. $M$ and $M'$ share the same **interim allocation rule** for every
   bidder $i$:
   $$
   \bar{x}_i(t_i) \;=\; \mathbb{E}_{t_{-i}}\big[x_i(t_i, t_{-i})\big]
   \;=\; \mathbb{E}_{t_{-i}}\big[x'_i(t_i, t_{-i})\big]
   \qquad \forall i, t_i;
   $$

2. they assign each bidder's lowest type the same expected payoff
   ($U_i^{M}(\underline t_i) = U_i^{M'}(\underline t_i)$),

then $M$ and $M'$ generate the **same expected revenue** for the seller.

## Proof route

Expected revenue is the negative of total expected bidder surplus
(seller's payment intake equals bidders' payment outflow). By the
Myerson payment formula ([[mechanism_design.myerson.payment_formula]]),
each BIC mechanism's expected payment from bidder $i$ at type $t_i$ is
determined entirely by:

- the interim allocation rule $\bar{x}_i$, and
- the boundary value $U_i(\underline t_i)$.

Specifically: $p_i(t_i) = t_i \cdot \bar{x}_i(t_i) - \int_{\underline t_i}^{t_i} \bar{x}_i(z)\, dz - U_i(\underline t_i)$.

Taking expectations over $t_i$ and summing over $i$ gives the seller's
expected revenue as a functional of $(\bar{x}_i, U_i(\underline t_i))_i$
alone — so any two mechanisms agreeing on these quantities have equal
expected revenue.

## Why it matters

Revenue equivalence is the structural insight that **only the allocation
rule and the lowest-type boundary affect revenue** under BIC + IPV.
This dramatically simplifies optimal-auction design: maximising revenue
reduces to maximising over interim allocation rules, leading directly to
the virtual-valuation framework
([[mechanism_design.myerson.optimal_auction]]).

## Lean port (deferred — see #174)

Planned declarations in `EconCSLib/MechanismDesign/Auction/Myerson.lean`:

- `expectedRevenue` (functional)
- `revenue_equivalence` (main theorem)
- Supporting integration lemmas for the BIC payment formula.

Dependencies on yet-to-formalise pieces: `BayesianSellingProblem`
([[mechanism_design.bayesian.selling_problem]]), the BIC interim
characterisation. The single-parameter Myerson envelope is already in
`EconCSLib/MechanismDesign/Auction/Myerson.lean` and provides the per-bidder
identity used in the proof.

## References

- [MSZ Thm 12.21] Maschler, Solan, Zamir, *Game Theory*.
- Krishna, V. (2010). *Auction Theory*, Thm 3.3..
- Myerson, R. B. (1981). "Optimal Auction Design". *Math. Oper. Res.*
  6: 58–73.
