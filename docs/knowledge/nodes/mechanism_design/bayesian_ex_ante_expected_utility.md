---
id: mechanism_design.bayesian.ex_ante_expected_utility
title: Ex-Ante Expected Utility (Bayesian Mechanisms)
kind: definition
status: formalized
primary_topic: mechanism_design
topics:
- mechanism_design
- mechanism_design.bayesian
uses:
- mechanism_design.bayesian.bayesian_mechanisms
- mechanism_design.transfer.mechanisms_with_transfers
lean:
  modules:
  - EconCSLib.MechanismDesign.Auction.MechBayesian
  declarations:
  - BayesianMechanismWithTransfers.exAnteExpectedUtility
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
tags:
- mechanism-design
- bayesian
- expected-utility
- ex-ante
---

# Ex-Ante Expected Utility (Bayesian Mechanisms)

For a Bayesian mechanism with transfers
$M : \mathrm{BayesianMechanismWithTransfers}\ I\ T\ M\ A$, a strategy
profile $\sigma : \forall i, (T_i \to M_i)$, and a prior measure $p$ on
the type space $T = \prod_i T_i$, the **ex-ante expected utility** of
agent $i$ is the integral
$$
U_i^{\mathrm{ea}}(\sigma) \;=\; \int_T u_i^{\mathrm{ql}}(t, \sigma(t)) \; dp(t),
$$
where $u_i^{\mathrm{ql}}$ is the quasi-linear stage utility at type
profile $t$ under the message profile $\sigma(t)$.

In Lean: `BayesianMechanismWithTransfers.exAnteExpectedUtility`.

## Two related notions kept separate

- *This node* — the ex-ante utility itself (an integral / random
  variable's expectation).
- *Integrability hypothesis*
  ([[mechanism_design.ex_ante_equilibrium_predicates]]'s
  `IntegrableExAnteUtility`) — a hypothesis on the strategy / prior that
  makes the integral well-defined.
- *Equilibrium predicate*
  ([[mechanism_design.ex_ante_equilibrium_predicates]]'s
  `IsExAnteBayesianNashEquilibrium`) — the no-profitable-deviation
  condition stated in terms of this utility.

Separating the *utility definition* from the *integrability hypothesis*
and the *equilibrium predicate* keeps each concern in one place — the
utility itself is just an integral, the integrability is a measurability
side condition, and the equilibrium is the strategic best-response
condition built on top.

## Bridge to interim utility

The interim expected utility (conditioned on agent $i$'s own type
$t_i$) is recovered by partial integration over $t_{-i}$. The Bayesian
revelation principle
([[mechanism_design.ex_ante_revelation_principle]]) works at the
ex-ante level for the existence statement and at the interim level for
the truthful-strategy characterisation.

## References

- [MSZ Chapter 12, §12.4] Maschler, Solan, Zamir, *Game Theory*.
  Bayesian mechanism utility levels.
- [Krishna 2010 §3.1] Krishna, V. *Auction Theory*, 2nd ed.
  Ex-ante vs. interim vs. ex-post utility distinctions.
