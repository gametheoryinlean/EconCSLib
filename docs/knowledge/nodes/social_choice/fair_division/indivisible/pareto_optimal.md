---
id: social_choice.fair_division.indivisible.pareto_optimal
title: Indivisible Pareto Optimal
kind: definition
status: formalized
primary_topic: social_choice
topics:
  - social_choice
  - social_choice.fair_division
  - social_choice.fair_division.indivisible
uses:
  - social_choice.fair_division.indivisible.allocation
  - social_choice.fair_division.indivisible.valuation
  - social_choice.fair_division.pareto_optimal
lean:
  modules:
    - EconCSLib.SocialChoice.FairDivision.Indivisible.Efficiency
  declarations:
    - SocialChoice.FairDivision.Indivisible.IsParetoOptimal
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
tags:
  - fair-division
  - indivisible
  - pareto
  - efficiency
---

# Indivisible Pareto Optimal

An indivisible allocation $A$ is *Pareto optimal* (PO) if no complete
allocation weakly improves every agent's bundle value with at least one
strict improvement.

In Lean: `SocialChoice.FairDivision.Indivisible.IsParetoOptimal` — an
`abbrev` for the generic [[social_choice.fair_division.pareto_optimal]]
specialised at `v.val` with the feasibility predicate $B \mapsto
\mathrm{IsAllocation}\ \mathrm{allGoods}\ B$.

The class hypotheses `[Fintype N]` (for `IsAllocation`'s
`Finset.univ.biUnion`) and `[DecidableEq G]` (for `Finset` operations)
are required.

## Significance

PO is the standard efficiency yardstick for indivisible allocations.
The headline existence result is that *EF1 + PO* always exists for
additive valuations, achievable by two distinct algorithms:

- **Maximum Nash welfare (MNW)** — Caragiannis et al. (EC 2016) prove
  the MNW allocation is simultaneously EF1 and PO. Not yet formalised
  in EconCSLib.
- **Envy-cycle elimination** — Lipton et al. (EC 2004) yield an EF1
  allocation; with a slight refinement on tie-breaking, also PO.

## References

- [AGT Chapter 11] Nisan, Roughgarden, Tardos, and Vazirani, *Algorithmic Game Theory*. Pareto optimality in indivisible fair division.
- Caragiannis, Kurokawa, Moulin, Procaccia, Shah, and Wang (2019). "The Unreasonable Fairness of Maximum Nash Welfare". *EC* 2016 / *ACM TEAC*.
- Lipton, Markakis, Mossel, and Saberi (2004). "On Approximately Fair Allocations of Indivisible Goods". *EC*.
