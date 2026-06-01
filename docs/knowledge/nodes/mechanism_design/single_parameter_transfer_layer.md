---
id: mechanism_design.transfer.single_parameter_transfer_layer
title: Single-Parameter Transfer Layer
kind: definition
status: formalized
primary_topic: mechanism_design
topics:
- mechanism_design
- mechanism_design.transfer
uses:
- mechanism_design.transfer.mechanisms_with_transfers
lean:
  modules:
  - EconCSLib.MechanismDesign.Auction.Transfer
  declarations:
  - SingleParameterMechanism
  - SingleParameterMechanism.IsAllocFeasible
  - SingleParameterMechanism.IsMonotone
  - SingleParameterMechanism.payment
  - SingleParameterMechanism.quasiLinearValue
  - SingleParameterMechanism.quasiLinearUtility
  - SingleParameterMechanism.quasiLinearUtility_eq_transferQuasiLinearUtility
  - SingleParameterMechanism.IsDSIC
  - SingleParameterMechanism.IsImplementable
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
tags:
- mechanism-design
- single-parameter
- transfers
---

# Single-Parameter Transfer Layer

Single-parameter mechanisms use scalar reports, scalar allocation coordinates,
and scalar payments. This is the common interface for Myerson-style payment
rules and knapsack auctions.

The layer records allocation feasibility, monotonicity, quasi-linear value and
utility, DSIC, and implementability predicates.

## References

- [AGT, Chapter 9, Section 9.5.4, Defs. 9.33-9.35 and Thm. 9.36]
  Nisan, Roughgarden, Tardos, and Vazirani, *Algorithmic Game Theory*. Single-parameter allocation rules,
  monotonicity, critical values, and implementability.
- [AGT, Chapter 12, Section 12.2] Nisan, Roughgarden, Tardos, and Vazirani,
  *Algorithmic Game Theory*.
  Single-dimensional domains for truthful approximation mechanisms.

## Provenance

- Migrated from EconCSLib pull request 27, old blueprint label
  `def:md_single_parameter_interface` in `blueprint/src/content.tex`.
