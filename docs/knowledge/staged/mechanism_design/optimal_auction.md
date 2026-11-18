---
id: mechanism_design.myerson.optimal_auction_legacy_plan
title: Myerson Optimal Auction Legacy Plan
kind: proof-plan
status: staged
primary_topic: mechanism_design
topics:
  - mechanism_design
  - mechanism_design.myerson
target: mechanism_design.myerson.optimal_auction
plan_status: formalized
verification:
  statement: accepted
  proof: not_applicable
tags:
  - mechanism-design
  - myerson
  - optimal-auction
  - provenance
---

# Myerson Optimal Auction Legacy Plan

This staged file previously carried the deferred plan for the regular Myerson
optimal-auction theorem. The regular single-item version is now represented by
the proved node [[mechanism_design.myerson.optimal_auction]], backed by the
Lean module `EconCSLib.MechanismDesign.Auction.OptimalSingleItem`.

## Current status

The regular case is no longer a blueprint gap, and the reserve second-price
endpoint is tracked by [[mechanism_design.myerson.reserve_price]]. The Lean
entry points now expose modular environment, candidate, reserve-candidate, and
interim-measurability assumption packages rather than one opaque analytic
bundle. Remaining future work belongs to more specific follow-up nodes,
especially primitive analytic discharge, concrete IID distribution examples,
nonzero seller-reservation-value extensions, boundary tie-sharing variants,
and the non-regular ironing theorem.

## References

- [MSZ, Chapter 12, Section 12.10] Maschler, Solan, and Zamir, *Game Theory*.
- [Myerson 1981] Roger Myerson, "Optimal Auction Design", *Mathematics of
  Operations Research* 6(1):58-73.
