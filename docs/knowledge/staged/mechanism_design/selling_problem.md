---
id: mechanism_design.bayesian.selling_problem
title: Bayesian Selling Problem (IPV)
kind: definition
status: staged
primary_topic: mechanism_design
topics:
- mechanism_design
- mechanism_design.bayesian
uses:
- mechanism_design.bayesian.bayesian_mechanisms
- mechanism_design.transfer.mechanisms_with_transfers
verification:
  definition: accepted
  proof: not_applicable
tags:
- mechanism-design
- bayesian
- selling-problem
- ipv
---

# Bayesian Selling Problem (IPV)

The **Bayesian selling problem** is the canonical mechanism-design
setting for auction-style allocation of one or more goods to bidders
with private information. It is the input shape consumed by Myerson's
optimal-auction theorem
([[mechanism_design.myerson.optimal_auction]]), revenue equivalence
([[mechanism_design.myerson.revenue_equivalence]]), and reserve-price
characterisation ([[mechanism_design.myerson.reserve_price]]).

## Setup

A selling problem is a tuple
$\mathcal{S} = (I, A, (T_i)_{i \in I}, (F_i)_{i \in I}, (v_i)_{i \in I})$
where:

- $I$ is a finite set of bidders.
- $A$ is the set of feasible allocations (e.g. "no sale" plus "bidder
  $i$ wins" for a single-object auction).
- $T_i \subseteq \mathbb{R}_{\ge 0}$ is bidder $i$'s type space.
- $F_i$ is the common-knowledge prior distribution on $T_i$.
- $v_i : T_i \to (A \to \mathbb{R})$ specifies bidder $i$'s value for
  each allocation as a function of their (privately known) type.

**Independent Private Values (IPV)** is the standard assumption that
the joint type prior factorises: $F(t_1, \dots, t_n) = \prod_i F_i(t_i)$.

## Selling mechanism

A *selling mechanism* for $\mathcal{S}$ is a Bayesian mechanism with
transfers ([[mechanism_design.transfer.mechanisms_with_transfers]])
whose outcome space includes both the allocation and the per-bidder
payment:

- **Allocation rule** $x : T \to \Delta(A)$ (possibly randomised).
- **Payment rule** $p : T \to I \to \mathbb{R}$ — bidder $i$ pays
  $p_i(t)$ at report profile $t$.

The induced quasi-linear utility for bidder $i$ at true type $t_i$ and
report $b_i$ given others' reports $b_{-i}$ is
$$
u_i(b_i; t_i, b_{-i}) \;=\; \mathbb{E}_{a \sim x(b_i, b_{-i})}\big[v_i(t_i)(a)\big] - p_i(b_i, b_{-i}).
$$

## Standard specialisations

- **Single-object auction**: $A = I \cup \{\bot\}$ with $\bot$ = "no
  sale"; $v_i(t_i)(j) = t_i$ if $j = i$, $0$ otherwise.
- **Multi-unit auctions**: $A$ encodes the number of units each bidder
  receives.
- **Combinatorial auctions**: $A$ enumerates allocations of multiple
  heterogeneous items.

## Lean port (deferred — see #173)

Planned Lean module: `EconCSLib/MechanismDesign/Auction/MechBayesianSelling.lean`.

Planned declarations:

- `BayesianSellingProblem` structure
- `BayesianSellingMechanism` (specialisation of
  `BayesianMechanismWithTransfers`)
- `IPVAssumption` (independence of priors)
- Standard examples: single-object, multi-object.

The Lean half is tracked in [#173](https://github.com/gametheoryinlean/EconCSLib/issues/173); this blueprint stub captures the structural setup so downstream nodes (revenue equivalence, optimal auction, reserve price) can reference the framework concretely.

## References

- [MSZ Chapter 12, §12.1, Def 12.1, Def 12.5] Maschler, Solan, Zamir,
  *Game Theory*.
- Krishna, V. (2010). *Auction Theory*, 2nd ed., Ch. 2.. IPV framework.
