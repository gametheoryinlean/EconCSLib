# Staged Auction Topic Catalog

Canonical folder topic: `auction`

## Subtopics

- `auction.basic` - auction formats, bid profiles, ordered-bid utilities,
  Vickrey (second-price) and first-price sealed-bid mechanisms.
- `auction.knapsack` - binary allocations, welfare maximization, relaxations,
  and dynamic programming.
- `auction.bayesian` - Bayesian single-item auction framework (CDF/density,
  opponent priors), interim quantities and IC, MSZ Chapter 12 blueprint
  stubs (Dutch/English equivalences, symmetric IPV equilibria for first-
  price and all-pay, entry fee and reserve price analysis, risk-aversion
  comparisons).

## Source Guidance

- Use [Krishna 2010] Vijay Krishna, *Auction Theory*, 2nd ed., for private-value auctions, first-price and
  second-price auctions, revenue equivalence, interdependent values, collusion,
  multiple-object auctions, packages, positions, and auction-specific mechanism
  design.
- Use [MSZ Chapter 12] Maschler, Solan, and Zamir, *Game Theory*, for the IPV / Bayesian-equilibrium track and
  for the strategic equivalences (Dutch≡FP, English≡SP under IPV).

## Boundary

Put general truthfulness, transfer interfaces, Myerson optimal-auction
machinery, revenue equivalence, reserve-price characterisations, and the
selling-problem framework under `mechanism_design`. The `auction` topic
covers concrete auction formats (single-item, multi-item, knapsack,
Bayesian single-item) and their format-specific equilibrium and DSIC
results.
