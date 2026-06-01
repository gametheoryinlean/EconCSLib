---
id: market_design.matching.one_to_one.stability
title: Stability (Individual Rationality + No Blocking Pair)
kind: definition
status: formalized
primary_topic: market_design
topics:
  - market_design
  - market_design.matching
  - market_design.matching.one_to_one
uses:
  - market_design.matching.one_to_one.matching
lean:
  modules:
    - EconCSLib.MarketDesign.Matching.Basic
  declarations:
    - Matching.IsBlocking
    - Matching.IsStable
source:
  spans:
    - artifact: msz-game-theory
      locator: "Chapter 22, Definitions 22.3–22.5"
      format: section
      note: "Individual rationality, blocking pair, stability"
verification:
  definition: accepted
  alignment: aligned
tags:
  - matching
  - stability
  - blocking-pair
---

# Stability of a Matching

Let $\mu$ be a matching in a one-to-one matching market $(M, W, \succ)$.

## Individual Rationality

$\mu$ is **individually rational** if no participant is matched to an
unacceptable partner:

- For every $i \in M$: $\mu(i) = \bot$ or $\mu(i) \succ_i \bot_i$.
- For every $j \in W$: $\mu^{-1}(j) = \bot$ or $\mu^{-1}(j) \succ_j \bot_j$.

## Blocking Pair

A pair $(i, j) \in M \times W$ **blocks** $\mu$ if both members strictly
prefer each other to their current $\mu$-partner (treating $\bot$ as the
lowest-ranked alternative):

- $j \succ_i \mu(i)$ (man $i$ prefers $j$ to his current match), AND
- $i \succ_j \mu^{-1}(j)$ (woman $j$ prefers $i$ to her current match).

## Stability

$\mu$ is **stable** if it is individually rational and admits no blocking pair.

Equivalently, $\mu$ is stable iff no pair $(i, j)$ would defect by mutually
breaking their current commitments and matching with each other.

In Lean, the three predicates live in `EconCSLib.MarketDesign.Matching.Basic`
as `Matching.IsIndividuallyRational`, `Matching.IsBlocking`, and
`Matching.IsStable`.

## References

- [MSZ Ch.22, Defs 22.3–22.5] Maschler, Solan, Zamir, *Game Theory*.
