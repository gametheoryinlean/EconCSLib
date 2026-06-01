---
id: market_design.matching.one_to_one.matching
title: Matching (Partial Bijection)
kind: definition
status: formalized
primary_topic: market_design
topics:
  - market_design
  - market_design.matching
  - market_design.matching.one_to_one
uses:
  - market_design.matching.one_to_one.market
lean:
  modules:
    - EconCSLib.MarketDesign.Matching.Basic
  declarations:
    - Matching
source:
  spans:
    - artifact: msz-game-theory
      locator: "Chapter 22, Definition 22.2"
      format: section
      note: "Matching as a partial bijection between two participant sets"
verification:
  definition: accepted
  alignment: aligned
tags:
  - matching
  - market-design
---

# Matching (Partial Bijection)

Given a one-to-one matching market $(M, W, \succ)$, a **matching** is a
partial function $\mu : M \to W \cup \{\bot\}$ together with the dual
$\mu^{-1} : W \to M \cup \{\bot\}$ such that:

- $\mu$ is injective on its matched domain (a man is matched to at most one woman).
- $\mu(i) = j \iff \mu^{-1}(j) = i$ for $i \in M$, $j \in W$ (consistency).
- If $\mu(i) = \bot$ we say $i$ is **unmatched**; symmetric for $j$.

Equivalently, $\mu$ is a set $\{(i, j) : \mu(i) = j\} \subseteq M \times W$ in
which each element of $M$ appears at most once and each element of $W$ appears
at most once.

In Lean this corresponds to the `Matching M W` structure in
`EconCSLib.MarketDesign.Matching.Basic` carrying both sides of the partial
bijection plus the consistency invariant.

## References

- [MSZ Ch.22, Def 22.2] Maschler, Solan, Zamir, *Game Theory*.
