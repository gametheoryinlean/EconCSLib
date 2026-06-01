---
id: market_design.matching.one_to_one.market
title: Matching Market (One-to-One)
kind: definition
status: formalized
primary_topic: market_design
topics:
  - market_design
  - market_design.matching
  - market_design.matching.one_to_one
lean:
  modules:
    - EconCSLib.MarketDesign.Matching.Basic
  declarations:
    - MatchingMarket
source:
  spans:
    - artifact: msz-game-theory
      locator: "Chapter 22, Definition 22.1"
      format: section
      note: "Two-sided matching market with strict preferences"
verification:
  definition: accepted
  alignment: aligned
tags:
  - matching
  - market-design
  - one-to-one
---

# Matching Market (One-to-One)

A **one-to-one matching market** consists of:

- A finite nonempty set $M$ of *men* (proposers).
- A finite nonempty set $W$ of *women* (receivers).
- For each $i \in M$, a strict linear order $\succ_i$ over $W \cup \{\bot_i\}$,
  where $\bot_i$ represents staying unmatched.
- For each $j \in W$, a strict linear order $\succ_j$ over $M \cup \{\bot_j\}$.

We say $j$ is **acceptable** to $i$ if $j \succ_i \bot_i$ (and symmetrically for
$i$ acceptable to $j$). The market makes no use of cardinal utilities — only
the ordinal preferences matter.

In Lean this is the `MatchingMarket` structure under
`EconCSLib.MarketDesign.Matching.Basic`. The "two-sided" terminology refers to
the two disjoint participant sets $M$, $W$; "one-to-one" refers to each
participant being matched to at most one partner.

## References

- [MSZ Ch.22, Def 22.1] Maschler, Solan, Zamir, *Game Theory*.
