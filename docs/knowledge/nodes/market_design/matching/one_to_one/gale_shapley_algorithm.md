---
id: market_design.matching.one_to_one.gale_shapley_algorithm
title: Gale-Shapley Deferred Acceptance Algorithm
kind: definition
status: formalized
primary_topic: market_design
topics:
  - market_design
  - market_design.matching
  - market_design.matching.one_to_one
uses:
  - market_design.matching.one_to_one.market
  - market_design.matching.one_to_one.matching
lean:
  modules:
    - EconCSLib.MarketDesign.Matching.GaleShapley
  declarations:
    - GS.daStep
    - GS.daRun
    - GS.finalState
    - GS.gs
source:
  spans:
    - artifact: msz-game-theory
      locator: "Chapter 22, Algorithm 22.6"
      format: section
      note: "Men-proposing deferred-acceptance algorithm"
verification:
  definition: accepted
  alignment: aligned
tags:
  - matching
  - gale-shapley
  - deferred-acceptance
  - algorithm
---

# Gale-Shapley Deferred Acceptance Algorithm

Men-proposing version on a one-to-one matching market $(M, W, \succ)$.

## Algorithm

Initialize: every man is free; every woman holds no offer.

Repeat until no free man has any acceptable woman remaining on his list:

1. **Propose.** Pick a free man $i$ who still has at least one acceptable
   woman not yet proposed to. Let $j$ be $i$'s most-preferred such woman.
   $i$ proposes to $j$ (and crosses $j$ off his list, whether or not she
   accepts).
2. **Decide.**
   - If $j$ currently holds no offer, $j$ tentatively accepts $i$.
   - If $j$ currently holds an offer from $i'$ and prefers $i$ to $i'$,
     $j$ accepts $i$ and rejects $i'$ (who becomes free again).
   - Else $j$ rejects $i$.

The algorithm terminates because the total number of (man, woman) proposal
pairs is at most $|M| \cdot |W|$ and strictly grows each round.

The output matching matches each woman to the man whose offer she is
holding at termination; unmatched men get $\bot$, unmatched women get $\bot$.

## Variant: Women-Proposing

Swap the roles of $M$ and $W$. The output is generally a *different* stable
matching (see [[lattice]]); both are stable but with opposite optimality
properties for the two sides (see [[proposing_optimal]]).

In Lean, the men-proposing algorithm is implemented in
`EconCSLib.MarketDesign.Matching.GaleShapley` over `Fin n` indices: one
round is `GS.daStep` (free men propose, women keep the best of held + new
offers, free men advance their cursor), iterated by `GS.daRun` with fuel
`n*n + 1` to `GS.finalState`, and `GS.gs` reads off each woman's final
holding as the output matching.

## References

- [MSZ Ch.22, Alg 22.6] Maschler, Solan, Zamir, *Game Theory*.
- Gale & Shapley (1962). *College Admissions and the Stability of Marriage*. AMM 69, 9–15.
