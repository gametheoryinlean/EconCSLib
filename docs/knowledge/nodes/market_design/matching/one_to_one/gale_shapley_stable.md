---
id: market_design.matching.one_to_one.gale_shapley_stable
title: Gale-Shapley Theorem (Existence of Stable Matching)
kind: theorem
status: proved
primary_topic: market_design
topics:
  - market_design
  - market_design.matching
  - market_design.matching.one_to_one
uses:
  - market_design.matching.one_to_one.gale_shapley_algorithm
  - market_design.matching.one_to_one.stability
lean:
  modules:
    - EconCSLib.MarketDesign.Matching.GaleShapley
  declarations:
    - galeShapley_isStable
source:
  spans:
    - artifact: msz-game-theory
      locator: "Chapter 22, Theorem 22.7"
      format: section
      note: "Gale-Shapley DA outputs a stable matching"
verification:
  statement: accepted
  proof: accepted
  alignment: aligned
tags:
  - matching
  - stability
  - existence
  - gale-shapley
---

# Gale-Shapley Theorem

**Theorem.** Every finite one-to-one matching market $(M, W, \succ)$ admits
a stable matching. Specifically, the matching output by the men-proposing
deferred-acceptance algorithm ([[gale_shapley_algorithm]]) is stable.

## Proof Sketch

Run the men-proposing algorithm to completion (termination is guaranteed by
the proposal-count argument).

Let $\mu$ be the output matching. We verify the two stability conditions:

**Individual rationality.** A man $i$ only ever proposes to women he finds
acceptable (the algorithm consults his preference list). A woman $j$ only
ever holds offers from men she finds acceptable (she rejects unacceptable
proposers). Hence every matched pair is mutually acceptable.

**No blocking pair.** Suppose toward contradiction that $(i, j)$ blocks
$\mu$, i.e., $j \succ_i \mu(i)$ and $i \succ_j \mu^{-1}(j)$.

Since $j \succ_i \mu(i)$, woman $j$ ranks higher than $\mu(i)$ on man $i$'s
list, so $i$ must have proposed to $j$ at some round (before settling for
$\mu(i)$ or staying unmatched). At the round $i$ proposed to $j$:

- Either $j$ rejected $i$, in which case $j$ was holding (or later switched
  to) some man $i'$ with $i' \succ_j i$, OR
- $j$ accepted $i$ but was later replaced by some $i' \succ_j i$.

In either case, once $j$ has held an offer she never reverts to unmatched
and her holding partner only ever improves (the algorithm has "no-going-back"
monotonicity on the receiving side). So her final partner satisfies
$\mu^{-1}(j) \succeq_j i'$ for the rejecting/replacing $i'$, and since
$i' \succ_j i$ we get $\mu^{-1}(j) \succ_j i$ — contradicting
$i \succ_j \mu^{-1}(j)$.

## Lean Status

**Proved** (no `sorry`) at
`EconCSLib.MarketDesign.Matching.GaleShapley.galeShapley_isStable`; axiom scan
shows only `propext`, `Classical.choice`, `Quot.sound`. Closed under MT-L1
(#203). The two structural ingredients are now in place:

1. The "monotone holding" invariant `holding_rank_mono_run` (+ the
   stay-matched companion `held_preserved_run`): a woman's holding partner
   can only improve over time and she never reverts to unmatched.
2. The "no free men at termination" property `finalState_no_free_men`,
   from the cursor-sum growth bound versus the `n*n` proposal ceiling.

The blocking-pair argument is assembled in the `RSInv` (Roth–Sotomayor)
run-state invariant and discharged by `rsinv_stability`.

## References

- [MSZ Ch.22, Thm 22.7] Maschler, Solan, Zamir, *Game Theory*.
- Gale & Shapley (1962).
