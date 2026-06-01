---
id: market_design.matching.one_to_one.strategy_proofness_proposing
title: Strategy-Proofness of Gale-Shapley for the Proposing Side (Roth 1982)
kind: theorem
status: staged
primary_topic: market_design
topics:
  - market_design
  - market_design.matching
  - market_design.matching.one_to_one
uses:
  - market_design.matching.one_to_one.gale_shapley_stable
  - market_design.matching.one_to_one.proposing_optimal
  - mechanism_design.basic.dsic_predicate
source:
  spans:
    - artifact: msz-game-theory
      locator: "Chapter 22, Theorem 22.16 (or Roth 1982)"
      format: section
      note: "Men-proposing GS is strategy-proof for men; not for women"
verification:
  statement: accepted
  proof: gap
tags:
  - matching
  - strategy-proofness
  - gale-shapley
  - mechanism-design
---

# Roth 1982: Strategy-Proofness for the Proposing Side

**Theorem (Roth 1982).** The men-proposing Gale-Shapley mechanism is
**dominant-strategy incentive-compatible (DSIC) for the men**: for every
man $i$, truthfully reporting his preference list $\succ_i$ weakly
dominates every misreport $\succ_i'$, regardless of what the other men and
women report.

Formally: let $\mathrm{GS}^M : \succ \mapsto \mu^M(\succ)$ denote the
men-proposing matching function. For every $i \in M$, every $\succ_i'$, and
every fixed report profile $\succ_{-i}$:

$$\mathrm{GS}^M(\succ_i, \succ_{-i})(i) \succeq_i \mathrm{GS}^M(\succ_i', \succ_{-i})(i)$$

where the LHS uses $i$'s *true* preferences $\succ_i$ for comparison.

## Asymmetry: Not Strategy-Proof for Women

The women-proposing analogue holds for women, but in the men-proposing
mechanism the *women* have profitable misreports (they can sometimes get a
strictly preferred match by truncating their preference list). This
asymmetry is fundamental: Roth showed that **no stable matching mechanism
is DSIC for both sides simultaneously** (Roth 1982 impossibility).

## Proof Sketch

The key tool is the *blocking lemma* (Gale-Sotomayor 1985): if a man $i$
misreports and gets a strictly better partner under the mechanism, then in
the resulting matching there must be a blocking pair involving $i$ and his
*true* preferred achievable partner — contradicting stability.

More concretely, suppose $i$ misreports $\succ_i'$ and ends up with
$j' = \mathrm{GS}^M(\succ_i', \succ_{-i})(i)$ such that $j' \succ_i \mathrm{GS}^M(\succ)(i)$.
Truth-telling gives $i$ his best achievable partner under the true
preferences (men-optimal property). So $j'$ must be *unachievable* under
the true profile — meaning there is no stable matching in which $i$ gets
$j'$ when truth is told. Combining with $j'$'s acceptance of $i$ under the
misreport gives the contradiction.

## Cross-Reference

Connects matching theory to mechanism design's general DSIC framework
([[mechanism_design.basic.dsic_predicate]]).

## Lean Status

Tracked by MT-L3 (#205). Depends on:
- [[gale_shapley_stable]] (stability of GS output),
- [[proposing_optimal]] (men-optimality), and
- the blocking lemma (Gale-Sotomayor 1985) which will need its own helper
  lemma in Lean.

## References

- [MSZ Ch.22, Thm 22.16] Maschler, Solan, Zamir, *Game Theory*.
- Roth (1982). *The Economics of Matching: Stability and Incentives*. Math. Oper. Res. 7, 617–628.
- Dubins & Freedman (1981). *Machiavelli and the Gale-Shapley Algorithm*. AMM 88.
- Gale & Sotomayor (1985). *Some Remarks on the Stable Matching Problem*. Discrete Applied Math 11.
- Roth & Sotomayor (1990), Ch. 4.
