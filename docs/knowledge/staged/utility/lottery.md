---
id: foundation.utility.lottery
title: Lottery
kind: definition
status: staged
uses:
  - foundation.preference.relation
lean:
  modules:
    - EconCSLib.Foundation.Utility.Lottery
  declarations:
    - Lottery
    - Lottery.pure
    - Lottery.mix
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
tags:
  - utility
  - lottery
---

# Lottery

For a finite set of outcomes $O$, a lottery is a probability distribution on
$O$. The degenerate lottery at $o\in O$ assigns probability one to $o$.

Given lotteries $L_1,L_2$ and a scalar $\alpha\in[0,1]$, the compound lottery
$$
  [\alpha L_1,(1-\alpha)L_2]
$$
is the lottery assigning each outcome the probability
$$
  \alpha L_1(o)+(1-\alpha)L_2(o).
$$

## Implementation note

`Lottery 𝕜 O` is a domain-flavored `abbrev` for `stdSimplex 𝕜 O`. The
constructors `Lottery.pure` and `Lottery.mix` are definitional aliases for
`stdSimplex.pure` and `stdSimplex.mix` from `Core.Simplex`; the canonical
algebra (`Lottery.expectedValue_pure`, `Lottery.expectedValue_mix`,
`Lottery.expectedValue_mono`, `Lottery.expectedValue_const`) is one-line
wrappers over `wsum_pure_apply`, `wsum_mix`, `wsum_le_wsum`, `wsum_const`.
See [[math.simplex.mix]] for the underlying convex-combination vocabulary.

## References

- [MSZ, Chapter 2, Definitions 2.9-2.11] Maschler, Solan, and Zamir, *Game Theory*. Lotteries, degenerate lotteries, and compound lotteries.
