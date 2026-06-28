---
id: mechanism_design.auction.online.secretary_quarter_competitive
title: Secretary Threshold Rule Is 1/4-Competitive
kind: theorem
status: proved
primary_topic: mechanism_design
topics:
  - mechanism_design
  - mechanism_design.auction
  - mechanism_design.auction.online
uses:
  - mechanism_design.auction.online.single_item_auction
  - mechanism_design.auction.online.no_constant_competitive
lean:
  modules:
    - EconCSLib.Examples.Online.SingleItemAuction
  declarations:
    - Online.Auction.Secretary.maxPairFold
    - Online.Auction.Secretary.auction
    - Online.Auction.Secretary.Favorable
    - Online.Auction.Secretary.welfare_nonneg
    - Online.Auction.Secretary.welfare_eq_max_of_favorable
    - Online.Auction.Secretary.favorableSet
    - Online.Auction.Secretary.favorableSet_card_ge
    - Online.Auction.Secretary.competitive
verification:
  statement: accepted
  proof: accepted
  alignment: aligned
tags:
  - auction
  - online-algorithm
  - secretary
  - competitive-ratio
  - random-order
---

# Secretary Threshold Rule Is 1/4-Competitive

**Theorem (Roughgarden, Problem 2.1(c)).** Under a uniformly random arrival
order, an explicit sample-then-threshold online auction obtains expected
welfare at least one quarter of the maximum valuation.

## The secretary auction

`Secretary.auction n` is the rule that posts unbeatable thresholds during
an *observe* phase (the first $\lfloor n/2\rfloor$ arrivals) and
thereafter posts the lex-max `(value, identity)` seen so far:

- `threshold h := if h.length < n/2 then ⊤ else ↑(toLex (maxPairFold h))`

where `maxPairFold h` folds the rejection history to find the
lexicographic maximum of `(value, identity)` pairs, starting from
$(0, \bot)$.

## Statement

For $n \ge 2$, an injective identity assignment
$g : \mathrm{Fin}\,n \to B$, nonneg valuations $v$, and truthful bids,

$$
\frac14 \cdot \max_i v_i
\;\le\;
\frac{1}{n!}\sum_{\sigma \in \mathrm{Perm}(\mathrm{Fin}\,n)}
\mathrm{welfare}\bigl(g\circ\sigma,\; v\circ\sigma\bigr),
$$

where the average over permutations $\sigma$ models the uniform random
arrival order (`competitive`).

## Proof

Let $\mathrm{MAX} = \max_i v_i$. The argument is the classic Dynkin /
secretary skeleton in three pieces.

### The favourable event

Call $\sigma$ **favourable** (`Favorable g v σ`) when the lex-argmax
bidder (under the `(v, g)` order) arrives in the second half
($\mathrm{max\_pos} \ge \lfloor n/2\rfloor$) and the lex-second bidder
arrives in the first half ($\mathrm{second\_pos} < \lfloor n/2\rfloor$).

The `Favorable` structure records:
- `v_is_max`: $\forall j,\; v\,j \le v\,(\sigma\,\mathrm{max\_pos})$
- `g_is_max_among_ties`: $\forall j,\; v\,j = v\,(\sigma\,\mathrm{max\_pos}) \to g\,j \le g\,(\sigma\,\mathrm{max\_pos})$
- `lex_is_second`: $\forall j \ne \sigma\,\mathrm{max\_pos}$, $j$ is
  lex-below the second
- `lex_second_lt_max`: the second is lex-strictly below the max
- `max_in_second_half`, `second_in_first_half`: the position constraints

### Welfare is exactly MAX on the favourable event

`welfare_eq_max_of_favorable`: on a favourable $\sigma$ the auction sells
to the lex-argmax bidder at the threshold, so welfare equals
$\mathrm{MAX}$. The core is an induction (`welfareAux_favorable`)
processing bidders one at a time:

- **Every pre-argmax bidder is rejected.** In the observe phase the price
  $\top$ rejects everything. In the second phase the threshold is the
  running lex-max of first-half bids, which is lex-at-least the
  second-largest; every remaining non-argmax bid is *lex-strictly* below
  the second-largest (by identity injectivity), hence below the threshold.
- **The argmax bidder is accepted**, since its `(value, identity)` pair
  lex-exceeds the threshold, yielding welfare $\mathrm{MAX}$.

### The favourable event has probability at least 1/4

`favorableSet_card_ge`: there are at least $n!/4$ favourable permutations.
The proof finds the lex-argmax $a$ and lex-second $c$ of the pairs
$(v\,i,\, g\,i)$ using `Finset.exists_max_image` with `Prod.Lex` order
(identity injectivity makes all pairs distinct, giving $a \ne c$ and
strict lex ordering). Each permutation $\sigma$ with $\sigma^{-1}(a)$
in the second half and $\sigma^{-1}(c)$ in the first half is favourable;
the count of such permutations equals

$$
|\mathrm{favorableSet}\,g\,v|
\;\ge\; (n-\lfloor n/2\rfloor)\cdot\lfloor n/2\rfloor\cdot (n-2)!,
$$

computed by the bijection $\sigma \mapsto \sigma^{-1}$ and the
combinatorial lemma `count_Q`. The elementary inequality
$4\cdot\lceil n/2\rceil\cdot\lfloor n/2\rfloor \ge n(n-1)$ gives
$4\,|\mathrm{favorableSet}\,g\,v| \ge n!$.

### Assembly

Welfare is nonneg everywhere (`welfare_nonneg`) and equals $\mathrm{MAX}$
on the favourable set, so the permutation sum is at least
$|\mathrm{favorableSet}|\cdot\mathrm{MAX} \ge \tfrac14 n!\,\mathrm{MAX}$;
dividing by $n!$ gives the bound.

## Why identity injectivity, not value injectivity

The hypothesis is `Function.Injective g` (identity injectivity), **not**
`Function.Injective v` (value injectivity). The lex acceptance rule
([[mechanism_design.auction.online.single_item_auction]]) resolves value
ties by comparing identities, so:

- The lex-argmax and lex-second of `(v i, g i)` are *unique* even when
  values collide, as long as identities are distinct.
- The rejection proof for pre-argmax bidders in the second phase uses
  lex-strict inequality — which only needs identity distinctness at
  value ties, not global value injectivity.

This is why `SingleItemAuction` uses a lexicographic threshold
`WithTop (Lex (F × B))` rather than a simple value threshold: without
the identity component, the theorem would need the mathematically
unnatural hypothesis that all bidders have distinct values. See the
definition node
([[mechanism_design.auction.online.single_item_auction]]) for the full
design rationale.

## Why it matters

Together with the deterministic impossibility
([[mechanism_design.auction.online.no_constant_competitive]]), this closes
Problem 2.1: worst-case order admits no constant competitive ratio, yet
random order restores a constant one. It is the single-item,
prophet-free instance of the secretary phenomenon — sample a constant
fraction of the input to set a threshold, then take the first item that
beats it.

## References

- [Roughgarden 2016, Lecture 2, Problem 2.1(c)] Tim Roughgarden, *Twenty
  Lectures on Algorithmic Game Theory*, Cambridge University Press.
  Random-order (secretary) analysis of the online auction.
