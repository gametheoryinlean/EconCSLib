---
id: mechanism_design.auction.online.secretary_quarter_competitive
title: Secretary Threshold Rule Is 1/4-Competitive
kind: theorem
status: staged
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
    - Online.Auction.Secretary.auction
    - Online.Auction.maxV
    - Online.Auction.Secretary.Favorable
    - Online.Auction.Secretary.welfare_eq_argmax_of_favorable
    - Online.Auction.Secretary.welfare_eq_max_of_favorable
    - Online.Auction.Secretary.favorableSet
    - Online.Auction.Secretary.favorableSet_card_ge
    - Online.Auction.Secretary.competitive
    - Online.Auction.Secretary.surrogate
    - Online.Auction.Secretary.surrogate_injective
    - Online.Auction.Secretary.surrogate_nonneg
    - Online.Auction.Secretary.surrogate_lt_n
    - Online.Auction.Secretary.surrogate_refines
    - Online.Auction.Secretary.competitive_of_nonneg
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

Concretely, `Secretary.auction n M` is the rule that posts the unbeatable
price $M + 1$ during an *observe* phase (the first $\lfloor n/2\rfloor$
arrivals, where $M$ bounds every valuation, so all are rejected) and
thereafter posts the largest bid seen so far. For $n \ge 2$, an injective
nonnegative profile $v$ bounded by $M$, and truthful bids,

$$
\frac14 \cdot \max_i v_i
\;\le\;
\frac{1}{n!}\sum_{\sigma \in \mathrm{Perm}(\mathrm{Fin}\,n)}
\mathrm{welfare}\bigl(v\circ\sigma,\; v\circ\sigma\bigr),
$$

where the average over permutations $\sigma$ models the uniform random
arrival order (`competitive`).

## Proof

Let $\mathrm{MAX} = \max_i v_i$. The argument is the classic Dynkin /
secretary skeleton in three pieces.

### The favourable event

Call $\sigma$ **favourable** (`Favorable v σ`) when the argmax bidder
arrives in the second half ($\mathrm{max\_pos} \ge \lfloor n/2\rfloor$) and
the second-largest bidder arrives in the first half
($\mathrm{second\_pos} < \lfloor n/2\rfloor$).

### Welfare is exactly MAX on the favourable event

`welfare_eq_max_of_favorable`: on a favourable $\sigma$ the auction sells to
the argmax bidder, so welfare equals $\mathrm{MAX}$. The core is an
induction (`welfareFrom_aux`) processing bidders one at a time:

- **Every pre-argmax bidder is rejected.** In the observe phase the price
  $M+1$ exceeds every legal bid. In the second phase the threshold is the
  running maximum of first-half bids, which is at least $v(\mathrm{second})$
  (the second-largest sits in the first half), while every remaining
  non-argmax bid is *strictly* below $v(\mathrm{second})$.
- **The argmax bidder is accepted**, since its value
  $\mathrm{MAX} > v(\mathrm{second}) \ge$ threshold, yielding welfare
  $\mathrm{MAX}$.

### The favourable event has probability at least 1/4

`favorableSet_card_ge`: there are at least $n!/4$ favourable permutations.
Characterising favourability by the inverse arrival positions of the unique
argmax $a$ and second-largest $c$ turns the count into a product

$$
|\mathrm{favorableSet}\,v|
\;=\; (n-\lfloor n/2\rfloor)\cdot\lfloor n/2\rfloor\cdot (n-2)!,
$$

and the elementary inequality
$4\cdot\lceil n/2\rceil\cdot\lfloor n/2\rfloor \ge n(n-1)$ gives
$4\,|\mathrm{favorableSet}\,v| \ge n!$.

### Assembly

Welfare is nonnegative everywhere and equals $\mathrm{MAX}$ on the
favourable set, so the permutation sum is at least
$|\mathrm{favorableSet}\,v|\cdot\mathrm{MAX} \ge \tfrac14 n!\,\mathrm{MAX}$;
dividing by $n!$ gives the bound.

## Why the plain value-threshold needs injectivity

`competitive` (above) assumes $v$ is **injective**, and for the *plain
value-threshold* rule this cannot be dropped. The obstruction is value-ties
*at the threshold*: in the welfare step injectivity is exactly what makes the
pre-argmax bids *strictly* below the threshold, so the weak acceptance rule
$p \le b$ does not let a tied bidder clear the price early; in the counting
step it pins the argmax and second-largest to unique positions.

The failure is quantitative, not cosmetic: for $v = (1, 0, \dots, 0)$ on $n$
bidders (a unique maximum, ties only among the zeros) the threshold collapses
to $0$ in the second phase, so the first second-phase arrival — almost always
a zero — clears it and wins. Welfare equals $1$ only when the lone high
bidder lands in the first second-phase slot, probability $1/n$, giving
expected welfare $1/n \to 0$. So for the plain value-threshold, **no**
constant $c > 0$ survives dropping injectivity; the guarantee degrades as
$\Theta(1/n)$.

## Removing injectivity via a compatible total order on bidders

`competitive_of_nonneg` drops the injectivity assumption entirely, for
**all** nonnegative $v$ (ties allowed). The key observation is that the
auction must know bidder *identity*: bidders carry a total order
compatible with their valuations, and the auction compares by this
order rather than by raw value alone.

Formally, the theorem is universal over a **bid profile**
$b : \mathrm{Fin}\,n \to F$ satisfying four conditions:

1. **injective** — distinct bidders get distinct rankings;
2. **nonneg** — $0 \le b_i$ for all $i$;
3. **bounded** — $b_i < n$ (so the observe phase at price $n+1$ still
   rejects every bidder);
4. **refines $v$** — $b_i \le b_j \Rightarrow v_i \le v_j$ (the
   ranking is compatible with the true valuation ordering).

Such a $b$ encodes a total order on bidders compatible with their
valuations. The canonical construction is the **rank surrogate**
`surrogate v`, where `surrogate v i` is the number of bidders ranking
strictly below $i$ under the lexicographic order
$(v_j, j) <_{\mathrm{lex}} (v_i, i)$, giving values in
$\{0,\dots,n-1\}$. Lemmas `surrogate_injective`, `surrogate_nonneg`,
`surrogate_lt_n`, and `surrogate_refines` witness that the surrogate
satisfies the four conditions.

Because $b$ is injective and refines $v$, two things hold:

- the favourable-event count `favorableSet_card_ge` applies to $b$
  **verbatim** — it only ever used distinctness;
- on the favourable event the captured bidder is the $b$-argmax, which
  (by refinement) is a *true* $v$-argmax, so the credited welfare is
  exactly $\mathrm{maxV}\,v$ (`v_argmax_of_favorable_refinement`).

The welfare core is the same induction, stated as
`welfare_eq_argmax_of_favorable`: it accumulates a separate valuation $w$
while comparing the bid $b$, giving
$\mathrm{welfare}(w\circ\sigma,\,b\circ\sigma) = w(\sigma\,\mathrm{max\_pos})$;
the injective `welfare_eq_max_of_favorable` is its diagonal $w = b = v$.

This is the standard secretary tie-breaking trick — break ties by a fixed
identity rule to make a tied instance behave like a distinct-valued one — and
it needs neither a "must-hire-last" forced sale (which would violate
individual rationality) nor any extra randomness beyond the arrival order.

`competitive_of_nonneg` holds for every `n ≥ 1`: the `n ≥ 2` core is above,
and `n = 1` is trivial (the lone bidder always clears the zero opening price,
so welfare `= max v`). Only `n = 0` is excluded, since `max v` is then
undefined.

## Why it matters

Together with the deterministic impossibility
([[mechanism_design.auction.online.no_constant_competitive]]), this closes
Problem 2.1: worst-case order admits no constant competitive ratio, yet
random order restores a constant one. It is the single-item, prophet-free
instance of the secretary phenomenon — sample a constant fraction of the
input to set a threshold, then take the first item that beats it.

## References

- [Roughgarden 2016, Lecture 2, Problem 2.1(c)] Tim Roughgarden, *Twenty
  Lectures on Algorithmic Game Theory*, Cambridge University Press.
  Random-order (secretary) analysis of the online auction.
