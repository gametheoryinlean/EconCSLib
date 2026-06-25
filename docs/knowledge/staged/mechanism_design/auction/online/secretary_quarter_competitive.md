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

## Removing injectivity by breaking ties on identity

`competitive_of_nonneg` drops injectivity entirely, for **all** nonnegative
$v$ (ties allowed), at the cost of one change: the auction compares bidders
by the lexicographic key $(\text{value}, \text{index})$ instead of value
alone. Concretely the bidders submit the **rank surrogate**
`surrogate v` — `surrogate v i` is the number of bidders ranking strictly
below $i$ under $(v_j, j) <_{\mathrm{lex}} (v_i, i)$, a value in
$\{0,\dots,n-1\}$ — and the auction (run with bound $M' = n$, so the observe
phase still rejects every rank) selects on these ranks, while the welfare
credited is the bidder's *true* valuation `v`.

Because the surrogate is **injective** (distinct ranks) and **refines** $v$
(`surrogate v i ≤ surrogate v j → v i ≤ v j`), two things hold:

- the favourable-event count `favorableSet_card_ge` applies to the surrogate
  **verbatim** — it only ever used distinctness;
- on the favourable event the captured bidder is the surrogate-argmax, which
  (by refinement) is a *true* $v$-argmax, so the credited welfare is exactly
  $\mathrm{maxV}\,v$ (`v_argmax_of_surrogate_favorable`).

The welfare core is the same induction, now stated as
`welfare_eq_argmax_of_favorable`: it accumulates a separate valuation $w$
while comparing the bid $b$, giving
$\mathrm{welfare}(w\circ\sigma,\,b\circ\sigma) = w(\sigma\,\mathrm{max\_pos})$;
the injective `welfare_eq_max_of_favorable` is its diagonal $w = b = v$. With
$w = v$, $b = \texttt{surrogate }v$, the same assembly yields
$\tfrac14\,\mathrm{maxV}\,v \le \tfrac1{n!}\sum_\sigma
\mathrm{welfare}(v\circ\sigma,\,\texttt{surrogate }v\circ\sigma)$, with only
the nonnegativity of $v$ surviving as a hypothesis.

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
