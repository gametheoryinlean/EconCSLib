---
id: market_design.matching.one_to_one.lattice
title: Lattice Structure of Stable Matchings (Conway-Knuth)
kind: theorem
status: proved
primary_topic: market_design
topics:
  - market_design
  - market_design.matching
  - market_design.matching.one_to_one
uses:
  - market_design.matching.one_to_one.stability
  - market_design.matching.one_to_one.proposing_optimal
lean:
  modules:
    - EconCSLib.MarketDesign.Matching.Lattice
  declarations:
    - GS.opposed_preferences
    - GS.stableJoin_isStable
    - GS.stableMeet_isStable
    - GS.StableMatching
    - GS.StableMatching.gsStable_isGreatest
source:
  spans:
    - artifact: msz-game-theory
      locator: "Chapter 22, Theorem 22.12"
      format: section
      note: "Set of stable matchings is a complete distributive lattice"
verification:
  statement: accepted
  proof: accepted
  alignment: aligned
tags:
  - matching
  - lattice
  - stable-set
---

# Lattice of Stable Matchings

**Theorem (Conway, reported by Knuth 1976).** The set of stable matchings
of any finite one-to-one matching market forms a **complete distributive
lattice** under the partial order

$$\mu \le_M \mu' \quad \iff \quad \mu(i) \preceq_i \mu'(i) \text{ for all } i \in M$$

("men weakly prefer $\mu'$ to $\mu$"). The join $\mu \vee \mu'$ matches each
man to his preferred of the two partners; the meet $\mu \wedge \mu'$ matches
each man to his less-preferred. Both are stable matchings.

Equivalently, under $\le_W$ defined dually (women's preference), the lattice
is the order-dual.

## Extrema

- Top under $\le_M$: the **men-optimal** matching $\mu^M$ (output of
  men-proposing GS — see [[proposing_optimal]]).
- Bottom under $\le_M$: the **women-optimal** matching $\mu^W$ (output of
  women-proposing GS).

These two are also the bottom and top respectively under $\le_W$ — the men's
and women's interests are exactly opposed across the stable set.

## Proof Sketch

The non-trivial part is showing $\mu \vee \mu'$ (each man picks his preferred
partner from $\mu$ and $\mu'$) is itself a matching (not just a function) and
is stable.

*Matching*: We must show no woman is "picked" by two different men. If man
$i_1$'s preferred partner is $j$, and $i_2$'s preferred is also $j$, then $j$
is matched to $i_1$ in one of $\mu, \mu'$ and to $i_2$ in the other. By the
opposed-preferences phenomenon (a corollary of stability), $j$ also prefers
exactly the opposite — contradiction.

*Stability*: If $(i, k)$ blocks $\mu \vee \mu'$, then $k$ ranks higher on
$i$'s list than his max of $\mu(i), \mu'(i)$, so $(i, k)$ blocks both $\mu$
and $\mu'$ — contradicting stability of either.

Distributivity follows from the same opposed-preferences structure.

## Formalization

In the balanced full-preference Lean model (`Preferences n` via
`MatchingMarket.ofEquivData`, every stable matching perfect), the lattice
structure is formalized as a `Lattice` instance on
`GS.StableMatching w m` (`EconCSLib.MarketDesign.Matching.Lattice`):

- `GS.opposed_preferences` (+ `opposed_preferences_women`) — the
  opposed-preferences lemma, proved by a direct pairwise blocking argument.
- `GS.stableJoin` / `GS.stableMeet` — the join and meet as `Matching`s, each
  built from an injective-hence-bijective partner map (`joinWoman` /
  `meetMan`); the injectivity is the "no woman picked twice" step and uses
  `opposed_preferences`.
- `GS.stableJoin_isStable` / `GS.stableMeet_isStable` — both operations are
  closed within the stable set.
- The `Lattice (GS.StableMatching w m)` instance — the men-preference order
  (`σ ≤ τ` iff every man weakly prefers `τ`) with `⊔ = stableJoin`,
  `⊓ = stableMeet`, all lattice axioms discharged.
- `GS.StableMatching.gsStable_isGreatest` — the **men-proposing GS output is
  the greatest element** ($\top$) of this lattice: every man weakly prefers
  it to his partner in any other stable matching. This is
  [[proposing_optimal]] (`galeShapley_isProposingOptimal`) packaged as the
  lattice maximum, identifying the men-optimal extremum $\mu^M$ with the GS
  output.

All sorry-free (axioms: `propext`, `Classical.choice`, `Quot.sound`).

**Not yet formalized** (classical, future refinements): *distributivity* of
the lattice, *completeness*, and the *women-proposing* bottom extremum
$\mu^W$ (no women-proposing GS is formalized yet). The general
$\bot$/unequal-cardinality version is also out of scope of the balanced model.

## Consequences

- The number of stable matchings is bounded by combinatorial counts on the
  lattice (e.g., chain lengths, antichains).
- The Conway-Knuth lattice is the foundation for the [[rural_hospitals]]
  invariant ("same set of matched participants across all stable matchings").

## References

- [MSZ Ch.22, Thm 22.12] Maschler, Solan, Zamir, *Game Theory*.
- Knuth (1976), *Marriages Stables*. Université de Montréal.
- Roth & Sotomayor (1990), Ch. 2 §2.3.
