---
id: market_design.matching.one_to_one.rural_hospitals
title: Rural Hospitals Theorem
kind: theorem
status: proved
primary_topic: market_design
topics:
  - market_design
  - market_design.matching
  - market_design.matching.one_to_one
uses:
  - market_design.matching.one_to_one.stability
lean:
  modules:
    - EconCSLib.MarketDesign.Matching.RuralHospitals
  declarations:
    - GS.stable_matching_perfect
source:
  spans:
    - artifact: msz-game-theory
      locator: "Chapter 22, Theorem 22.14"
      format: section
      note: "Same set of matched participants across all stable matchings"
verification:
  statement: accepted
  proof: accepted
  alignment: aligned
tags:
  - matching
  - rural-hospitals
  - invariance
---

# Rural Hospitals Theorem

**Theorem (Roth 1986; McVitie–Wilson 1970 for one-to-one).** In a finite
one-to-one matching market $(M, W, \succ)$, the set of **matched participants**
is invariant across all stable matchings:

$$\{ i \in M : \mu(i) \ne \bot \} = \{ i \in M : \mu'(i) \ne \bot \}$$

for any two stable matchings $\mu, \mu'$ (and symmetrically for $W$). In
particular the man-optimal $\mu^M$ and woman-optimal $\mu^W$ match exactly the
same individuals.

## Formalized specialization: balanced full-preference markets

The Lean model (`Preferences n` via `MatchingMarket.ofEquivData`) is the
**balanced full-preference** case: $|M| = |W| = n$ and every agent ranks every
agent on the other side (no $\bot$). There the theorem sharpens to:

> **Every stable matching is perfect** — all $n$ men and all $n$ women are
> matched.

So the matched set is all of $\mathrm{Fin}\,n$ in *every* stable matching and
invariance is immediate. This is `GS.stable_matching_perfect`.

### Proof (balanced case)

Suppose a woman $i_0$ is unmatched in a stable $\mu$. If *every* man were
matched, then $\mathrm{matchW} : \text{men} \to \text{women}$ would be a total
injection on the finite equal-size set $\mathrm{Fin}\,n$, hence a bijection,
making $i_0$ some man's partner — contradiction. So some man $j_0$ is also
unmatched. But then $(i_0, j_0)$ blocks $\mu$: each strictly prefers *any*
partner to staying single (since $\bot$ is least-preferred), contradicting
stability. The men side is symmetric, using totality of $\mathrm{matchM}$.

No lattice machinery is needed in the balanced case — the argument is a direct
finiteness-plus-blocking-pair contradiction.

## General case (⊥ and unequal sets)

With unacceptable partners or $|M| \ne |W|$, stable matchings genuinely *can*
leave agents unmatched, and the theorem becomes the non-trivial invariance
statement above. The standard proof routes through the [[lattice]] structure
(WLOG compare $\mu^M$ and $\mu^W$). Formalizing this general version requires
the $\bot$/acceptability extension of the Lean model and is tracked as future
work (#231 item D).

## Why "Rural Hospitals"?

The name comes from the many-to-one (residency matching) version: any hospital
that fills fewer positions than its quota under one stable assignment fills
exactly the same set of positions — with the same residents — under every
stable assignment. Rural hospitals that struggle to fill positions still
struggle; no stable mechanism can rescue them within the stable-matching
framework. The one-to-one statement above is the simplest specialization.

## References

- [MSZ Ch.22, Thm 22.14] Maschler, Solan, Zamir, *Game Theory*.
- McVitie & Wilson (1970), *Stable Marriage Assignment for Unequal Sets*.
- Roth (1986), *On the Allocation of Residents to Rural Hospitals*. Econometrica 54.
- Roth & Sotomayor (1990), Ch. 2 §2.4.
