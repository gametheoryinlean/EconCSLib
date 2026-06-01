---
id: social_choice.fair_division.divisible.envy_free
title: Divisible Envy-Free, Proportional, Equitable Predicates
kind: definition
status: formalized
primary_topic: social_choice
topics:
  - social_choice
  - social_choice.fair_division
  - social_choice.fair_division.divisible
uses:
  - social_choice.fair_division.divisible.allocation
  - social_choice.fair_division.divisible.cake_valuation
lean:
  modules:
    - EconCSLib.SocialChoice.FairDivision.Divisible.Basic
  declarations:
    - SocialChoice.FairDivision.Divisible.IsEnvyFree
    - SocialChoice.FairDivision.Divisible.IsProportional
    - SocialChoice.FairDivision.Divisible.IsEquitable
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
tags:
  - fair-division
  - divisible
  - envy-free
  - proportional
  - equitable
---

# Divisible Envy-Free, Proportional, Equitable Predicates

Three fairness predicates specialised to divisible allocations
([[social_choice.fair_division.divisible.allocation]]) under a cake
valuation $\mathrm{cv}$ ([[social_choice.fair_division.divisible.cake_valuation]]).

## Envy-Free (EF)

$$
\forall i, j \in N,\ \mathrm{cv}(i, A(j)) \le \mathrm{cv}(i, A(i)).
$$

In Lean: `Divisible.IsEnvyFree`. Requires only `[Preorder V]` on the value
type.

For divisible goods with non-atomic measures, EF allocations always exist
(Stromquist; [[social_choice.fair_division.divisible.ef_exists]]). This is
the central difference from the indivisible setting
([[social_choice.fair_division.indivisible.envy_free]]), where EF may fail
to exist.

## Proportional (PROP)

For a population size parameter $n$,
$$
\forall i \in N,\ \mathrm{cv}(i, \Omega) \le n \cdot \mathrm{cv}(i, A(i)).
$$

Stated without division so it makes sense over any `[Semiring V]`. In
Lean: `Divisible.IsProportional`.

## Equitable

Every agent assigns the same value to their own piece:
$$
\forall i, j \in N,\ \mathrm{cv}(i, A(i)) = \mathrm{cv}(j, A(j)).
$$

In Lean: `Divisible.IsEquitable`. Comparable across agents only with
normalized cake valuations
([[social_choice.fair_division.divisible.normalized_iff_probability]]).

These three are exactly the generic
([[social_choice.fair_division.envy_free]],
[[social_choice.fair_division.proportional]],
[[social_choice.fair_division.equitable]]) predicates re-stated with
$\mathrm{cv}.val$ in place of an opaque utility function, so the shape
matches downstream measure-theoretic proofs.

## References

- [AGT Chapter 13] Nisan, Roughgarden, Tardos, and Vazirani, *Algorithmic Game Theory*. Fairness for cake cutting.
- Procaccia, A. D. (2013). "Cake Cutting: Not Just Child's Play".
- Robertson, J. M. and Webb, W. A. (1998). *Cake-Cutting Algorithms*.
