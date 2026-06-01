---
id: social_choice.fair_division.divisible.ef_implies_proportional
title: EF ⇒ Proportional (Measure Valuations)
kind: theorem
status: staged
primary_topic: social_choice
topics:
  - social_choice
  - social_choice.fair_division
  - social_choice.fair_division.divisible
uses:
  - social_choice.fair_division.divisible.envy_free
  - social_choice.fair_division.divisible.measure_valuation
lean:
  modules:
    - EconCSLib.SocialChoice.FairDivision.Divisible.Basic
  declarations:
    - SocialChoice.FairDivision.Divisible.IsEnvyFree.isProportional
verification:
  statement: accepted
  proof: accepted
  alignment: aligned
tags:
  - fair-division
  - divisible
  - envy-free
  - proportional
---

# EF ⇒ Proportional (Measure Valuations)

**Theorem.** Let $\mu : N \to \mathrm{Measure}\ \Omega$ on a measurable
cake $\Omega$ and a finite agent type $N$, and let $A$ be an envy-free
complete divisible allocation under the measure valuation
$\mathrm{MeasureValuation}\ \mu$
([[social_choice.fair_division.divisible.measure_valuation]],
[[social_choice.fair_division.divisible.envy_free]],
[[social_choice.fair_division.divisible.allocation]]). Then $A$ is
proportional with respect to $|N|$.

That is, for every agent $i$,
$$
\mu_i(\Omega) \;\le\; |N| \cdot \mu_i(A(i)).
$$

In Lean: `SocialChoice.FairDivision.Divisible.IsEnvyFree.isProportional`.

## Proof

Use the partition / additivity properties of the measure valuation. For
each agent $i$:

$$
\begin{aligned}
\mu_i(\Omega)
  &= \mu_i\bigl(\bigcup_j A(j)\bigr) && \text{cover of $A$} \\
  &= \sum_{j} \mu_i(A(j)) && \text{disjoint, measurable pieces} \\
  &\le \sum_{j} \mu_i(A(i)) && \text{envy-freeness: $\mu_i(A_j) \le \mu_i(A_i)$} \\
  &= |N| \cdot \mu_i(A(i)). && \text{constant sum}
\end{aligned}
$$

The countable-additivity step uses `MeasureTheory.measure_iUnion` on the
disjoint measurable family $A : N \to \mathrm{Set}\ \Omega$; for a finite
agent type this collapses to a `Finset` sum via `tsum_fintype`.

## Interpretation

Envy-freeness is a *strictly stronger* fairness notion than
proportionality for divisible goods. The theorem above is the precise
form: an EF measure-valued allocation automatically guarantees every
agent at least their $1/n$ share of the whole.

The same statement at the bundled `MeasureInstance` level — including the
real-valued (`toReal`) variant — appears in
[[social_choice.fair_division.divisible.measure_instance_existence]].

## References

- [AGT Chapter 13] Nisan, Roughgarden, Tardos, and Vazirani, *Algorithmic Game Theory*. EF implies proportional for divisible goods.
