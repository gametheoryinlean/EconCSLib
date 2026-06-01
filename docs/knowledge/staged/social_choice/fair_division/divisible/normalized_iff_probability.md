---
id: social_choice.fair_division.divisible.normalized_iff_probability
title: Normalized Measure Valuation ↔ Probability Measure
kind: lemma
status: staged
primary_topic: social_choice
topics:
  - social_choice
  - social_choice.fair_division
  - social_choice.fair_division.divisible
uses:
  - social_choice.fair_division.divisible.measure_valuation
lean:
  modules:
    - EconCSLib.SocialChoice.FairDivision.Divisible.Valuation
  declarations:
    - SocialChoice.FairDivision.Divisible.IsNormalized.iff_isProbabilityMeasure
verification:
  statement: accepted
  proof: accepted
  alignment: aligned
tags:
  - fair-division
  - divisible
  - measure
  - probability
---

# Normalized Measure Valuation ↔ Probability Measure

**Lemma.** For a family of measures $\mu : N \to \mathrm{Measure}\ \Omega$,
the induced measure valuation $\mathrm{MeasureValuation}\ \mu$
([[social_choice.fair_division.divisible.measure_valuation]]) is
normalized ([[social_choice.fair_division.divisible.cake_valuation]]) if
and only if every $\mu_i$ is a probability measure:
$$
\mathrm{IsNormalized}\,(\mathrm{MeasureValuation}\ \mu)
\;\iff\;
\forall i \in N,\ \mu_i\text{ is a probability measure.}
$$

In Lean: `IsNormalized.iff_isProbabilityMeasure`.

*Proof.* Unfolding `IsNormalized` and `MeasureValuation`, the predicate
becomes "$\mu_i(\Omega) = 1$ for every $i$", which is exactly the
defining condition of `IsProbabilityMeasure`. The two directions are the
constructor and projection of the one-field `IsProbabilityMeasure` class.
$\square$

This is the bridge between two ways of writing the same hypothesis:
"normalized cake valuation" (the social-choice phrasing) and "probability
measure family" (the measure-theoretic phrasing). Downstream theorems
typically state hypotheses in whichever form is most convenient and use
this lemma to translate.

## References

- [AGT Chapter 13] Nisan, Roughgarden, Tardos, and Vazirani, *Algorithmic Game Theory*. Normalised cake valuations.
