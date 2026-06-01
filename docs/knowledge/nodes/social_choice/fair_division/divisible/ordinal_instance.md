---
id: social_choice.fair_division.divisible.ordinal_instance
title: Divisible Ordinal Instance
kind: definition
status: formalized
primary_topic: social_choice
topics:
  - social_choice
  - social_choice.fair_division
  - social_choice.fair_division.divisible
uses:
  - social_choice.fair_division.share_instance
lean:
  modules:
    - EconCSLib.SocialChoice.FairDivision.Divisible.Instance
  declarations:
    - SocialChoice.FairDivision.Divisible.Instance
    - SocialChoice.FairDivision.Divisible.Instance.toShareInstance
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
tags:
  - fair-division
  - divisible
  - instance
  - ordinal
---

# Divisible Ordinal Instance

A *divisible ordinal instance* is the no-externality share model
specialized to cake-cutting: each agent's preference is an ordinal
preference on cake pieces $\mathrm{Set}\ \Omega$.

In Lean: structure `SocialChoice.FairDivision.Divisible.Instance N Ω`
with a single field `sharePref : N → Pref (Set Ω)`.

Feasibility is fixed at the divisible-allocation level (a measurable
partition of $\Omega$, the predicate
[[social_choice.fair_division.divisible.allocation]]). The instance's
`feasible` member is therefore a definitional alias for `IsAllocation`.

## Bridge to the generic share-instance API

`Divisible.Instance.toShareInstance` views the divisible instance as a
no-externality share instance
([[social_choice.fair_division.share_instance]]) over the share type
$S = \mathrm{Set}\ \Omega$ and resource value $\mathrm{Set.univ}$. This
makes every fair-division solution concept stated against the generic
`ShareInstance` API ([[social_choice.fair_division.solution_concept]])
automatically applicable to divisible instances.

The cardinal-instance and measure-instance specializations
([[social_choice.fair_division.divisible.cardinal_instance]],
[[social_choice.fair_division.divisible.measure_instance]]) feed into
the same bridge — the entire divisible track plugs into the shared
social-choice infrastructure through these wrappers.

## References

- [AGT Chapter 13] Nisan, Roughgarden, Tardos, and Vazirani, *Algorithmic Game Theory*. Cake-cutting instances.
