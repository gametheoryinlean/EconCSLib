---
id: social_choice.fair_division.divisible.no_atoms_map_subtype
title: Non-Atomicity Is Preserved by Subtype.val Pushforward
kind: lemma
status: staged
primary_topic: social_choice
topics:
  - social_choice
  - social_choice.fair_division
  - social_choice.fair_division.divisible
uses: []
lean:
  modules:
    - EconCSLib.SocialChoice.FairDivision.Divisible.UnitInterval
  declarations:
    - SocialChoice.FairDivision.Divisible.noAtomsMapSubtypeVal
verification:
  statement: accepted
  proof: accepted
  alignment: aligned
tags:
  - fair-division
  - divisible
  - measure
  - cake-cutting
---

# Non-Atomicity Is Preserved by Subtype.val Pushforward

**Instance.** Let $\mu$ be a measure on the unit interval $I = [0, 1]$
(viewed as a subtype of $\mathbb{R}$) with no atoms (`[NoAtoms μ]`). Then
the pushforward $\mu.map\ \mathrm{Subtype.val}$ on $\mathbb{R}$ also has
no atoms.

In Lean: `SocialChoice.FairDivision.Divisible.noAtomsMapSubtypeVal` —
provided as an `instance` so that downstream lemmas requiring
`[NoAtoms (μ.map Subtype.val)]` resolve automatically.

## Proof

A single point $\{x\} \subseteq \mathbb{R}$ has pushforward measure
$\mu(\mathrm{Subtype.val}^{-1}(\{x\}))$. The preimage is either empty (if
$x \notin I$) or a singleton in $I$; in both cases it is a subsingleton.
Subsingletons have measure $0$ by `Set.Subsingleton.measure_zero`. Thus
every singleton in $\mathbb{R}$ has zero pushforward measure, which is
the definition of `NoAtoms`.

## Where this is used

The cake-cutting machinery often models the cake as $I = [0, 1]$ but
states IVT lemmas at the $\mathbb{R}$ level
([[social_choice.fair_division.divisible.cdf_continuous]],
[[social_choice.fair_division.divisible.cut_exists]]). This instance is
the bridge that lets `cut_exists` invoke `cdfRealContinuous` on
$\mu.map\ \mathrm{Subtype.val}$ without manually carrying the
`NoAtoms` hypothesis through every call site.

## References

- Folland, G. B. (1999). *Real Analysis*, §1.5. Pushforward and atomicity.
