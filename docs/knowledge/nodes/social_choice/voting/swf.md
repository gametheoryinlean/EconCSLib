---
id: social_choice.voting.swf
title: Social Welfare Function
kind: definition
status: formalized
primary_topic: social_choice
topics:
  - social_choice
  - social_choice.voting
uses:
  - social_choice.preference_profile
lean:
  modules:
    - EconCSLib.SocialChoice.Voting.Basic
  declarations:
    - SocialChoice.Voting.SWF
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
tags:
  - social-choice
  - voting
  - aggregation
---

# Social Welfare Function

A *social welfare function* (SWF) on a population $N$ and alternative set
$A$ is a map
$$
F : \mathrm{PrefProfile}(N, A) \to \mathrm{Pref}(A)
$$
that aggregates a profile of individual preferences into a single bundled
social preference on $A$.

In Lean this is the structure `SocialChoice.Voting.SWF N A` with one field
`f : PrefProfile N A → Pref A`. A `CoeFun` instance lets us write `F P`
for the aggregated society-wide preference at profile $P$.

The SWF output is itself a `Pref A`, so the standard axioms — unanimity
([[social_choice.voting.unanimity]]), independence of irrelevant alternatives
([[social_choice.voting.iia]]), and (non-)dictatorship
([[social_choice.voting.dictatorial_swf]]) — apply to the strict and weak
relations derived from $F(P)$.

## References

- [MSZ 21.5] Maschler, Solan, and Zamir, *Game Theory*. Social welfare function.
- Arrow, K. J. (1951). *Social Choice and Individual Values*. Original SWF definition.
