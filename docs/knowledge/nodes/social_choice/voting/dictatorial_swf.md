---
id: social_choice.voting.dictatorial_swf
title: Dictatorial Social Welfare Function
kind: definition
status: formalized
primary_topic: social_choice
topics:
  - social_choice
  - social_choice.voting
uses:
  - social_choice.voting.swf
  - social_choice.strict_preference
lean:
  modules:
    - EconCSLib.SocialChoice.Voting.Basic
  declarations:
    - SocialChoice.Voting.SWF.Dictatorial
    - SocialChoice.Voting.SWF.NonDictatorial
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
tags:
  - social-choice
  - voting
  - dictator
---

# Dictatorial Social Welfare Function

A social welfare function $F$ is *dictatorial* if there exists a voter
$i \in N$ whose strict preference always determines society's strict
preference:
$$
\exists i \in N,\ \forall P,\ \forall a, b,\
a \succ_{P_i} b \Rightarrow a \succ_{F(P)} b.
$$

A SWF is *non-dictatorial* iff no such voter exists. In Lean these are
`SocialChoice.Voting.SWF.Dictatorial` and
`SocialChoice.Voting.SWF.NonDictatorial`, the latter being the literal
negation of the former.

The dictator only needs to fix the *strict* ranking; under reasonable
auxiliary conditions (e.g. totality of the social order) this forces
agreement on the weak ranking as well.

Arrow's impossibility theorem ([[social_choice.voting.arrow_impossibility]])
states that, with at least three alternatives, the conjunction of unanimity
([[social_choice.voting.unanimity]]) and IIA ([[social_choice.voting.iia]])
forces $F$ to be dictatorial in this sense.

## References

- [MSZ 21.7, 21.11] Maschler, Solan, and Zamir, *Game Theory*. Dictatorial SWF and non-dictatorship.
