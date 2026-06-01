---
id: social_choice.voting.is_decisive
title: Decisive Coalition and Dictator
kind: definition
status: formalized
primary_topic: social_choice
topics:
  - social_choice
  - social_choice.voting
  - social_choice.voting.arrow
uses:
  - social_choice.voting.is_decisive_for
lean:
  modules:
    - EconCSLib.SocialChoice.Voting.Decisive
  declarations:
    - SocialChoice.Voting.IsDecisive
    - SocialChoice.Voting.SWF.IsDictator
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
tags:
  - social-choice
  - voting
  - decisive-coalition
  - dictator
  - arrow
---

# Decisive Coalition and Dictator

A coalition $C \subseteq N$ is *decisive* for a social welfare function $F$
([[social_choice.voting.swf]]) if it is decisive for every ordered pair of
alternatives:
$$
\forall a, b \in A,\ \mathrm{IsDecisiveFor}(F, C, a, b).
$$

An individual $i \in N$ is a *dictator* exactly when their singleton coalition
$\{i\}$ is decisive in this sense.

In Lean: `SocialChoice.Voting.IsDecisive F C` and the singleton specialization
`SocialChoice.Voting.SWF.IsDictator F i := IsDecisive F {i}`.

This identification is the structural heart of the decisive-coalition proof
of Arrow ([[social_choice.voting.arrow_of_unanimity_iia]]): the dictatorship
conclusion ([[social_choice.voting.dictatorial_swf]]) reduces to producing a
singleton decisive coalition.

## References

- [MSZ 21.15] Maschler, Solan, and Zamir, *Game Theory*. Decisive coalitions and the singleton dictator.
