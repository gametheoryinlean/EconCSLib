---
id: social_choice.voting.scf
title: Social Choice Function
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
    - SocialChoice.Voting.VotingRule
    - SocialChoice.Voting.IsTotal
    - SocialChoice.Voting.Resolute
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
tags:
  - social-choice
  - voting
  - aggregation
---

# Social Choice Function

A *social choice function* aggregates a preference profile into the
alternatives that win. In this formalization it is the set-valued *voting
rule*
$$
f : \mathrm{PrefProfile}(N, A) \to \mathcal{P}(A)
$$
returning, for every profile, the (possibly tied) winner set $f(P)$.

In Lean this is `SocialChoice.Voting.VotingRule N A`, the abbreviation
`Profile N A → Finset A`. Two refinements isolate the single-winner case:

- `IsTotal f` — every profile has at least one winner, $f(P) \ne \varnothing$.
- `Resolute f` — every profile has exactly one winner, $\#f(P) = 1$. A
  resolute rule is the set-valued encoding of the classical single-valued SCF
  $G : \mathrm{PrefProfile}(N,A) \to A$ via $f(P) = \{G(P)\}$.

Compared with a social welfare function ([[social_choice.voting.swf]]) the
voting rule returns only the chosen winners rather than a full ranking. The
standard axioms — unanimity ([[social_choice.voting.unanimity]]), monotonicity
([[social_choice.voting.monotonic_scf]]), strategy-proofness
([[social_choice.voting.strategyproof]]), and (non-)dictatorship
([[social_choice.voting.dictatorial_scf]]) — are all stated on the winner set
$f(P)$, with strategy-proofness and dictatorship specializing to the resolute
case.

## References

- [MSZ 21.21] Maschler, Solan, and Zamir, *Game Theory*. Social choice function.
