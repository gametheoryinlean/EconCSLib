---
id: social_choice.voting.dictatorial_scf
title: Dictatorial Social Choice Function
kind: definition
status: formalized
primary_topic: social_choice
topics:
  - social_choice
  - social_choice.voting
uses:
  - social_choice.voting.scf
  - social_choice.strict_preference
lean:
  modules:
    - EconCSLib.SocialChoice.Voting.Basic
  declarations:
    - SocialChoice.Voting.Dictatorial
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
tags:
  - social-choice
  - voting
  - dictator
---

# Dictatorial Social Choice Function

A voting rule $f$ is *dictatorial* if there exists a voter $i \in N$ whose
top-ranked alternative is always the unique winner: for every profile $P$,
$$
\exists i \in N,\ \forall P,\ f(P) = \{\,\mathrm{top}_{P_i}\,\},
$$
where $\mathrm{top}_{P_i}$ is voter $i$'s most-preferred alternative under
$P_i$.

In Lean: `SocialChoice.Voting.Dictatorial`, defined as
`∃ i, ∀ P, f P = {topChoice P i}`.

This is the voting-rule counterpart to dictatorship for social welfare
functions ([[social_choice.voting.dictatorial_swf]]): rather than copying the
dictator's full ranking, the rule returns the dictator's unique top choice as
the sole winner at every profile.

Gibbard–Satterthwaite ([[social_choice.voting.gibbard_satterthwaite]]) shows
that for $|A| \ge 3$ on a finite nonempty voter set, a resolute rule that is
unanimous and strategy-proof ([[social_choice.voting.strategyproof]]) must be
dictatorial in this sense.

## References

- [MSZ 21.23] Maschler, Solan, and Zamir, *Game Theory*. Dictatorial SCF.
