---
id: social_choice.voting.arrow_impossibility
title: Arrow's Impossibility Theorem
kind: theorem
status: staged
primary_topic: social_choice
topics:
  - social_choice
  - social_choice.voting
  - social_choice.voting.arrow
uses:
  - social_choice.voting.arrow_of_unanimity_iia
lean:
  modules:
    - EconCSLib.SocialChoice.Voting.Arrow
  declarations:
    - SocialChoice.Voting.arrow_impossibility
verification:
  statement: accepted
  proof: accepted
  alignment: aligned
tags:
  - social-choice
  - voting
  - arrow
  - impossibility
---

# Arrow's Impossibility Theorem

**Theorem (Arrow 1951).** Let $N$ be a finite nonempty population and $A$ a
finite alternative set with $|A| \ge 3$. Every social welfare function
$F$ ([[social_choice.voting.swf]]) satisfying

- unanimity ([[social_choice.voting.unanimity]]) and
- independence of irrelevant alternatives ([[social_choice.voting.iia]])

is dictatorial ([[social_choice.voting.dictatorial_swf]]).

In Lean: `SocialChoice.Voting.arrow_impossibility`, with signature
`[Fintype A] [Fintype N] [Nonempty N] (hA : Fintype.card A ≥ 3)`.

## Proof

The public theorem packages the cardinality hypothesis: a finite alternative
set with at least three elements contains three distinct alternatives
$x, y, z$ (via `Fintype.equivFin`), which is the witness shape consumed by
the decisive-coalitions form
[[social_choice.voting.arrow_of_unanimity_iia]]. Apply that theorem to
conclude. $\square$

## Interpretation

If one insists on aggregating individual rankings into a single social
ranking that (i) respects unanimity and (ii) does not let society's
$\{a,b\}$ ranking depend on irrelevant alternatives, then the *only*
admissible rules with three or more alternatives are dictatorships — one
agent fully determines society's strict preference. Three classical escapes
are: weaken to a social choice function (Gibbard–Satterthwaite is the SCF
analogue, [[social_choice.voting.gibbard_satterthwaite]]); restrict the
preference domain (e.g. single-peaked); or move from ordinal to cardinal /
probabilistic aggregation.

## References

- [MSZ 21.10] Maschler, Solan, and Zamir, *Game Theory*. Arrow's impossibility theorem.
- Arrow, K. J. (1951). *Social Choice and Individual Values*.
