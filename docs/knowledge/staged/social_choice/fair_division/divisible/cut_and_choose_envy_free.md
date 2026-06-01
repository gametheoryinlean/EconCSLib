---
id: social_choice.fair_division.divisible.cut_and_choose_envy_free
title: Cut-and-Choose Is Envy-Free at a Fair Cut
kind: theorem
status: staged
primary_topic: social_choice
topics:
  - social_choice
  - social_choice.fair_division
  - social_choice.fair_division.divisible
  - social_choice.fair_division.divisible.cut_and_choose
uses:
  - social_choice.fair_division.divisible.chooser_envy_free
  - social_choice.fair_division.divisible.cutter_envy_free_of_fair
lean:
  modules:
    - EconCSLib.SocialChoice.FairDivision.Divisible.CutAndChoose
  declarations:
    - SocialChoice.FairDivision.Divisible.cutAndChoose_isEnvyFree
verification:
  statement: accepted
  proof: accepted
  alignment: aligned
tags:
  - fair-division
  - divisible
  - cut-and-choose
  - envy-free
---

# Cut-and-Choose Is Envy-Free at a Fair Cut

**Theorem.** For a two-agent measure family $\mu : \mathrm{Fin}\ 2 \to
\mathrm{Measure}\ I$ and a *fair* cut point $t$ for the cutter, the
cut-and-choose allocation is envy-free.

In Lean: `cutAndChoose_isEnvyFree`.

## Proof

Combine the two half-results:

- The chooser never envies the cutter at *any* cut
  ([[social_choice.fair_division.divisible.chooser_envy_free]]).
- The cutter does not envy the chooser *at a fair cut*
  ([[social_choice.fair_division.divisible.cutter_envy_free_of_fair]]).

Together these cover both directions of the envy-freeness condition
$\forall i, j,\ \mu_i(A_j) \le \mu_i(A_i)$ for the two agents.

## Existence corollary

Because fair cut points always exist for finite non-atomic cutter measures
([[social_choice.fair_division.divisible.fair_cut_exists]]), cut-and-choose
gives a constructive existence proof for EF allocations on two agents
([[social_choice.fair_division.divisible.cut_and_choose_ef_exists]]).

## References

- Steinhaus, H. (1948). "The Problem of Fair Division". *Econometrica*.
- Robertson, J. M. and Webb, W. A. (1998). *Cake-Cutting Algorithms*, Ch. 1.
- [AGT Chapter 13] Nisan, Roughgarden, Tardos, and Vazirani, *Algorithmic Game Theory*.
