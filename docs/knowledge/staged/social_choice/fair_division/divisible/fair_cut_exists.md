---
id: social_choice.fair_division.divisible.fair_cut_exists
title: Fair Cut Point Exists
kind: theorem
status: staged
primary_topic: social_choice
topics:
  - social_choice
  - social_choice.fair_division
  - social_choice.fair_division.divisible
  - social_choice.fair_division.divisible.cut_and_choose
uses:
  - social_choice.fair_division.divisible.cut_and_choose_alloc
  - social_choice.fair_division.divisible.cut_exists
lean:
  modules:
    - EconCSLib.SocialChoice.FairDivision.Divisible.CutAndChoose
  declarations:
    - SocialChoice.FairDivision.Divisible.fairCutPoint_exists
verification:
  statement: accepted
  proof: accepted
  alignment: aligned
tags:
  - fair-division
  - divisible
  - cut-and-choose
  - existence
---

# Fair Cut Point Exists

**Theorem.** For a finite non-atomic cutter measure $\mu_0$ on the unit
interval $I = [0, 1]$, there exists a cut point $t \in I$ that is fair
for the cutter
([[social_choice.fair_division.divisible.cut_and_choose_alloc]]):
$$
\mu_0([0, t]) = \mu_0((t, 1]).
$$

In Lean: `fairCutPoint_exists`. Hypotheses: `[IsFiniteMeasure μ_0]` and
`[NoAtoms μ_0]`.

## Proof

This is an immediate specialization of the unit-interval IVT lemma
[[social_choice.fair_division.divisible.cut_exists]] at the target value
$c = \mu_0(I)/2$ (in the real-valued / `toReal` form). The IVT yields a
$t \in I$ with $\mu_0([0, t]) = c$; the complement satisfies $\mu_0((t, 1])
= \mu_0(I) - c = c$.

## Significance

This is the *existence-of-cuts* half of cut-and-choose. Combined with the
guarantee that a fair cut makes the cutter envy-free
([[social_choice.fair_division.divisible.cutter_envy_free_of_fair]]) and
the chooser is envy-free at every cut
([[social_choice.fair_division.divisible.chooser_envy_free]]), it
constructively closes the EF-existence theorem for two agents on
non-atomic measures
([[social_choice.fair_division.divisible.cut_and_choose_ef_exists]]).

## References

- Steinhaus, H. (1948). "The Problem of Fair Division". *Econometrica*.
- Robertson, J. M. and Webb, W. A. (1998). *Cake-Cutting Algorithms*, Ch. 1.
