---
id: social_choice.fair_division.divisible.cutter_envy_free_of_fair
title: Cutter Does Not Envy at a Fair Cut
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
  - social_choice.fair_division.divisible.envy_free
lean:
  modules:
    - EconCSLib.SocialChoice.FairDivision.Divisible.CutAndChoose
  declarations:
    - SocialChoice.FairDivision.Divisible.cutter_isEnvyFree_of_fair
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

# Cutter Does Not Envy at a Fair Cut

**Theorem.** If the cut point $t \in I$ is *fair* for the cutter
([[social_choice.fair_division.divisible.cut_and_choose_alloc]]) — i.e.
$\mu_0([0, t]) = \mu_0((t, 1])$ — then in the cut-and-choose allocation,
the cutter (agent 0) does not envy the chooser:
$$
\mu_0\bigl(A_{\mathrm{chooser}}\bigr) \;\le\; \mu_0\bigl(A_{\mathrm{cutter}}\bigr).
$$

In Lean: `cutter_isEnvyFree_of_fair`.

## Proof

Both pieces have equal cutter-measure by the fair-cut hypothesis:
$\mu_0([0,t]) = \mu_0((t,1])$. Whichever side the chooser takes leaves the
cutter with a piece of the *same* cutter-value as the one taken. So
$\mu_0(A_{\mathrm{cutter}}) = \mu_0(A_{\mathrm{chooser}})$, hence the
no-envy inequality is in fact an equality.

## Significance

This complements the chooser's structural guarantee
([[social_choice.fair_division.divisible.chooser_envy_free]]): when the
cutter cuts at a fair point, the *cutter* becomes indifferent between the
two halves and therefore cannot envy. Combining the two gives full
envy-freeness ([[social_choice.fair_division.divisible.cut_and_choose_envy_free]]).

Fair cut points always exist for finite non-atomic cutter measures
([[social_choice.fair_division.divisible.fair_cut_exists]]), so cut-and-
choose with a fair cut is a constructive EF-existence procedure for two
agents.

## References

- Steinhaus, H. (1948). "The Problem of Fair Division". *Econometrica*.
- Robertson, J. M. and Webb, W. A. (1998). *Cake-Cutting Algorithms*, Ch. 1.
