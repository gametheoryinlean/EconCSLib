---
id: social_choice.fair_division.divisible.cut_and_choose_alloc
title: Cut-and-Choose Allocation and Fair Cut Point
kind: definition
status: formalized
primary_topic: social_choice
topics:
  - social_choice
  - social_choice.fair_division
  - social_choice.fair_division.divisible
  - social_choice.fair_division.divisible.cut_and_choose
uses:
  - social_choice.fair_division.divisible.allocation
lean:
  modules:
    - EconCSLib.SocialChoice.FairDivision.Divisible.CutAndChoose
  declarations:
    - SocialChoice.FairDivision.Divisible.cutAndChooseAlloc
    - SocialChoice.FairDivision.Divisible.IsFairCutPoint
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
tags:
  - fair-division
  - divisible
  - cut-and-choose
  - cake-cutting
---

# Cut-and-Choose Allocation and Fair Cut Point

The cut-and-choose protocol on $I = [0, 1]$ with two agents
$\{0, 1\} \subseteq \mathrm{Fin}\ 2$ is parameterised by a cut point
$t \in I$. The output is the function `cutAndChooseAlloc μ t : Allocation
(Fin 2) I` defined by:

- Compute the left and right pieces $L = [0, t]$ and $R = (t, 1]$.
- The chooser (agent $1$) takes whichever side they prefer:
  - if $\mu_1(L) \ge \mu_1(R)$, the chooser takes $L$, the cutter takes $R$;
  - otherwise the chooser takes $R$, the cutter takes $L$.

In Lean: `cutAndChooseAlloc μ t`. The `@[simp]` lemmas
`cutAndChooseAlloc_zero` and `cutAndChooseAlloc_one` unfold the assignment
for the cutter (agent 0) and the chooser (agent 1) respectively.

## Fair cut point

The cut point $t$ is *fair for the cutter* if agent 0's measure splits the
cake into two equal halves:
$$
\mu_0([0, t]) = \mu_0((t, 1]).
$$

In Lean: `IsFairCutPoint μ t`.

A fair cut point always exists for finite non-atomic $\mu_0$ — this is the
shared unit-interval IVT lemma
([[social_choice.fair_division.divisible.cut_exists]]) specialised at
$c = \mu_0(I)/2$, giving
[[social_choice.fair_division.divisible.fair_cut_exists]].

## References

- Steinhaus, H. (1948). "The Problem of Fair Division". *Econometrica*.
- Robertson, J. M. and Webb, W. A. (1998). *Cake-Cutting Algorithms*, Ch. 1.
- [AGT Chapter 13] Nisan, Roughgarden, Tardos, and Vazirani, *Algorithmic Game Theory*.
