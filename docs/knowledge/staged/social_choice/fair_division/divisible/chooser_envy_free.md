---
id: social_choice.fair_division.divisible.chooser_envy_free
title: Chooser Is Always Envy-Free
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
    - SocialChoice.FairDivision.Divisible.chooser_isEnvyFree
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

# Chooser Is Always Envy-Free

**Theorem.** For any cut point $t \in I$ and any two-agent measure family
$\mu : \mathrm{Fin}\ 2 \to \mathrm{Measure}\ I$, the chooser (agent 1) in
the cut-and-choose allocation
([[social_choice.fair_division.divisible.cut_and_choose_alloc]]) does not
envy the cutter:
$$
\mu_1\bigl(A_{\mathrm{cutter}}\bigr) \;\le\; \mu_1\bigl(A_{\mathrm{chooser}}\bigr).
$$

In Lean: `chooser_isEnvyFree`. The statement *does not depend* on the cut
being fair — the chooser's guarantee holds for **every** cut.

## Proof

By construction of the protocol, the chooser receives whichever of the two
sides $L = [0, t]$ and $R = (t, 1]$ they value at least as much (with the
tie broken to the left). Concretely:

- If $\mu_1(L) \ge \mu_1(R)$ the chooser takes $L$ and the cutter is left
  with $R$, giving $\mu_1(R) \le \mu_1(L)$.
- Otherwise the chooser takes $R$ and the cutter takes $L$, giving
  $\mu_1(L) < \mu_1(R) \le \mu_1(R)$.

In both branches the chooser's value for their own piece weakly dominates
their value for the cutter's piece, which is the envy-freeness statement.

## Significance

The chooser is structurally protected: they get the optimal choice between
the two halves by construction. The interesting half of cut-and-choose is
that the *cutter* can also be made envy-free
([[social_choice.fair_division.divisible.cutter_envy_free_of_fair]]) by
cutting at the right point — namely a fair cut.

## References

- Steinhaus, H. (1948). "The Problem of Fair Division". *Econometrica*.
- Robertson, J. M. and Webb, W. A. (1998). *Cake-Cutting Algorithms*, Ch. 1.
