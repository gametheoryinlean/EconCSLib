---
id: social_choice.fair_division.divisible.cut_and_choose_ef_exists
title: Two-Agent EF Existence via Cut-and-Choose
kind: theorem
status: staged
primary_topic: social_choice
topics:
  - social_choice
  - social_choice.fair_division
  - social_choice.fair_division.divisible
  - social_choice.fair_division.divisible.cut_and_choose
uses:
  - social_choice.fair_division.divisible.cut_and_choose_envy_free
  - social_choice.fair_division.divisible.fair_cut_exists
lean:
  modules:
    - EconCSLib.SocialChoice.FairDivision.Divisible.CutAndChoose
    - EconCSLib.SocialChoice.FairDivision.Divisible.EnvyFree
  declarations:
    - SocialChoice.FairDivision.Divisible.cutAndChoose_ef_exists
    - SocialChoice.FairDivision.Divisible.ef_exists_two_agents
verification:
  statement: accepted
  proof: accepted
  alignment: aligned
tags:
  - fair-division
  - divisible
  - cut-and-choose
  - envy-free
  - existence
---

# Two-Agent EF Existence via Cut-and-Choose

**Theorem.** For two agents with measures $\mu_0, \mu_1$ on the unit
interval $I = [0, 1]$ where $\mu_0, \mu_1$ are finite and $\mu_0$ is
non-atomic, there exists a complete measurable partition of $I$ that is
envy-free under the measure valuation
$\mathrm{MeasureValuation}\ \mu$
([[social_choice.fair_division.divisible.envy_free]]).

Formally:
$$
\exists A : \mathrm{Allocation}\ (\mathrm{Fin}\ 2)\ I,\;
\mathrm{IsAllocation}\ A \;\wedge\;
\mathrm{IsEnvyFree}\ (\mathrm{MeasureValuation}\ \mu)\ A.
$$

In Lean this appears as two equivalent statements: `cutAndChoose_ef_exists`
(in `CutAndChoose.lean`) and the alias `ef_exists_two_agents` (in
`EnvyFree.lean`).

## Proof

Constructively: pick a fair cut point $t$ via
[[social_choice.fair_division.divisible.fair_cut_exists]], use it in the
cut-and-choose protocol to produce
$A = \mathrm{cutAndChooseAlloc}\ \mu\ t$, and verify EF via
[[social_choice.fair_division.divisible.cut_and_choose_envy_free]].

The result is a *contiguous* EF allocation — each agent receives a single
interval, not a fragmented set. This stronger conclusion sets the stage
for Stromquist's $n$-agent generalization
([[social_choice.fair_division.divisible.ef_exists]]), which also
produces contiguous EF allocations.

## References

- Steinhaus, H. (1948). "The Problem of Fair Division". *Econometrica*.
- Robertson, J. M. and Webb, W. A. (1998). *Cake-Cutting Algorithms*, Ch. 1.
- [AGT Chapter 13] Nisan, Roughgarden, Tardos, and Vazirani, *Algorithmic Game Theory*.
