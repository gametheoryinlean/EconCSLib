---
id: social_choice.fair_division.indivisible.efx
title: EFX — Envy-Free Up to Any Good
kind: definition
status: formalized
primary_topic: social_choice
topics:
  - social_choice
  - social_choice.fair_division
  - social_choice.fair_division.indivisible
uses:
  - social_choice.fair_division.indivisible.envy_free
lean:
  modules:
    - EconCSLib.SocialChoice.FairDivision.Indivisible.Fairness
  declarations:
    - SocialChoice.FairDivision.Indivisible.IsEFX
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
tags:
  - fair-division
  - indivisible
  - efx
  - fairness
---

# EFX — Envy-Free Up to Any Good

An allocation $A$ is *envy-free up to any good* (EFX) if, for every
envied bundle $A(j)$ from agent $i$'s perspective, removing **any**
single item eliminates the envy:
$$
\forall i \ne j,\ \forall g \in A(j),\ v_i(A(j) \setminus \{g\}) \le v_i(A(i)).
$$

In Lean: `SocialChoice.FairDivision.Indivisible.IsEFX`. Requires
`[DecidableEq G]` for the `Finset` difference.

## Strength

EFX is *strictly stronger* than EF1
([[social_choice.fair_division.indivisible.ef1]]): EFX demands the
"removing one item eliminates envy" property for **every** witness, EF1
for **some**. The implication EFX ⇒ EF1
([[social_choice.fair_division.indivisible.implications]]) is
unconditional.

## Existence

EFX existence is partially open:

- *2 agents.* EFX always exists, by a small explicit construction
  ([[social_choice.fair_division.indivisible.efx_exists_two_agents]]).
- *3 agents.* Chaudhury–Garg–Mehlhorn (EC 2020) prove existence for
  any 3-agent additive valuation; this proof is *not yet formalised*
  in EconCSLib (`SocialChoice/FairDivision/Indivisible/EFX.lean` only
  covers the 2-agent case in the library).
- *$n \ge 4$ agents.* **Open problem in fair division.** Existence is
  not known and is the most prominent open question in algorithmic
  fair division.

## Implications

- *EF + monotone valuation* ⇒ EFX
  ([[social_choice.fair_division.indivisible.implications]]):
  removing an item from $A(j)$ only decreases its value, so the EF
  inequality $v_i(A(j)) \le v_i(A(i))$ propagates to subsets.
  Additive valuations with nonnegative weights are monotone, so
  EF-on-additive directly gives EFX.

## References

- [AGT Chapter 11] Nisan, Roughgarden, Tardos, and Vazirani, *Algorithmic Game Theory*. EFX.
- Caragiannis, Kurokawa, Moulin, Procaccia, Shah, and Wang (2019). "The Unreasonable Fairness of Maximum Nash Welfare". *EC* 2016 / *ACM TEAC* 2019.
- Chaudhury, B. R., Garg, J., and Mehlhorn, K. (2020). "EFX Allocations for Three Agents". *EC*. arXiv:2005.06878.
