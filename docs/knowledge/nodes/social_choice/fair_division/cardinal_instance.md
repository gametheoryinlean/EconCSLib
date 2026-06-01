---
id: social_choice.fair_division.cardinal_instance
title: Cardinal Fair-Division Instance
kind: definition
status: formalized
primary_topic: social_choice
topics:
  - social_choice
  - social_choice.fair_division
  - social_choice.fair_division.core
uses:
  - social_choice.fair_division.share_instance
lean:
  modules:
    - EconCSLib.SocialChoice.FairDivision.Cardinal
  declarations:
    - SocialChoice.FairDivision.CardinalInstance
    - SocialChoice.FairDivision.CardinalInstance.inducedSharePref
    - SocialChoice.FairDivision.CardinalInstance.toShareInstance
verification:
  definition: accepted
  proof: accepted
  alignment: aligned
tags:
  - fair-division
  - instance
  - cardinal
---

# Cardinal Fair-Division Instance

A *cardinal fair-division instance* is the standard real-valued
no-externality model: each agent assigns a real *utility* to every
candidate share.

In Lean: `SocialChoice.FairDivision.CardinalInstance N R S` with fields
`resource : R`, `feasible : Allocation N S → Prop`, and
`utility : N → S → ℝ`.

## Induced share preference

The natural ordinal preference associated with $u_i$ ranks shares by
utility — *higher utility is weakly preferred*:
$$
s \preceq_i t \iff u_i(s) \le u_i(t).
$$

In Lean: `CardinalInstance.inducedSharePref` — bundled as a `Pref S` whose
reflexivity, transitivity, and totality come from the linear order on
$\mathbb{R}$.

## Bridge to the ordinal share instance

`CardinalInstance.toShareInstance` lifts the cardinal data into a
no-externality share instance ([[social_choice.fair_division.share_instance]])
whose share preference is `inducedSharePref`. This is the canonical way to
view a real-valued utility problem inside the ordinal share-instance API.

The compatibility condition between an *external* ordinal share instance
$I_1$ and a cardinal instance $I_2$ is captured by
`UtilityRepresentsSharePref`:
$$
I_1.\mathrm{sharePref}(i)\ s\ t \iff I_2.\mathrm{utility}(i)\ t \le I_2.\mathrm{utility}(i)\ s,
$$
asserting that $I_2$'s utility represents $I_1$'s ordinal preference.

## References

- [AGT Chapter 11] Nisan, Roughgarden, Tardos, and Vazirani, *Algorithmic Game Theory*. Cardinal valuation in fair division.
