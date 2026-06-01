---
id: social_choice.fair_division.share_instance
title: Share Instance (No-Externality Model)
kind: definition
status: formalized
primary_topic: social_choice
topics:
  - social_choice
  - social_choice.fair_division
  - social_choice.fair_division.core
uses:
  - social_choice.fair_division.instance
lean:
  modules:
    - EconCSLib.SocialChoice.FairDivision.Basic
  declarations:
    - SocialChoice.FairDivision.ShareInstance
    - SocialChoice.FairDivision.ShareInstance.toInstance
verification:
  definition: accepted
  proof: accepted
  alignment: aligned
tags:
  - fair-division
  - instance
  - no-externality
---

# Share Instance (No-Externality Model)

A *share instance* is a fair-division instance restricted to the
*no-externality* model: each agent ranks only the share they personally
receive, not the entire allocation.

In Lean: `SocialChoice.FairDivision.ShareInstance N R S`, with fields
`resource : R`, `feasible : Allocation N S → Prop`, and
`sharePref : N → Pref S`.

This is the standard input shape for textbook fair-division problems
(envy-freeness, proportionality, MMS, etc., all formulated in terms of
each agent's own share).

## Lift to the full-allocation interface

There is a canonical embedding
`toInstance : ShareInstance N R S → Instance N R S`
([[social_choice.fair_division.instance]]) that promotes share preferences
to allocation preferences by comparing two allocations only through the
evaluating agent's own share:
$$
A \preceq_i B \iff A(i) \preceq_{\mathrm{share},i} B(i).
$$

The promoted relation inherits reflexivity, transitivity, and totality
pointwise from `sharePref i`, so the result is a valid `Pref` on
allocations.

This lift is the bridge that makes the share-instance API a true special
case of the generic allocation-preference instance, and lets the same
solution concepts apply at both layers.

## References

- [AGT Chapter 11] Nisan, Roughgarden, Tardos, and Vazirani, *Algorithmic Game Theory*. No-externality fair-division model.
