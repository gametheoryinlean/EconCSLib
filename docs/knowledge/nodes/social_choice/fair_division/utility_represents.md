---
id: social_choice.fair_division.utility_represents
title: Utility Represents Share Preference
kind: definition
status: formalized
primary_topic: social_choice
topics:
  - social_choice
  - social_choice.fair_division
  - social_choice.fair_division.core
uses:
  - social_choice.fair_division.cardinal_instance
lean:
  modules:
    - EconCSLib.SocialChoice.FairDivision.Cardinal
  declarations:
    - SocialChoice.FairDivision.CardinalInstance.UtilityRepresentsSharePref
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
tags:
  - fair-division
  - utility
  - representation
---

# Utility Represents Share Preference

Let $I_1$ be a no-externality share instance
([[social_choice.fair_division.share_instance]]) and $I_2$ a cardinal
instance ([[social_choice.fair_division.cardinal_instance]]) on the same
population $N$ and share type $S$. We say $I_2$'s utility *represents*
$I_1$'s share preference if for every agent $i$ and every pair of
shares $s, t$,
$$
I_1.\mathrm{sharePref}(i)\,s\,t \iff I_2.\mathrm{utility}(i)\,t \le I_2.\mathrm{utility}(i)\,s.
$$

In Lean: `SocialChoice.FairDivision.CardinalInstance.UtilityRepresentsSharePref`.

This is the bridging predicate that lets a cardinal instance *play the
role of* an ordinal share instance: whenever the predicate holds, theorems
stated against $I_1$'s ordinal preferences automatically apply with $I_2$'s
utilities.

Two design notes:

- The direction of the inequality reflects "higher utility is weakly
  preferred"; the LHS uses the bundled weak preference $\preceq$ in the
  $s \preceq_i t$ convention.
- The predicate does not require the utility to be *unique* — many cardinal
  instances can represent the same ordinal share instance, differing by
  monotone transformations.

The canonical *induced* cardinal instance for a given share instance
($I_2 = I_1.\mathrm{induced}$ via
`CardinalInstance.inducedSharePref` ↔ `toShareInstance`) automatically
satisfies the representation predicate.

## References

- [AGT Chapter 11] Nisan, Roughgarden, Tardos, and Vazirani, *Algorithmic Game Theory*. Cardinal representation of ordinal preferences.
