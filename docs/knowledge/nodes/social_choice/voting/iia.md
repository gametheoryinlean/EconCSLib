---
id: social_choice.voting.iia
title: Independence of Irrelevant Alternatives
kind: definition
status: formalized
primary_topic: social_choice
topics:
  - social_choice
  - social_choice.voting
uses:
  - social_choice.voting.swf
lean:
  modules:
    - EconCSLib.SocialChoice.Voting.Basic
  declarations:
    - SocialChoice.Voting.SWF.IIA
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
tags:
  - social-choice
  - voting
  - axiom
  - iia
---

# Independence of Irrelevant Alternatives

A social welfare function $F$ satisfies *Independence of Irrelevant
Alternatives* (IIA) if society's ranking of any pair $\{a,b\}$ depends only
on how the voters rank $a$ versus $b$, not on how they rank either of these
against any third alternative:
$$
\forall P, Q,\ \forall a, b,\
\bigl(\forall i,\ P_i(a,b) \iff Q_i(a,b)\bigr)
\Rightarrow \bigl(F(P)(a,b) \iff F(Q)(a,b)\bigr).
$$

In Lean: `SocialChoice.Voting.SWF.IIA`. The statement is in terms of the
weak preference $P_i(a,b)$ (the raw bundled relation), which is the standard
formulation.

A useful corollary: under IIA the *strict* social preference between $a$ and
$b$ also depends only on the pair-restricted profiles
([[social_choice.voting.iia_strict]] in the decisive-coalition proof).

IIA, together with unanimity ([[social_choice.voting.unanimity]]), is the
Arrow hypothesis: every SWF satisfying both must be dictatorial when there
are at least three alternatives
([[social_choice.voting.arrow_impossibility]]).

## References

- [MSZ 21.9] Maschler, Solan, and Zamir, *Game Theory*. Independence of irrelevant alternatives.
- Arrow, K. J. (1951). *Social Choice and Individual Values*. Original IIA axiom.
