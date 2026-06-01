---
id: social_choice.voting.iia_strict
title: IIA on Strict Preference
kind: lemma
status: staged
primary_topic: social_choice
topics:
  - social_choice
  - social_choice.voting
  - social_choice.voting.arrow
uses:
  - social_choice.voting.iia
  - social_choice.strict_preference
lean:
  modules:
    - EconCSLib.SocialChoice.Voting.Decisive
  declarations:
    - SocialChoice.Voting.iia_strict
verification:
  statement: accepted
  proof: accepted
  alignment: aligned
tags:
  - social-choice
  - voting
  - iia
  - arrow
---

# IIA on Strict Preference

**Lemma.** If $F$ satisfies IIA ([[social_choice.voting.iia]]), and two
profiles $P$, $Q$ agree on the weak ranking of the pair $\{a, b\}$ in both
directions ($P_i(a,b) \iff Q_i(a,b)$ and $P_i(b,a) \iff Q_i(b,a)$ for all
$i$), then society's *strict* preference between $a$ and $b$ is the same
under $P$ and $Q$:
$$
a \succ_{F(P)} b \iff a \succ_{F(Q)} b.
$$

*Proof.* Strict preference $\succ_R$ is defined as $R(a,b) \wedge \neg R(b,a)$
([[social_choice.strict_preference]]). Both conjuncts are determined by
the IIA-controlled weak rankings, so the strict comparison transfers between
$P$ and $Q$. $\square$

In Lean: `SocialChoice.Voting.iia_strict`.

This is the workhorse algebraic lemma in the decisive-coalition Arrow proof
([[social_choice.voting.arrow_of_unanimity_iia]]): every step where the
proof modifies a profile while preserving the $\{a,b\}$ pair-restricted
profile invokes this lemma to keep society's strict $a$-vs-$b$ comparison
fixed.

## References

- [MSZ Chapter 21] Maschler, Solan, and Zamir, *Game Theory*. IIA applied to strict comparisons.
