---
id: social_choice.voting.is_weakly_decisive_for
title: Weakly Decisive Coalition
kind: definition
status: formalized
primary_topic: social_choice
topics:
  - social_choice
  - social_choice.voting
  - social_choice.voting.arrow
uses:
  - social_choice.voting.is_decisive_for
lean:
  modules:
    - EconCSLib.SocialChoice.Voting.Decisive
  declarations:
    - SocialChoice.Voting.IsWeaklyDecisiveFor
    - SocialChoice.Voting.isWeaklyDecisiveFor_of_isDecisiveFor
verification:
  definition: accepted
  proof: accepted
  alignment: aligned
tags:
  - social-choice
  - voting
  - decisive-coalition
  - arrow
---

# Weakly Decisive Coalition

A coalition $C \subseteq N$ is *weakly decisive for the ordered pair*
$(a, b)$ under a social welfare function $F$ ([[social_choice.voting.swf]])
if unanimous $a \succ b$ inside $C$, *combined with* unanimous
$b \succ a$ outside $C$, forces society to rank $a \succ b$:
$$
\forall P,\
\bigl(\forall i \in C,\ a \succ_{P_i} b\bigr) \wedge
\bigl(\forall i \notin C,\ b \succ_{P_i} a\bigr)
\Rightarrow a \succ_{F(P)} b.
$$

In Lean: `SocialChoice.Voting.IsWeaklyDecisiveFor F C a b`.

Weak decisiveness is *implied* by decisiveness ([[social_choice.voting.is_decisive_for]])
— a witness profile satisfying the stronger constraint of total opposition
is in particular a witness for plain decisiveness:
`SocialChoice.Voting.isWeaklyDecisiveFor_of_isDecisiveFor`.

The opposite-direction-strengthening — turning weak decisiveness into full
decisiveness — is the substantive content of the *field expansion* lemma
[[social_choice.voting.decisive_spread]]. The split into "weak" vs full
decisiveness lets the Arrow proof use only the simpler hypothesis when
building witnesses.

## References

- [MSZ 21.14ff] Maschler, Solan, and Zamir, *Game Theory*. Weak decisiveness in the field-expansion argument.
