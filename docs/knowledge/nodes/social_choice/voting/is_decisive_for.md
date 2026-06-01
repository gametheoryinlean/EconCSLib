---
id: social_choice.voting.is_decisive_for
title: Decisive Coalition for an Ordered Pair
kind: definition
status: formalized
primary_topic: social_choice
topics:
  - social_choice
  - social_choice.voting
  - social_choice.voting.arrow
uses:
  - social_choice.voting.swf
  - social_choice.strict_preference
lean:
  modules:
    - EconCSLib.SocialChoice.Voting.Decisive
  declarations:
    - SocialChoice.Voting.IsDecisiveFor
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
tags:
  - social-choice
  - voting
  - decisive-coalition
  - arrow
---

# Decisive Coalition for an Ordered Pair

Fix a social welfare function $F$ ([[social_choice.voting.swf]]). A coalition
$C \subseteq N$ is *decisive for the ordered pair* $(a, b)$ if unanimous
strict $a \succ b$ inside $C$ forces society to rank $a \succ b$:
$$
\forall P,\ \bigl(\forall i \in C,\ a \succ_{P_i} b\bigr)
\Rightarrow a \succ_{F(P)} b.
$$

In Lean: `SocialChoice.Voting.IsDecisiveFor F C a b`.

The pair $(a,b)$ is ordered: decisiveness for $(a,b)$ does *not* imply
decisiveness for $(b,a)$. Lifting from a single decisive pair to all pairs is
the content of the *field expansion* lemma
[[social_choice.voting.decisive_spread]].

Decisiveness is the structural device behind the Arrow proof
([[social_choice.voting.arrow_of_unanimity_iia]]): one shows the grand
coalition is decisive (under unanimity), that decisive coalitions can be
shrunk in cardinality (under unanimity + IIA), and that a singleton
decisive coalition is a dictator.

## References

- [MSZ 21.14] Maschler, Solan, and Zamir, *Game Theory*. Decisive coalitions.
