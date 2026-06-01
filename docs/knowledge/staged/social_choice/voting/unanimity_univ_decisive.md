---
id: social_choice.voting.unanimity_univ_decisive
title: Grand Coalition Is Decisive under Unanimity
kind: theorem
status: staged
primary_topic: social_choice
topics:
  - social_choice
  - social_choice.voting
  - social_choice.voting.arrow
uses:
  - social_choice.voting.is_decisive
  - social_choice.voting.unanimity
lean:
  modules:
    - EconCSLib.SocialChoice.Voting.Decisive
  declarations:
    - SocialChoice.Voting.unanimity_univ_isDecisive
verification:
  statement: accepted
  proof: accepted
  alignment: aligned
tags:
  - social-choice
  - voting
  - decisive-coalition
  - arrow
---

# Grand Coalition Is Decisive under Unanimity

**Theorem.** If a social welfare function $F$ ([[social_choice.voting.swf]])
satisfies unanimity ([[social_choice.voting.unanimity]]), then the grand
coalition $N \subseteq N$ is decisive for $F$
([[social_choice.voting.is_decisive]]).

*Proof.* Unanimity says: if every voter strictly prefers $a$ to $b$, society
does too. Specialising the universal quantifier in $\mathrm{IsDecisive}$ to
the universal coalition gives exactly that statement. $\square$

In Lean: `SocialChoice.Voting.unanimity_univ_isDecisive`.

This is the *base case* of the decisive-coalition proof of Arrow's theorem
([[social_choice.voting.arrow_of_unanimity_iia]]): start from the trivially
decisive grand coalition, then shrink it in cardinality using
[[social_choice.voting.decisive_contraction]] until you reach a singleton
dictator.

## References

- [MSZ Chapter 21] Maschler, Solan, and Zamir, *Game Theory*. Decisive-coalitions proof of Arrow.
