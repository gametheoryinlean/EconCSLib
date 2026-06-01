---
id: social_choice.voting.majority_prefers
title: Pairwise Majority Comparison
kind: definition
status: formalized
primary_topic: social_choice
topics:
  - social_choice
  - social_choice.voting
  - social_choice.voting.rules
uses:
  - social_choice.preference_profile
  - social_choice.strict_preference
lean:
  modules:
    - EconCSLib.SocialChoice.Voting.VotingRules
  declarations:
    - SocialChoice.Voting.MajorityPrefers
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
tags:
  - social-choice
  - voting
  - majority
---

# Pairwise Majority Comparison

For a finite voter type $N$ and preference profile $P$, society *prefers
$a$ to $b$ by strict majority* if strictly more voters strictly prefer $a$
to $b$ than vice versa:
$$
\#\{i \in N \mid a \succ_{P_i} b\}
\;>\;
\#\{i \in N \mid b \succ_{P_i} a\}.
$$

In Lean: `SocialChoice.Voting.MajorityPrefers`, written using
`Finset.card (Finset.univ.filter ...)` and the bundled strict preference
`(P i).lt`.

This is the natural starting point for two-alternative voting rules and for
the Condorcet criterion ([[social_choice.voting.condorcet_winner]]): a
Condorcet winner is an alternative that pairwise-majority-beats every
other.

The strict-majority form (as opposed to weak majority) makes pairwise
comparison antisymmetric — at most one of $a, b$ can majority-beat the
other.

## References

- [MSZ Chapter 21] Maschler, Solan, and Zamir, *Game Theory*. Majority rule.
- [AGT Chapter 10] Nisan, Roughgarden, Tardos, and Vazirani, *Algorithmic Game Theory*. Voting and Condorcet criteria.
