---
id: social_choice.voting.condorcet_winner
title: Condorcet Winner
kind: definition
status: formalized
primary_topic: social_choice
topics:
  - social_choice
  - social_choice.voting
  - social_choice.voting.rules
uses:
  - social_choice.voting.majority_prefers
source:
  spans:
    - artifact: msz-game-theory
      locator: "Chapter 21, Example 21.16"
      format: section
      note: "Condorcet winner"
lean:
  modules:
    - EconCSLib.SocialChoice.Voting.VotingRules
  declarations:
    - SocialChoice.Voting.CondorcetWinner
    - SocialChoice.Voting.HasCondorcetWinner
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
tags:
  - social-choice
  - voting
  - condorcet
---

# Condorcet Winner

An alternative $a \in A$ is a *Condorcet winner* for a preference profile
$P$ if it beats every other alternative in pairwise strict-majority
comparison ([[social_choice.voting.majority_prefers]]):
$$
\forall b \in A,\ b \ne a,\ \mathrm{MajorityPrefers}(P, a, b).
$$

A profile *has a Condorcet winner* if some such $a$ exists.

In Lean: `SocialChoice.Voting.CondorcetWinner` and `HasCondorcetWinner`.

A Condorcet winner — when one exists — is the canonical "majority-acceptable"
choice. But Condorcet winners *need not exist*: cyclic pairwise majorities
("Condorcet paradox", [[social_choice.voting.condorcet_paradox]]) are
possible already with 3 voters and 3 alternatives.

Concrete rules that always elect the Condorcet winner when it exists are
called *Condorcet methods* (Copeland, Schulze, Ranked Pairs, …). Borda
([[social_choice.voting.borda_score]]) and plurality
([[social_choice.voting.plurality_score]]) are *not* Condorcet methods.

## References

- [MSZ, Chapter 21] Maschler, Solan, and Zamir, *Game Theory*. Condorcet winner; see the `source` block
  above for the precise locator.
