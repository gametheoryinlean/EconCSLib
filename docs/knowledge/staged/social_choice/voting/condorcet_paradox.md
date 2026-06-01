---
id: social_choice.voting.condorcet_paradox
title: Condorcet Paradox
kind: theorem
status: staged
primary_topic: social_choice
topics:
  - social_choice
  - social_choice.voting
  - social_choice.voting.rules
uses:
  - social_choice.voting.condorcet_winner
source:
  spans:
    - artifact: msz-game-theory
      locator: "Chapter 21, Example 21.17"
      format: section
      note: "Condorcet's voting paradox"
lean:
  modules:
    - EconCSLib.SocialChoice.Voting.VotingRules
  declarations:
    - SocialChoice.Voting.condorcet_paradox_possible
verification:
  statement: accepted
  proof: accepted
  alignment: aligned
tags:
  - social-choice
  - voting
  - condorcet
  - example
  - counterexample
---

# Condorcet Paradox

**Theorem.** There exists a preference profile on three voters and three
alternatives that has *no* Condorcet winner
([[social_choice.voting.condorcet_winner]]).

In Lean: `SocialChoice.Voting.condorcet_paradox_possible`. The explicit
witness is the cyclic *Condorcet cycle profile* over $\mathrm{Fin}\ 3$:

| voter | first | second | third |
|:-----:|:-----:|:------:|:-----:|
| 0     | 0     | 1      | 2     |
| 1     | 1     | 2      | 0     |
| 2     | 2     | 0      | 1     |

Pairwise majority is cyclic ($0 \succ_{\text{maj}} 1$,
$1 \succ_{\text{maj}} 2$, $2 \succ_{\text{maj}} 0$), so no alternative
beats both of the others.

The Lean proof builds this profile via a small rank function on
$\mathrm{Fin}\ 3$ and case-analyses the three would-be Condorcet winners
$a \in \{0, 1, 2\}$, using `fin_cases` and explicit
$\mathrm{MajorityPrefers}$ counts.

## Interpretation

Aggregating individual preferences by pairwise majority does not always
produce a transitive social ranking. The Condorcet paradox is the canonical
demonstration that majority rule alone is not enough to escape Arrow-style
impossibilities; it motivates positional rules (Borda
[[social_choice.voting.borda_score]], plurality
[[social_choice.voting.plurality_score]]) and tournament solutions
(Copeland, Slater) that always select *some* alternative.

## References

- [MSZ, Chapter 21] Maschler, Solan, and Zamir, *Game Theory*. Condorcet's voting paradox; see the
  `source` block above for the precise locator.
