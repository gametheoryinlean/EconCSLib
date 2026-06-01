---
id: social_choice.voting.plurality_score
title: Plurality Score and Plurality Rule
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
    - SocialChoice.Voting.pluralityScore
    - SocialChoice.Voting.plurality
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
tags:
  - social-choice
  - voting
  - plurality
---

# Plurality Score and Plurality Rule

The *plurality score* is the positional scoring vector that puts all weight on
the top rank: an alternative earns $1$ from each voter who ranks it first and
$0$ otherwise. As a rank-indexed vector (rank $0$ is the top),
$$
\mathrm{pluralityScore}(m, r) =
\begin{cases} 1 & r = 0 \\ 0 & r \ne 0,\end{cases}
$$
independent of the number of alternatives $m$.

The *plurality rule* is the positional scoring rule built from this vector. At
a profile $P$ its winner set is the alternatives maximising total plurality
score — those ranked first by the most voters, with ties allowed:
$$
\mathrm{plurality}(P) =
\arg\max_{a \in A}\ \#\{i \in N \mid a \text{ is } i\text{'s top choice}\}.
$$

In Lean: `SocialChoice.Voting.pluralityScore` (the score vector) and
`SocialChoice.Voting.plurality` (the rule, `scoringRule pluralityScore`, a
set-valued `VotingRule`). As with Borda ([[social_choice.voting.borda_score]]),
these are `noncomputable` because aggregating a bare-`Prop` strict preference
uses classical decidability, and ties are kept in the winner set.

## Properties (informal)

- Plurality is the simplest positional rule (all weight on the top rank).
- Plurality is *not* a Condorcet method: examples exist where the Condorcet
  winner is *not* even a plurality winner.
- Plurality satisfies unanimity ([[social_choice.voting.unanimity]]) but is
  strategy-manipulable for $|A| \ge 3$
  ([[social_choice.voting.gibbard_satterthwaite]]).

## References

- [AGT Chapter 10] Nisan, Roughgarden, Tardos, and Vazirani, *Algorithmic Game Theory*. Plurality and positional scoring rules.
