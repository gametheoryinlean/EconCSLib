---
id: social_choice.voting.borda_score
title: Borda Score and Borda Rule
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
    - SocialChoice.Voting.bordaScore
    - SocialChoice.Voting.scoreCandidate
    - SocialChoice.Voting.borda
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
tags:
  - social-choice
  - voting
  - borda
---

# Borda Score and Borda Rule

The *Borda score* is the positional scoring vector that awards $m - 1$ points
to a voter's top alternative and one fewer for each rank down. As a
rank-indexed vector (rank $0$ is the top, $m = |A|$),
$$
\mathrm{bordaScore}(m, r) = m - 1 - r,
$$
so under preference $P_i$ an alternative $a$ earns the count of alternatives
ranked strictly below it, $\#\{c \in A \mid a \succ_{P_i} c\}$.

The *total Borda score* of $a$ across the profile sums the per-voter scores,
$B(P, a) = \sum_{i \in N} \mathrm{bordaScore}$ — in Lean this is the generic
`scoreCandidate P` aggregator applied to the Borda vector.

The *Borda rule* selects the alternatives maximising total Borda score, with
ties kept:
$$
\mathrm{borda}(P) = \arg\max_{a \in A}\ B(P, a).
$$

In Lean: `SocialChoice.Voting.bordaScore` (the score vector),
`SocialChoice.Voting.scoreCandidate` (the total-score aggregator), and
`SocialChoice.Voting.borda` (the rule, `scoringRule bordaScore`, a set-valued
`VotingRule`). These are `noncomputable` because aggregating a bare-`Prop`
strict preference uses classical decidability, and ties are kept in the
winner set.

## Properties (informal)

- Borda is monotonic, anonymous, and neutral.
- Borda is *not* a Condorcet method
  ([[social_choice.voting.condorcet_winner]]): the Borda winner may differ
  from the Condorcet winner when both exist.
- Borda is strategy-manipulable
  ([[social_choice.voting.strategyproof]] fails) — already follows from
  Gibbard–Satterthwaite for $|A| \ge 3$.

## References

- [AGT Chapter 10] Nisan, Roughgarden, Tardos, and Vazirani, *Algorithmic Game Theory*. Positional scoring rules.
