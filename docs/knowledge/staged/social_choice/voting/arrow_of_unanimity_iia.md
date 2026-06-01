---
id: social_choice.voting.arrow_of_unanimity_iia
title: Arrow's Theorem via Decisive Coalitions
kind: theorem
status: staged
primary_topic: social_choice
topics:
  - social_choice
  - social_choice.voting
  - social_choice.voting.arrow
uses:
  - social_choice.voting.minimal_decisive_card_one
  - social_choice.voting.dictatorial_swf
lean:
  modules:
    - EconCSLib.SocialChoice.Voting.Decisive
  declarations:
    - SocialChoice.Voting.arrow_of_unanimity_iia
verification:
  statement: accepted
  proof: accepted
  alignment: aligned
tags:
  - social-choice
  - voting
  - arrow
  - decisive-coalition
---

# Arrow's Theorem via Decisive Coalitions

**Theorem.** Let $A$ have three distinct elements (witnessed by
`h0 : ∃ x y z, x ≠ y ∧ x ≠ z ∧ y ≠ z`) and let $N$ be a finite nonempty
voter type. Every social welfare function $F$
([[social_choice.voting.swf]]) satisfying unanimity
([[social_choice.voting.unanimity]]) and IIA
([[social_choice.voting.iia]]) is dictatorial
([[social_choice.voting.dictatorial_swf]]).

In Lean: `SocialChoice.Voting.arrow_of_unanimity_iia`. This is the internal
decisive-coalition form of Arrow; the public Fintype-cardinality version
([[social_choice.voting.arrow_impossibility]]) packages the
three-distinct-elements hypothesis from `Fintype.card A ≥ 3`.

## Proof sketch

By the size-one minimal-decisive-coalition theorem
([[social_choice.voting.minimal_decisive_card_one]]) there is a decisive
coalition $C$ with $|C| = 1$. Subsingleton extraction yields $C = \{i_0\}$
for some $i_0$. Because decisive on every ordered pair means in particular
that $i_0$'s strict preference forces society's strict preference for every
pair, $i_0$ is a dictator. $\square$

## Attribution

The Lean port of the full decisive-coalitions proof is adapted from
`GameTheory/SocialChoice.lean` in
[mdnestor/GameTheory](https://github.com/mdnestor/GameTheory).

## References

- [MSZ 21.10] Maschler, Solan, and Zamir, *Game Theory*. Arrow's impossibility theorem.
- Arrow, K. J. (1951). *Social Choice and Individual Values*.
