---
id: social_choice.voting.minimal_decisive_card_one
title: Minimal Decisive Coalition Has Size One
kind: theorem
status: staged
primary_topic: social_choice
topics:
  - social_choice
  - social_choice.voting
  - social_choice.voting.arrow
uses:
  - social_choice.voting.unanimity_univ_decisive
  - social_choice.voting.decisive_contraction
lean:
  modules:
    - EconCSLib.SocialChoice.Voting.Decisive
  declarations:
    - SocialChoice.Voting.decisive_minimal
    - SocialChoice.Voting.exists_minimal_decisive_coalition
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

# Minimal Decisive Coalition Has Size One

**Theorem.** Let $F$ be a social welfare function on a finite nonempty voter
type with $|A| \ge 3$, satisfying unanimity ([[social_choice.voting.unanimity]])
and IIA ([[social_choice.voting.iia]]). Then $F$ admits a decisive coalition of
size exactly one.

Formally: the cardinality predicate $n \mapsto \exists C\ \mathrm{decisive\ of\ size}\ n$
is well-founded on $\mathbb{N}$, and its minimum equals $1$.

In Lean: `SocialChoice.Voting.decisive_minimal` (proves
`Minimal (exists_nonempty_decisive_of_size F) 1`), with the existence half
`SocialChoice.Voting.exists_minimal_decisive_coalition`. Both are public lemmas
of the Arrow development in `Decisive.lean`, over the predicate
`SocialChoice.Voting.exists_nonempty_decisive_of_size`.

## Proof sketch

1. The grand coalition is decisive of size $|N|$
   ([[social_choice.voting.unanimity_univ_decisive]]), so the cardinality
   predicate is nonempty. Take any minimal $n$.

2. $n \ne 0$: a decisive coalition is nonempty by definition.

3. $n < 2$: if $n \ge 2$, the contraction lemma
   ([[social_choice.voting.decisive_contraction]]) produces a strictly
   smaller decisive coalition, contradicting minimality.

Combining $n \ne 0$ and $n < 2$ forces $n = 1$. $\square$

## References

- [MSZ Chapter 21] Maschler, Solan, and Zamir, *Game Theory*. Minimality step in the decisive-coalitions proof.
