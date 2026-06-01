---
id: social_choice.voting.decisive_contraction
title: Coalition Contraction — Splitting a Decisive Coalition
kind: theorem
status: staged
primary_topic: social_choice
topics:
  - social_choice
  - social_choice.voting
  - social_choice.voting.arrow
uses:
  - social_choice.voting.decisive_spread
lean:
  modules:
    - EconCSLib.SocialChoice.Voting.Decisive
  declarations:
    - SocialChoice.Voting.decisive_contraction
verification:
  statement: accepted
  proof: accepted
  alignment: aligned
tags:
  - social-choice
  - voting
  - decisive-coalition
  - arrow
  - contraction
---

# Coalition Contraction — Splitting a Decisive Coalition

**Theorem.** Let $F$ be a social welfare function satisfying unanimity
([[social_choice.voting.unanimity]]) and IIA ([[social_choice.voting.iia]]),
on a finite voter type with $|A| \ge 3$. If a decisive coalition
$C$ ([[social_choice.voting.is_decisive]]) has at least two members, then
there exists a strictly smaller nonempty decisive coalition $D \subsetneq C$.

In Lean: `SocialChoice.Voting.decisive_contraction` (a public lemma of the Arrow
development in `Decisive.lean`).

## Proof sketch

Pick two distinct elements $i, j \in C$ and split $C = C_1 \cup C_2$ with
$C_1 = \{i\}$ and $C_2 = C \setminus \{i\}$.

By the three-alternative hypothesis, fix distinct $x, y, z \in A$ and
build a *Condorcet-style profile* $P_0$ over the tripartition
$(C_1, C^c, C_2)$:

- $C_1$ ranks $x \succ y \succ z$;
- $C^c$ ranks $y \succ z \succ x$;
- $C_2$ ranks $z \succ x \succ y$.

Such a profile exists by an explicit construction
(`exists_condorcet_profile'` in the source).

Now branch on the social ranking of $x$ versus $z$ at $P_0$:

- **Case $x \succ_{F(P_0)} z$.** Every voter in $C$ has
  $x \succ z$ in $P_0$, while every voter outside $C$ has the opposite.
  Applying the field-expansion lemma
  ([[social_choice.voting.decisive_spread]]) to the witness pair
  $(x, z)$ shows $C_1$ is weakly decisive for $(x, z)$, hence decisive.
  But $|C_1| = 1 < |C|$, so $C_1$ is the smaller decisive coalition.

- **Case $\neg (x \succ_{F(P_0)} z)$.** Use unanimity on the $C$-shared
  preference $x \succ y$ to obtain $x \succ_{F(P_0)} y$. Combined with
  the case hypothesis and totality of $F(P_0)$ we get
  $z \succ_{F(P_0)} y$. Then $C_2$ is the smaller decisive coalition by the
  same field-expansion argument applied at the witness $(z, y)$.

Either way, we exhibit a nonempty decisive coalition strictly inside $C$.
The argument needs IIA to carry the conclusion from $P_0$ to arbitrary
$C$-unanimous profiles and unanimity to derive the auxiliary social
rankings used in the case split.

## References

- [MSZ Chapter 21] Maschler, Solan, and Zamir, *Game Theory*. Contraction step in the decisive-coalitions proof.
