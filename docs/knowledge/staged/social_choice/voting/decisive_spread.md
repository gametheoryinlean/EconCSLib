---
id: social_choice.voting.decisive_spread
title: Field Expansion — Decisive on One Pair Implies Decisive Everywhere
kind: theorem
status: staged
primary_topic: social_choice
topics:
  - social_choice
  - social_choice.voting
  - social_choice.voting.arrow
uses:
  - social_choice.voting.is_decisive
  - social_choice.voting.is_weakly_decisive_for
  - social_choice.voting.unanimity
  - social_choice.voting.iia_strict
lean:
  modules:
    - EconCSLib.SocialChoice.Voting.Decisive
  declarations:
    - SocialChoice.Voting.decisive_spread
verification:
  statement: accepted
  proof: accepted
  alignment: aligned
tags:
  - social-choice
  - voting
  - decisive-coalition
  - arrow
  - field-expansion
---

# Field Expansion — Decisive on One Pair Implies Decisive Everywhere

**Theorem.** Let $F$ be a social welfare function satisfying unanimity
([[social_choice.voting.unanimity]]) and IIA ([[social_choice.voting.iia]]).
If a nonempty coalition $C$ is *weakly decisive* for some ordered pair
$(x, y)$ with three distinct alternatives $x, y, z$
([[social_choice.voting.is_weakly_decisive_for]]), then $C$ is *decisive*
for every ordered pair of alternatives ([[social_choice.voting.is_decisive]]).

In Lean: `SocialChoice.Voting.decisive_spread` (a public lemma of the Arrow
development in `Decisive.lean`), depending on the third-alternative witness
`x ≠ y ≠ z ≠ x`.

## Proof sketch

The argument splits into directional "spread" lemmas that each construct an
auxiliary profile and apply [[social_choice.voting.iia_strict]] plus
unanimity:

1. **Forward spread** $x \succ_C y \Rightarrow x \succ_C z$.
   Build a profile where members of $C$ rank $x \succ y \succ z$ and members
   outside $C$ rank $y \succ x$ but everyone ranks $y \succ z$. Weak
   decisiveness gives $x \succ_{F(P')} y$; unanimity gives
   $y \succ_{F(P')} z$; transitivity of $F(P')$ yields $x \succ_{F(P')} z$.
   Then IIA (`iia_strict`) carries the conclusion back to an arbitrary
   $C$-unanimous profile on $(x,z)$.

2. **Backward spread** $x \succ_C y \Rightarrow z \succ_C y$. Symmetric.

3. **Symmetric spread** $x \succ_C y \Rightarrow y \succ_C x$. Compose
   two forward / backward steps through a third alternative.

4. **Strengthening** $x \succ_C y$ from weak to full decisiveness.

5. Combining these with case analysis on overlap between $(s, t)$ and
   $(x, y, z)$ (the helper `isDecisive_spread` in the source) extends
   $(s, t)$-decisiveness to *all* ordered pairs.

The proof requires $|A| \ge 3$ only through the third-alternative witness
$z$, hence the hypothesis $x \ne y \ne z \ne x$ in the Lean signature.

## References

- [MSZ Chapter 21] Maschler, Solan, and Zamir, *Game Theory*. Field expansion lemma in the decisive-coalitions proof.
