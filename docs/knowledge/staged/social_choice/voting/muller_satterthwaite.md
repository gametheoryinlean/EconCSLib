---
id: social_choice.voting.muller_satterthwaite
title: Muller–Satterthwaite Theorem
kind: theorem
status: staged
primary_topic: social_choice
topics:
  - social_choice
  - social_choice.voting
  - social_choice.voting.gibbard_satterthwaite
uses:
  - social_choice.voting.monotonic_scf
  - social_choice.voting.dictatorial_scf
  - social_choice.voting.arrow_impossibility
lean:
  modules:
    - EconCSLib.SocialChoice.Voting.GibbardSatterthwaite
  declarations:
    - SocialChoice.Voting.muller_satterthwaite
verification:
  statement: accepted
  proof: gap
  alignment: aligned
tags:
  - social-choice
  - voting
  - gibbard-satterthwaite
  - muller-satterthwaite
  - monotonic
---

# Muller–Satterthwaite Theorem

**Theorem.** Let $N$ be a finite nonempty voter type and $A$ a finite
alternative set with $|A| \ge 3$. Every unanimous
([[social_choice.voting.unanimity]]) and monotonic
([[social_choice.voting.monotonic_scf]]) social choice function is
dictatorial ([[social_choice.voting.dictatorial_scf]]).

In Lean: `SocialChoice.Voting.muller_satterthwaite`. The statement is
present in `EconCSLib.SocialChoice.Voting.GibbardSatterthwaite`; the proof is
currently a `sorry`, with the standard SCF-from-SWF reduction outlined below.

## Proof plan (Arrow-reduction route)

Given $G : \mathrm{PrefProfile}(N, A) \to A$ unanimous and monotonic, construct
an auxiliary social welfare function $F : \mathrm{PrefProfile}(N, A) \to
\mathrm{Pref}(A)$ defined pairwise as: for each pair $\{a, b\}$,
$F(P)$ ranks $a \succ b$ iff $G$ selects $a$ at the *pair-restricted*
profile $P|_{\{a,b\}}$ that pushes both $a$ and $b$ to the top above all
other alternatives in everyone's ranking.

1. **Well-definedness.** Pair restriction yields a profile where $\{a,b\}$
   are everyone's top two; by unanimity (and finite case analysis on the
   structure of $P|_{\{a,b\}}$) the outcome must be $a$ or $b$.

2. **$F$ satisfies unanimity.** If everyone strictly prefers $a$ to $b$ in
   $P$, the pair-restricted profile has $a$ above $b$ at every voter; by
   unanimity of $G$ the outcome is $a$, hence $F(P)$ strictly ranks
   $a \succ b$.

3. **$F$ satisfies IIA.** Society's $\{a,b\}$ ranking depends only on
   $P|_{\{a,b\}}$, which depends only on each voter's $\{a,b\}$ pair
   ranking. (Monotonicity of $G$ is what makes this construction
   independent of how voters rank irrelevant alternatives.)

4. **$F$ is a `Pref`.** Transitivity of $F(P)$ uses monotonicity plus a
   third-alternative case analysis; reflexivity and totality follow from
   the unanimous outcome.

5. **Apply Arrow** ([[social_choice.voting.arrow_impossibility]]) to
   conclude $F$ is dictatorial: some voter $i$'s strict preference
   determines $F(P)$ for every pair.

6. **Transfer back to $G$.** A pairwise dictator over $F$ is also a
   top-pick dictator over $G$: at any profile, $G(P)$ must lie above
   every other alternative in $i$'s ranking (else the pair-restricted
   profile witnessing the contradiction would yield a different
   $F$-ranking).

The argument needs `Fintype N`, `Nonempty N`, `Fintype A`, and the
hypothesis $|A| \ge 3$ to invoke Arrow.

## References

- [MSZ 21.27] Maschler, Solan, and Zamir, *Game Theory*. Muller–Satterthwaite theorem and the SWF reduction.
