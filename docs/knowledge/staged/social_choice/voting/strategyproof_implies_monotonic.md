---
id: social_choice.voting.strategyproof_implies_monotonic
title: Strategy-Proof ⇒ Monotonic
kind: theorem
status: staged
primary_topic: social_choice
topics:
  - social_choice
  - social_choice.voting
  - social_choice.voting.gibbard_satterthwaite
uses:
  - social_choice.voting.strategyproof
  - social_choice.voting.monotonic_scf
lean:
  modules:
    - EconCSLib.SocialChoice.Voting.GibbardSatterthwaite
  declarations:
    - SocialChoice.Voting.strategyproof_monotonic
verification:
  statement: accepted
  proof: gap
  alignment: aligned
tags:
  - social-choice
  - voting
  - gibbard-satterthwaite
  - strategyproof
  - monotonic
---

# Strategy-Proof ⇒ Monotonic

**Theorem.** Every strategy-proof social choice function on a finite voter
type is monotonic.

That is, ([[social_choice.voting.strategyproof]]) implies
([[social_choice.voting.monotonic_scf]]).

In Lean this is `SocialChoice.Voting.strategyproof_monotonic`. The statement is
present in `EconCSLib.SocialChoice.Voting.GibbardSatterthwaite`; the proof is
currently a `sorry`, with the standard finite-replacement argument outlined
below.

## Proof plan

We argue the contrapositive: if monotonicity fails between profiles $P$ and
$Q$ at a winner $a = G(P)$, then strategy-proofness fails too.

1. **Setup.** Fix profiles $P, Q$ and $a$ with $G(P) = a$ and the
   monotonicity hypothesis ($\forall i,\ \forall c \ne a,\
   a \succ_{P_i} c \Rightarrow a \succ_{Q_i} c$), but
   $G(Q) \ne a$.

2. **Finite path.** Enumerate $N = \{i_1, \dots, i_n\}$ and form the chain
   of profiles $R_0 = P$, $R_k$ obtained from $R_{k-1}$ by replacing voter
   $i_k$'s report from $P_{i_k}$ to $Q_{i_k}$. Then $R_n = Q$. The outcome
   $G(R_k)$ varies along this chain, starting at $a$ and ending at
   $G(Q) \ne a$.

3. **First defection.** Let $k$ be the smallest index where the outcome
   *first* changes off $a$: $G(R_{k-1}) = a$ and $G(R_k) \ne a$. Write
   $a' = G(R_k)$.

4. **Profitable manipulation.** Inspect the two consecutive profiles. By
   the monotonicity hypothesis, voter $i_k$'s true ranking $P_{i_k}$ has
   $a$ strictly above $a'$ (otherwise the hypothesis would fail). At the
   profile $R_{k-1}$ truthful $i_k$ obtains $a$; at $R_k$ — obtained from
   $R_{k-1}$ by $i_k$ reporting $Q_{i_k}$ instead of $P_{i_k}$ — they
   obtain $a' \prec_{P_{i_k}} a$, contradicting strategy-proofness
   ([[social_choice.voting.strategyproof]]) applied to the deviation
   $Q_{i_k}$.

The argument needs `Fintype N` (to enumerate the chain) and `DecidableEq N`
(to substitute one voter's report).

## References

- [MSZ 21.35] Maschler, Solan, and Zamir, *Game Theory*. Strategy-proofness implies monotonicity.
