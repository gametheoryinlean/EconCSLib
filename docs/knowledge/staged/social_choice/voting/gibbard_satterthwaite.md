---
id: social_choice.voting.gibbard_satterthwaite
title: Gibbard–Satterthwaite Theorem
kind: theorem
status: staged
primary_topic: social_choice
topics:
  - social_choice
  - social_choice.voting
  - social_choice.voting.gibbard_satterthwaite
uses:
  - social_choice.voting.strategyproof_implies_monotonic
  - social_choice.voting.muller_satterthwaite
lean:
  modules:
    - EconCSLib.SocialChoice.Voting.GibbardSatterthwaite
  declarations:
    - SocialChoice.Voting.gibbard_satterthwaite
verification:
  statement: accepted
  proof: accepted
  alignment: aligned
tags:
  - social-choice
  - voting
  - gibbard-satterthwaite
  - strategyproof
  - impossibility
---

# Gibbard–Satterthwaite Theorem

**Theorem (Gibbard 1973, Satterthwaite 1975).** Let $N$ be a finite nonempty
voter type and $A$ a finite alternative set with $|A| \ge 3$. Every
unanimous ([[social_choice.voting.unanimity]]) and strategy-proof
([[social_choice.voting.strategyproof]]) social choice function is
dictatorial ([[social_choice.voting.dictatorial_scf]]).

In Lean: `SocialChoice.Voting.gibbard_satterthwaite`, with signature
`[Fintype N] [Nonempty N] [DecidableEq N] [Fintype A] (hA : Fintype.card A ≥ 3)`.

## Proof

The Lean term composes two lemmas:

1. `strategyproof_monotonic` ([[social_choice.voting.strategyproof_implies_monotonic]])
   turns strategy-proofness into monotonicity
   ([[social_choice.voting.monotonic_scf]]).

2. `muller_satterthwaite` ([[social_choice.voting.muller_satterthwaite]])
   turns monotonicity plus unanimity (with $|A| \ge 3$) into dictatorship.

Both intermediate theorems are themselves admitted with proof plans; once
they are filled, the composition in `gibbard_satterthwaite` closes on its
own (no further sorries in this file).

## Interpretation

For ordinal voting rules on three or more alternatives, *honesty cannot be a
dominant strategy without a dictator*. This is the SCF analogue of Arrow
([[social_choice.voting.arrow_impossibility]]), and the central motivating
impossibility for the field of *strategy-proof mechanism design* — including
randomized escapes (Gibbard 1977), domain restrictions (Moulin's median
voter on single-peaked domains), and money-augmented mechanisms (VCG, where
transfers restore incentive compatibility).

## References

- [MSZ 21.39] Maschler, Solan, and Zamir, *Game Theory*. Gibbard–Satterthwaite theorem.
- Gibbard, A. (1973). "Manipulation of voting schemes". *Econometrica*.
- Satterthwaite, M. A. (1975). "Strategy-proofness and Arrow's conditions". *J. Econ. Theory*.
