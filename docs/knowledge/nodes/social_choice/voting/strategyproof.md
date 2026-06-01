---
id: social_choice.voting.strategyproof
title: Strategy-Proof Social Choice Function
kind: definition
status: formalized
primary_topic: social_choice
topics:
  - social_choice
  - social_choice.voting
uses:
  - social_choice.voting.scf
  - social_choice.strict_preference
lean:
  modules:
    - EconCSLib.SocialChoice.Voting.Basic
  declarations:
    - SocialChoice.Voting.ResoluteStrategyproofness
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
tags:
  - social-choice
  - voting
  - axiom
  - strategyproof
  - mechanism-design
---

# Strategy-Proof Social Choice Function

A resolute voting rule $f$ (one that returns a single winner) is
*strategy-proof* (non-manipulable) if no voter can obtain a strictly better
winner by misreporting. If $f(P) = \{a\}$ and voter $i$ unilaterally switches
their ballot to a ranking $r$, producing $f(P[i \mapsto r]) = \{b\}$, then
$$
\neg\,(\, b \succ_{P_i} a \,),
$$
i.e. the new winner $b$ is never strictly preferred to the honest winner $a$
under $i$'s *true* preference $P_i$.

In Lean: `SocialChoice.Voting.ResoluteStrategyproofness`, stated for a rule
together with a `Resolute` witness, using `updateProfile P i r` for the
profile with voter $i$'s ballot replaced by ranking $r$.

Strategy-proofness is the central incentive-compatibility axiom for ordinal
voting rules; it is the natural ordinal counterpart of dominant-strategy
incentive compatibility (DSIC) in mechanism design.

Two classical implications closed the field:

- Resolute strategy-proof rules are monotonic
  ([[social_choice.voting.strategyproof_implies_monotonic]]).
- Combined with unanimity ([[social_choice.voting.unanimity]]) and
  $|A| \ge 3$, strategy-proofness forces dictatorship — the
  Gibbard–Satterthwaite theorem
  ([[social_choice.voting.gibbard_satterthwaite]]).

## References

- [MSZ 21.36] Maschler, Solan, and Zamir, *Game Theory*. Strategy-proof / nonmanipulable SCF.
- Gibbard, A. (1973). "Manipulation of voting schemes". *Econometrica*.
- Satterthwaite, M. A. (1975). "Strategy-proofness and Arrow's conditions". *J. Econ. Theory*.
