---
id: social_choice.voting.monotonic_scf
title: Monotonic Social Choice Function
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
    - SocialChoice.Voting.Monotonicity
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
tags:
  - social-choice
  - voting
  - axiom
  - monotonicity
---

# Monotonic Social Choice Function

A voting rule $f$ is *monotonic* if a selected winner stays selected whenever
it is weakly pushed up in everyone's ranking. Writing $Q$ for a profile
obtained from $P$ by a *simple lift* of $a$,
$$
a \in f(P) \;\wedge\; \mathrm{SimpleLift}(Q, P, a)
\;\Rightarrow\; a \in f(Q).
$$
Here $\mathrm{SimpleLift}(Q, P, a)$ requires, for every voter $i$ and
alternative $x$: if $a \succ_{P_i} x$ then $a \succ_{Q_i} x$, and if
$x \succ_{Q_i} a$ then $x \succ_{P_i} a$ — i.e. $a$ only moves up, never down.

In Lean: `SocialChoice.Voting.Monotonicity`, using the lift relation
`SocialChoice.Voting.SimpleLift`.

The condition only constrains strict comparisons involving the winner $a$;
voters may rearrange their rankings among the other alternatives freely.

Monotonicity is the bridge from strategy-proofness
([[social_choice.voting.strategyproof]]) to dictatorship in the Gibbard
–Satterthwaite chain: resolute strategy-proof rules are monotonic
([[social_choice.voting.strategyproof_implies_monotonic]]), and monotonic
unanimous resolute rules with $|A| \ge 3$ are dictatorial
([[social_choice.voting.muller_satterthwaite]]).

## References

- [MSZ 21.22] Maschler, Solan, and Zamir, *Game Theory*. Monotonicity for SCFs.
