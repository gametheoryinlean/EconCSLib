---
id: social_choice.voting.unanimity
title: Unanimity (Pareto Axiom)
kind: definition
status: formalized
primary_topic: social_choice
topics:
  - social_choice
  - social_choice.voting
uses:
  - social_choice.voting.swf
  - social_choice.voting.scf
  - social_choice.strict_preference
lean:
  modules:
    - EconCSLib.SocialChoice.Voting.Basic
  declarations:
    - SocialChoice.Voting.SWF.Unanimity
    - SocialChoice.Voting.Unanimity
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
tags:
  - social-choice
  - voting
  - axiom
  - pareto
---

# Unanimity (Pareto Axiom)

Unanimity asks that an aggregation rule respect unanimous individual strict
rankings. Two parallel versions:

**SWF unanimity.** A social welfare function $F$ is *unanimous* if for every
profile $P$ and every pair $a, b \in A$,
$$
\bigl(\forall i \in N,\ a \succ_{P_i} b\bigr)
\Rightarrow a \succ_{F(P)} b.
$$

**Voting-rule unanimity (weak Pareto).** A voting rule $f$ is *unanimous* if
no unanimously dominated alternative is ever selected: for every profile $P$
and every pair $a, b \in A$,
$$
\bigl(\forall i \in N,\ a \succ_{P_i} b\bigr)
\Rightarrow b \notin f(P).
$$
For a resolute rule this recovers the single-winner statement $G(P) = a$
whenever every voter ranks $a$ strictly first.

In Lean these are `SocialChoice.Voting.SWF.Unanimity` and
`SocialChoice.Voting.Unanimity`, defined in terms of the bundled strict
preference [[social_choice.strict_preference]].

Unanimity is the weakest Paretian axiom in this hierarchy. It is the hypothesis
for both Arrow's impossibility ([[social_choice.voting.arrow_impossibility]])
and Muller-Satterthwaite ([[social_choice.voting.muller_satterthwaite]]).

## References

- [MSZ 21.8, 21.26] Maschler, Solan, and Zamir, *Game Theory*. Unanimity / Pareto axioms.
