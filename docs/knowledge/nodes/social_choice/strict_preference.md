---
id: social_choice.strict_preference
title: Strict Preference
kind: definition
status: formalized
primary_topic: social_choice
topics:
  - social_choice
uses:
  - social_choice.preference
lean:
  modules:
    - EconCSLib.Foundation.Preference
  declarations:
    - strict
    - strict_transitive
    - Pref.lt
verification:
  definition: accepted
  proof: accepted
  alignment: aligned
tags:
  - social-choice
  - preference
---

# Strict Preference

Given a weak preference relation $R$ on a set $A$ of alternatives, the
induced *strict preference* is the relation

$$
a \succ_R b \iff R(a,b) \wedge \neg R(b,a).
$$

In Lean this is `strict R a b := R a b ∧ ¬ R b a`, with the notation-friendly
alias `Pref.lt p a b`.

## Transitivity

If $R$ is transitive then $\succ_R$ is transitive. Suppose $a \succ_R b$ and
$b \succ_R c$, so in particular $R(a,b)$ and $R(b,c)$, hence $R(a,c)$ by
transitivity of $R$. If we also had $R(c,a)$, transitivity would give
$R(b,a)$, contradicting $a \succ_R b$. Hence $a \succ_R c$. This is
`strict_transitive` in Lean.

The symmetry / antisymmetry-style properties of $\succ_R$ rely on totality of
$R$ and are used implicitly when arguing about ties in voting axioms.

## References

- [MSZ, Chapter 21] Maschler, Solan, and Zamir, *Game Theory*. Strict preference derived from a weak preference relation.
