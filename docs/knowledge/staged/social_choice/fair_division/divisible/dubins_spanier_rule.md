---
id: social_choice.fair_division.divisible.dubins_spanier_rule
title: Dubins–Spanier as a Rule on Measure Instances
kind: theorem
status: staged
primary_topic: social_choice
topics:
  - social_choice
  - social_choice.fair_division
  - social_choice.fair_division.divisible
  - social_choice.fair_division.divisible.dubins_spanier
uses:
  - social_choice.fair_division.divisible.dubins_spanier_proportional
  - social_choice.fair_division.solution_concept
lean:
  modules:
    - EconCSLib.SocialChoice.FairDivision.Divisible.DubinsSpanier
  declarations:
    - SocialChoice.FairDivision.Divisible.dubinsSpanier_exists_proportional_allocation
    - SocialChoice.FairDivision.Divisible.dubinsSpanierRule_isProportional
verification:
  statement: accepted
  proof: accepted
  alignment: aligned
tags:
  - fair-division
  - divisible
  - dubins-spanier
  - rule
  - proportional
---

# Dubins–Spanier as a Rule on Measure Instances

Two bundled-instance reformulations of
[[social_choice.fair_division.divisible.dubins_spanier_proportional]]:

## Existence at the instance level

`dubinsSpanier_exists_proportional_allocation` repackages the bare
theorem as a `Divisible.MeasureInstance`-keyed existence statement:
$$
\forall n \ge 1,\ \forall I : \mathrm{MeasureInstance}\ (\mathrm{Fin}\ n)\ \mathrm{[0,1]}\ \text{(non-atomic finite)},\
\exists A,\ I.\mathrm{feasible}\ A \wedge I.\mathrm{IsProportional}\ n\ A.
$$

The translation is mechanical: an `Instance` exposes the measure
family $I.\mathrm{measure}$, and the underlying theorem applies to that
family.

## Rule form

`dubinsSpanierRule_isProportional` exhibits Dubins–Spanier as a *rule* in
the sense of [[social_choice.fair_division.solution_concept]] — a
function that takes a measure instance and returns a feasible allocation
together with a proof that the returned allocation is proportional.

The rule is *non-canonical*: the construction depends on choosing one of
the proportional witnesses (selecting which agent to assign first at the
moving-knife step). Different selection rules give different outputs;
all are proportional.

## Why both

The proof of existence is the same theorem in all three forms, but
exposing it as

- a bare existential (`dubinsSpanierProportional`),
- an instance-level existential (`dubinsSpanier_exists_proportional_allocation`),
- a deterministic rule (`dubinsSpanierRule_isProportional`),

lets downstream callers pick whichever fits their needs (proof
ergonomics, instance polymorphism, or computability).

## References

- Dubins, L. E. and Spanier, E. H. (1961). "How to Cut a Cake Fairly". *Amer. Math. Monthly* 68: 1–17.
