---
id: social_choice.fair_division.indivisible.efx_singleton_bundle
title: EFX from a Singleton-Bundle Sufficient Condition
kind: lemma
status: staged
primary_topic: social_choice
topics:
  - social_choice
  - social_choice.fair_division
  - social_choice.fair_division.indivisible
uses:
  - social_choice.fair_division.indivisible.efx
lean:
  modules:
    - EconCSLib.SocialChoice.FairDivision.Indivisible.EFX
  declarations:
    - SocialChoice.FairDivision.Indivisible.isEFX_of_singleton_bundle
verification:
  statement: accepted
  proof: accepted
  alignment: aligned
tags:
  - fair-division
  - indivisible
  - efx
  - singleton
---

# EFX from a Singleton-Bundle Sufficient Condition

**Lemma.** In a 2-agent ($\mathrm{Fin}\ 2$) allocation where agent $i$'s
bundle is *exactly* a singleton $\{g\}$, the EFX-style "remove any item"
inequality for agent $j$ against $A(i)$ reduces to the empty-bundle
comparison: assuming $v_j(\emptyset) \le v_j(A(j))$,
$$
\forall h \in A(i),\ v_j(A(i) \setminus \{h\}) \le v_j(A(j)).
$$

In Lean: `SocialChoice.FairDivision.Indivisible.isEFX_of_singleton_bundle`.
The signature is pair-specific:
$\mathrm{Fin}\ 2$, fixed agents $i, j$, and the hypothesis $A(i) = \{g\}$
as data.

## Proof

The only element of $A(i)$ is $g$, so the universal becomes
"$v_j(A(i) \setminus \{g\}) \le v_j(A(j))$", which simplifies to
$v_j(\emptyset) \le v_j(A(j))$ — exactly the supplied hypothesis. The
lemma takes the relevant nonnegativity hypothesis as a parameter rather
than baking it into a typeclass.

## Significance

This is a small *pair-helper* used inside the 2-agent EFX existence
construction
([[social_choice.fair_division.indivisible.efx_exists_two_agents]]) to
discharge one side of the EFX inequality when one agent's bundle has
collapsed to a singleton. It is **not** a stand-alone "singleton
bundles automatically give EFX" theorem.

A generic "every bundle has cardinality $\le 1 \Rightarrow$ EFX"
statement is not formalised in the library; if needed, it would be a
short corollary using one application of this lemma per envy direction.

## References

- [AGT Chapter 11] Nisan, Roughgarden, Tardos, and Vazirani, *Algorithmic Game Theory*. EFX special cases.
