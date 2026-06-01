---
id: social_choice.fair_division.divisible.ds_step
title: Dubins–Spanier Inductive Step
kind: lemma
status: staged
primary_topic: social_choice
topics:
  - social_choice
  - social_choice.fair_division
  - social_choice.fair_division.divisible
  - social_choice.fair_division.divisible.dubins_spanier
uses:
  - social_choice.fair_division.divisible.cut_exists
  - social_choice.fair_division.divisible.envy_free
lean:
  modules:
    - EconCSLib.SocialChoice.FairDivision.Divisible.DubinsSpanier
  declarations:
    - SocialChoice.FairDivision.Divisible.dubinsSpanierProportional
verification:
  statement: accepted
  proof: accepted
  alignment: aligned
tags:
  - fair-division
  - divisible
  - dubins-spanier
  - proportional
  - moving-knife
---

# Dubins–Spanier Inductive Step

The Dubins–Spanier moving-knife algorithm builds a proportional allocation
on $n$ agents by induction. The key construction is an inductive
proposition

$$
P(n) \;\;\text{is}\;\;
\bigl(\forall\ \mu : \mathrm{Fin}\ n \to \mathrm{Measure}\ I,\
\text{prop-conditions}\bigr)
\;\Rightarrow\;
\exists A : \mathrm{Allocation}\ (\mathrm{Fin}\ n)\ I,\
\mathrm{IsAllocation}\ A \wedge \mathrm{IsProportional}\ n\ \mu\ A,
$$

proved by induction on $n$ in
`SocialChoice.FairDivision.Divisible.dubinsSpanierProportional`. The
proof uses three concrete pieces:

## Algorithm shape

1. **Threshold step.** For each remaining agent $i$, find $t_i \in I$ with
   $\mu_i([0, t_i]) = \mu_i(I)/n$ via the IVT lemma
   ([[social_choice.fair_division.divisible.cut_exists]]).

2. **Argmin selection.** Let $i^* = \arg\min_i t_i$ and $t^* = t_{i^*}$.
   Assign agent $i^*$ the piece $[0, t^*]$.

3. **Recurse.** Restrict the remaining agents $j \ne i^*$ to
   $(t^*, 1]$ and apply the algorithm recursively with $n - 1$ agents.

## Why proportionality is preserved

- **The selected agent.** $\mu_{i^*}([0, t^*]) = \mu_{i^*}(I) / n$ by
  the threshold construction. ✓

- **Each remaining agent $j$.** $t^* \le t_j$ by argmin, so
  $\mu_j([0, t^*]) \le \mu_j(I)/n$ by monotonicity of the CDF.
  Hence
  $$
  \mu_j((t^*, 1]) \;=\; \mu_j(I) - \mu_j([0, t^*]) \;\ge\; \frac{n-1}{n}\,\mu_j(I).
  $$
  Inductively, the recursive call on $n - 1$ agents on the remaining
  interval yields each $j$ a piece worth at least $1/(n-1)$ of their
  *remaining* value, which (combined with the bound above) is at least
  $\mu_j(I)/n$. ✓

## Lean implementation notes

The Lean proof uses `Fin.insertNth` to fold the recursively-produced
sub-allocation back into a full allocation over `Fin n`. Partition
validity (measurability, disjointness, cover) and proportionality are
established by `ennreal_prop_step` — a packaged induction-step lemma
that combines the moving-knife construction with monotonicity bounds in
`ENNReal`.

All sorries are closed; the resulting public theorem is
[[social_choice.fair_division.divisible.dubins_spanier_proportional]].

## References

- Dubins, L. E. and Spanier, E. H. (1961). "How to Cut a Cake Fairly". *Amer. Math. Monthly* 68: 1–17.
- [AGT Chapter 13] Nisan, Roughgarden, Tardos, and Vazirani, *Algorithmic Game Theory*. Moving-knife procedures.
