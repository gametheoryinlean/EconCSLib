---
id: game_theory.strategic_game.correlated.correlated_equilibrium_convex_compact
primary_topic: game_theory.strategic_game
topics:
  - game_theory.strategic_game
  - game_theory.strategic_game.bayesian_correlated
title: Correlated Equilibrium Set Is a Polytope
kind: theorem
status: staged
uses:
  - game_theory.strategic_game.correlated.correlated_equilibrium
  - game_theory.strategic_game.correlated.obedience_condition
lean:
  modules:
    - EconCSLib.Math.Convex.FinitePolyhedron
    - EconCSLib.GameTheory.StrategicGame.CorrelatedEq
  declarations:
    - EconCSLib.Convex.FiniteLinearInequalitySet
    - EconCSLib.Convex.finiteLinearInequalitySet_extremePoints_finite
    - EconCSLib.Convex.finiteLinearInequalitySet_eq_convexHull_finset
    - StrategicGame.expectedPayoff_contingentPlanExtension_eq_extendBy
    - StrategicGame.isMixedContingentPlanNashEquilibrium_iff_behavioral
    - StrategicGame.mixedContingentPlanCorrelatedEquilibriumDistributions_eq_behavioral
    - StrategicGame.behaviorProfileToMixedContingentPlan_canonical_truthful
    - StrategicGame.mixedPlanCanonicalCorrelatedEquilibriumDistributions_eq_mixedPlanCED
    - StrategicGame.CEDFiniteLinearInequalitySet
    - StrategicGame.correlatedEquilibriumDistributions_eq_finiteLinearInequalitySet
    - StrategicGame.cedFiniteLinearInequalitySet_convex
    - StrategicGame.correlatedEquilibriumDistributions_image_convex
    - StrategicGame.correlatedEquilibriumDistributions_eq_convexHull_finset
    - StrategicGame.correlatedEquilibriumDistributions_image_isCompact
verification:
  statement: accepted
  proof: accepted
  alignment: aligned
tags:
  - strategic-game
  - correlated-equilibrium
  - convexity
  - compactness
  - polytope
---

# Correlated Equilibrium Set Is a Polytope

For a finite strategic-form game, write $A=\prod_i A_i$ for the finite set of
pure action profiles. The set $CED(G)$ of correlated-equilibrium distributions
is the subset of $\mathbb{R}^{A}$ cut out by
$$
  q(a)\ge 0,\qquad \sum_{a\in A}q(a)=1,
$$
together with the finitely many obedience inequalities
$$
  \sum_{a_{-i}}q(s_i,a_{-i})
    \bigl(g_i(s_i,a_{-i})-g_i(t_i,a_{-i})\bigr)\ge 0
$$
for every player $i$ and every pair $s_i,t_i\in A_i$.

Consequently $CED(G)$ is a bounded polyhedron, hence a polytope. Equivalently,
there is a finite set $V\subseteq\mathbb{R}^{A}$ such that
$$
  CED(G)=\operatorname{conv}(V).
$$
In particular, $CED(G)$ is convex and compact.

## Proof Sketch

The simplex constraints make the feasible set bounded, while the obedience
constraints and simplex constraints form a finite system of affine weak
inequalities (with the mass equality written as two inequalities if needed).
The finite-dimensional bounded-polyhedron theorem then yields a finite vertex
set whose convex hull is the feasible set.

## Formalization status

`FinitePolyhedron.lean` proves that the extreme points of a finite real linear
inequality system are finite and that every bounded such system is the convex
hull of a finite set. `CorrelatedEq.lean` encodes nonnegativity, total mass one,
and obedience as one finite system, proves boundedness from containment in the
probability simplex, and applies the general theorem. It also formalizes the
source's mixed complete-contingent-plan extension and proves that its expected
payoffs, Nash equilibria, and induced outcome set agree with the behavioral
presentation used by the linear characterization. Thus the model bridge and
the exact finite convex-hull conclusion are verified. In the canonical model,
the product coupling of truthful signalwise point masses is proved equal to
the point mass on the identity contingent-plan profile, and the resulting
source-literal mixed-plan canonical-set equality is exposed directly.
Compactness is exposed by
`correlatedEquilibriumDistributions_image_isCompact`.

## References

- [MSZ, Chapter 8, Thm. 8.9] Maschler, Solan, and Zamir, *Game Theory*. The set of correlated equilibria is convex and compact.
- [MFoGT, Cor. 7.2.8] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. The correlated-equilibrium distribution set is a polytope, equivalently the convex hull of finitely many points.
