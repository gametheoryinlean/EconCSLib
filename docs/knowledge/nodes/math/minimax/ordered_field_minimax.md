---
id: math.minimax.ordered_field_minimax
title: Ordered-Field Minimax Statement
kind: theorem
status: formalized
primary_topic: math
topics:
  - math
  - math.minimax
uses:
  - game_theory.strategic_game.zero_sum.von_neumann_minimax
lean:
  modules:
    - EconCSLib.Math.Minimax.Minimax
    - EconCSLib.Math.Minimax.SkewSymmetric
  declarations:
    - Minimax.minimax
    - SkewSymmetric.optimal
source:
  spans:
    - artifact: mfogt
      locator: "Chapter 2, Section 2.3, paragraph after the proof of Theorem 2.3.1"
      format: section
      note: "Ordered-field generalization via finite weak linear inequalities"
verification:
  statement: accepted
  proof: accepted
  alignment: aligned
generality:
  reviewed: true
  prompt: "Is this stronger than the ℝ-version closed by Loomis?"
  verdict: "Yes — it works over any linearly ordered field (e.g. ℚ, ℝ, ℝ((ε)), ...). Proved sorry-free as `Minimax.minimax` by von Neumann symmetrisation: embed the game in a skew-symmetric matrix whose value-0 optimal strategy exists by the Theorem of the Alternative (`SkewSymmetric.optimal`) — a pure feasibility fact, needing no compactness and no order-completeness."
tags:
  - zero-sum
  - minimax
  - ordered-field
---

# Ordered-Field Minimax Statement

The finite minimax theorem admits an ordered-field form: if the payoff
matrix has entries in an ordered field and the proof is carried out
algebraically through finitely many weak linear inequalities, then the
value and optimal mixed strategies can be taken over that ordered field.

*Proof.* Use an algebraic proof route for finite minimax, such as the
linear-programming route, whose steps are finite systems of weak
linear inequalities, pivot operations, and normalisations by positive
elements. These operations make sense over any ordered field. The terminal
inequalities are precisely the two minimax optimality systems, so the
extracted mixed strategies and value lie in the same ordered field as the
matrix entries.

The Lean theorem is `Minimax.minimax`, polymorphic in
`[Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]`, proved **sorry-free**
(axioms: `propext`, `Classical.choice`, `Quot.sound`). The route is von
Neumann symmetrisation: shift the game positive, embed it in the
skew-symmetric matrix on `I ⊕ J ⊕ Unit`, and read the optimal `(x, y, v)`
off the value-0 optimal strategy of that skew game — which exists by the
Theorem of the Alternative (`SkewSymmetric.optimal`), a pure feasibility
statement needing no LP optimum / order-completeness. The ℝ-specialisation
also follows from the Loomis route
([[node:game_theory.strategic_game.zero_sum.von_neumann_minimax]]).

## References

- [MFoGT, Chapter 2, Section 2.3, paragraph after the proof of Thm. 2.3.1] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Ordered-field generalization via finite weak linear inequalities.
