---
id: game_theory.strategic_game.zero_sum.continuous.intersection_lemma
title: Intersection Lemma
kind: lemma
status: admitted
primary_topic: game_theory.zero_sum
topics:
  - game_theory.zero_sum
  - game_theory.zero_sum.continuous
source:
  spans:
    - artifact: mfogt
      locator: "Lemma 3.2.1"
      format: section
      note: "Convex compact intersection lemma used in Sion's theorem"
verification:
  statement: accepted
  proof: accepted
tags:
  - zero-sum
  - convexity
  - separation
---

# Intersection Lemma

Let $C_1,\ldots,C_n$ be nonempty convex compact subsets of a Euclidean space.
Assume that $\bigcup_{i=1}^n C_i$ is convex and that every intersection of
$n-1$ of the sets is nonempty:
$$
  \bigcap_{i\ne j} C_i\ne\emptyset
  \quad\text{for every }j=1,\ldots,n.
$$
Then
$$
  \bigcap_{i=1}^n C_i\ne\emptyset.
$$

*Proof.* The proof is by induction on $n$. The case $n=2$ uses strict separation of two
disjoint compact convex sets: if $C_1$ and $C_2$ were disjoint, their convex union
would have to cross the separating hyperplane, contradiction. For the induction
step, separate $C_n$ from $\bigcap_{i<n}C_i$ and intersect the other sets with the
separating hyperplane. The induction hypothesis applied in the hyperplane gives a
point that contradicts strict separation.

## References

- [MFoGT, Lem. 3.2.1] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Convex compact intersection lemma used in Sion's theorem.
