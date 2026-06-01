---
id: math.order.sup_inf_choice_function_identity
title: Sup-Inf Choice Function Identity
kind: lemma
status: staged
verification:
  statement: accepted
  proof: gap
tags:
  - order
  - minimax
---

# Sup-Inf Choice Function Identity

Let $f:S\times T\to\mathbb R$, where $S$ and $T$ are arbitrary nonempty sets.
Let $B$ be the set of all maps $\beta:S\to T$. Then
$$
  \sup_{s\in S}\inf_{t\in T} f(s,t)
  =
  \inf_{\beta\in B}\sup_{s\in S} f(s,\beta(s)).
$$

## References

- [MFoGT, Section 3.5, Exercise 5] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Sup-inf identity using choice functions from S to T.
