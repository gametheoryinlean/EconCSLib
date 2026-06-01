---
id: math.fixed_point.brouwer_simplex
title: Brouwer Fixed Point Theorem For A Simplex
kind: theorem
status: proved
primary_topic: math
topics:
  - math
  - math.fixed_point
uses:
  - math.fixed_point.scarf_lemma
verification:
  statement: accepted
  proof: accepted
  alignment: aligned
tags:
  - fixed-point
  - brouwer
lean:
  repository: econcslib
  modules:
    - EconCSLib.Math.FixedPoint.Brouwer
  declarations:
    - Brouwer
---

# Brouwer Fixed Point Theorem For A Simplex

Every continuous map
$$
  f:\Delta\to\Delta
$$
from a simplex to itself has a fixed point.

## References

- [MFoGT, Cor. 4.11.2] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Continuous self-map of a simplex has a fixed point.
