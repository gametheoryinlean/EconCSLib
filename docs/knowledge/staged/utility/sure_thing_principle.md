---
id: foundation.utility.sure_thing_principle
title: Sure Thing Principle
kind: theorem
status: staged
uses:
  - foundation.utility.vnm_axioms
lean:
  modules:
    - EconCSLib.Foundation.Utility.VNMAxioms
  declarations:
    - VNM.sure_thing_principle
verification:
  statement: accepted
  proof: accepted
  alignment: aligned
tags:
  - utility
  - vnm
  - independence
---

# Sure Thing Principle

The sure-thing principle says that a common consequence in a lottery mixture
does not affect strict preference between the non-common parts.

If independence holds, then for any lotteries $L_1,L_2,L_3,L_4$ and
$\alpha\in[0,1]$,
$$
  [\alpha L_1,(1-\alpha)L_3] \succ
  [\alpha L_2,(1-\alpha)L_3]
$$
if and only if
$$
  [\alpha L_1,(1-\alpha)L_4] \succ
  [\alpha L_2,(1-\alpha)L_4].
$$

## Proof Sketch

When $\alpha=0$, both sides compare a lottery with itself and strict preference
is impossible. When $\alpha>0$, apply independence once to remove $L_3$ and once
to insert $L_4$.

## References

- [MSZ, Chapter 2, Exercise 2.12] Maschler, Solan, and Zamir, *Game Theory*. The sure-thing principle follows from independence.
