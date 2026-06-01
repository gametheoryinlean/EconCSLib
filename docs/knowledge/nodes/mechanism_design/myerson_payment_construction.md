---
id: mechanism_design.myerson.payment_construction
title: Myerson Payment Construction (withMyersonPayment)
kind: definition
status: formalized
primary_topic: mechanism_design
topics:
- mechanism_design
- mechanism_design.myerson
uses:
- mechanism_design.myerson.payment_formula
- mechanism_design.transfer.single_parameter_transfer_layer
lean:
  modules:
  - EconCSLib.MechanismDesign.Auction.Myerson
  declarations:
  - withMyersonPayment
  - withMyersonPayment_quasiLinearUtility_eq
verification:
  definition: accepted
  proof: accepted
  alignment: aligned
tags:
- mechanism-design
- myerson
- single-parameter
- payment-construction
---

# Myerson Payment Construction

`withMyersonPayment` is the *constructive operator* that takes a
single-parameter allocation rule $x : (I \to \mathbb{R}) \to (I \to \mathbb{R})$
and returns the mechanism with Myerson payments
([[mechanism_design.myerson.payment_formula]]) attached.

If the input allocation rule is monotone, the resulting mechanism is
DSIC — this is the implementability half of the Myerson characterisation
([[mechanism_design.myerson.monotonicity_characterization]]).

## Quasi-linear utility after attachment

The companion lemma `withMyersonPayment_quasiLinearUtility_eq` gives the
explicit utility expression after Myerson payments are attached:
$$
u_i(b_i; b_{-i}) \;=\; v_i \cdot x_i(b_i, b_{-i})
                 \;-\; \int_0^{b_i} x_i(z, b_{-i})\, dz.
$$

When $b_i = v_i$ (truthful reporting), this collapses to
$\int_0^{v_i} (x_i(v_i, b_{-i}) - x_i(z, b_{-i}))\, dz \ge 0$ whenever
$x_i$ is monotone in its first argument — yielding both DSIC (truthful
reporting is best) and ex-post IR (utility is non-negative).

## Where this sits

- *Definition layer*: this node. `withMyersonPayment` is the operator
  itself, and the utility-equality lemma is its definitional
  unfolding.
- *Characterisation layer*:
  [[mechanism_design.myerson.monotonicity_characterization]] proves
  monotone $\Leftrightarrow$ implementable using this operator.
- *Formula layer*: [[mechanism_design.myerson.payment_formula]] gives
  the Myerson payment integral itself.

## References

- [AGT Chapter 9, §9.5.4] Nisan, Roughgarden, Tardos, and Vazirani,
  *Algorithmic Game Theory*. Single-parameter Myerson payment
  attachment.
- Myerson, R. B. (1981). "Optimal Auction Design".
  *Math. Oper. Res.* 6: 58–73.
