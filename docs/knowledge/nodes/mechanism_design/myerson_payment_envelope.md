---
id: mechanism_design.myerson.payment_envelope
title: Myerson Payment Envelope Lemmas
kind: lemma
status: proved
primary_topic: mechanism_design
topics:
- mechanism_design
- mechanism_design.myerson
uses:
- mechanism_design.transfer.single_parameter_transfer_layer
- mechanism_design.myerson.payment_formula
lean:
  modules:
  - EconCSLib.MechanismDesign.Auction.Myerson
  declarations:
  - payment_sandwich
  - payment_difference_bound
verification:
  statement: accepted
  proof: accepted
  alignment: aligned
tags:
- mechanism-design
- myerson
- envelope
- single-parameter
---

# Myerson Payment Envelope Lemmas

Two technical lemmas central to Myerson's envelope-theorem argument for
single-parameter mechanisms.

## `payment_sandwich`

For a DSIC single-parameter mechanism with allocation rule $x$ and
payments $p$, the payment $p_i(b)$ at bid $b$ is **sandwiched** between
the upper and lower integral bounds determined by $x_i$:
$$
\int_0^{b_i} x_i(z, b_{-i}) \, dz \;\le\; p_i(b) - p_i(b_0)
  \;\le\; \int_0^{b_i} x_i(z, b_{-i}) \, dz
$$
where $b_0$ is the zero-bid reference. The collapsed equality is the
Myerson payment formula
([[mechanism_design.myerson.payment_formula]]).

## `payment_difference_bound`

A Lipschitz-style bound on the payment difference between two bids:
$$
|p_i(b) - p_i(b')| \;\le\; \int \big|x_i(z, b_{-i}) - x_i(z, b'_{-i})\big| \, dz,
$$
controlling how the payment moves when the bid profile changes.

## Where these are used

- **Implementability proof** (`withMyersonPayment_isDSIC_of_isMonotone`,
  in [[mechanism_design.myerson.monotonicity_characterization]]):
  uses `payment_sandwich` to verify the Myerson-payment-attached
  mechanism satisfies DSIC.
- **Payment-formula recovery**
  (`payment_formula_of_isDSIC_of_zeroNormalized`,
  in [[mechanism_design.myerson.payment_formula]]): uses
  `payment_difference_bound` to show that any DSIC zero-normalised
  payment equals the Myerson integral.

These are the technical mid-steps in the envelope-theorem derivation
of the Myerson characterisation.

## References

- [AGT Chapter 9, §9.5.4, Thm 9.36] Nisan, Roughgarden, Tardos, and
  Vazirani, *Algorithmic Game Theory*. Envelope characterisation of
  single-parameter DSIC mechanisms.
- Myerson, R. B. (1981). "Optimal Auction Design".
  *Math. Oper. Res.* 6: 58–73. Original envelope-theorem framing.
