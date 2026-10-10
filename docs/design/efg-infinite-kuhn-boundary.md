# Infinite-Horizon Kuhn Boundary

This note records the strongest Kuhn-style theorem currently proved beyond
the finite-information package. It is a scope contract, not a claim of an
unrestricted infinite-horizon equivalence.

## Hypothesis matrix

| Dimension | Implemented bounded theorem | Finite two-way Nash theorem | Unformalized analytic route |
|---|---|---|---|
| Players | finite, decidable equality | finite, decidable equality | finite initially |
| Pure-plan randomization | playerwise `FiniteLaw`; finite support and rational weights | same finite rational laws | countably supported PMF or arbitrary probability measure |
| Information states | represented and raw carriers may be infinite | represented decision coordinates finite for every player; raw carriers unrestricted | countable or standard Borel |
| Abstract actions | arbitrary types carrying finite rational laws | arbitrary dependent fibers carrying finite rational laws | standard-Borel measurable fibers |
| Recall | explicit `RecallCertificate` | `FiniteKuhnHypotheses.recallCertificate` | measurable perfect-recall certificate |
| Horizon | every finite fuel, with no common terminal bound | every finite fuel | complete infinite path law |
| Chance | history-indexed `FiniteLaw` chance laws | same finite rational laws | measurable probability kernel |
| Conditioning | finite remembered decision list in a `FiniteLaw` | same, plus finite-table deviation sampling | regular conditional probabilities |
| Null information | caller-supplied `offPath` behavioral profile, used when the posterior is `none` | same | version policy must be explicit |
| Conclusion | `FiniteLaw.Equivalent` of bounded complete-history laws, mixed to behavioral | realization plus behavioral-deviation coverage and Nash equivalence | equality of complete path laws |

## Implemented theorem

`ObservedChanceGame.finiteLawMixedToBehavioral_boundedHistoryLaw`
uses a root-scoped `RecallCertificate`. It permits infinitely many declared
information states and arbitrarily long games, but fixes one continuation root
and one finite fuel. The result is `FiniteLaw.Equivalent` of the complete
history distributions at that fuel. Sparse atom lists need not be equal.

The mixed plans, local actions, and chance laws all have finite support and
rational weights. Infinite ambient carriers and arbitrarily large finite fuel
do not supply a theorem for arbitrary countably supported, real-weighted PMFs.

The direction is mixed to behavioral. The reverse construction needs a law on
complete contingent tables. The current implementation obtains it only from
finite information-state products; therefore no two-way Nash claim is made at
the broader boundary.

`finiteKuhn_boundedHistoryLaw_specialization` proves that
`FiniteKuhnHypotheses` supplies the recall certificate required by the broader
law theorem. Its separate finiteness field is consumed by deviation coverage,
not by this mixed-to-behavioral law equality.

## Why this is not an infinite-path theorem

Agreement for each finite fuel is not yet packaged as equality of one common
projective-limit path law. The missing assembly must connect the
root-conditioned behavioral kernels to the existing analytic infinite
executor and prove consistency of all finite marginals. For countably supported
PMFs, one must first extend the finite-law input and conditioning/execution
realization. For arbitrary pure-strategy measures the route additionally needs
measurable evaluation and suitable disintegration.

## Literature boundary

Kuhn's original equivalence theorem is a finite perfect-recall result
([Kuhn 1953, §4 and Thm. 4](https://doi.org/10.1515/9781400829156-011)).
It supports the finite theorem and the conditioning pattern, but not an
unrestricted extension to infinite histories, arbitrary measures, or
non-atomic action spaces. The implemented broader theorem is therefore
classified as an EconCSLib bounded-law generalization under a standard recall
certificate.
