# Chapter 7 Formalization Audit

## Scope and standard of comparison

This note records a semantic audit of the currently implemented parts of
Chapter 7 of Laraki, Renault, and Sorin, *Mathematical Foundations of Game
Theory* (MFoGT), cross-checked against the corresponding treatments in
Maschler, Solan, and Zamir, *Game Theory* (MSZ). MSZ does not place the same
material in one chapter: correlated equilibrium is in Chapter 8, common-prior
Bayesian games are in Chapter 9, and approachability/no-regret is in Chapter
14. The declaration-by-declaration audit covers MFoGT Sections 7.2.2-7.2.5,
7.3.1-7.3.4, and 7.4.1-7.4.2 as represented in:

- `EconCSLib/GameTheory/StrategicGame/CorrelatedEq.lean`;
- `EconCSLib/Math/Probability/Blackwell.lean`;
- `EconCSLib/GameTheory/StrategicGame/NoRegret/Basic.lean`;
- `EconCSLib/GameTheory/StrategicGame/NoRegret/External.lean`;
- `EconCSLib/GameTheory/StrategicGame/NoRegret/Internal.lean`;
- `EconCSLib/GameTheory/StrategicGame/NoRegret/Calibration.lean`;
- `EconCSLib/GameTheory/StrategicGame/NoRegret/EmpiricalDistribution.lean`;
- `EconCSLib/GameTheory/StrategicGame/NoRegret/Process.lean`;
- `EconCSLib/Examples/StrategicGame/HannanThreeCycle.lean`;
- `EconCSLib/GameTheory/StrategicGame/BayesianGame/Basic.lean`;
- `EconCSLib/GameTheory/StrategicGame/BayesianGame/Continuous.lean`;
- `EconCSLib/GameTheory/StrategicGame/BayesianGame/WarOfAttrition.lean`;
- `EconCSLib/GameTheory/StrategicGame/BayesianGame/WarOfAttrition/CompactApproximation.lean`;
- `EconCSLib/GameTheory/StrategicGame/ZeroSum/StochasticMatrix.lean`.

The rest of the chapter is included in the coverage accounting below so that
"Chapter 7 audit" is not mistaken for a claim that every example, exercise, or
comment has been formalized.

## Chapter coverage boundary

| MFoGT section | Current repository coverage | Audit conclusion |
| --- | --- | --- |
| 7.1 Introduction | No dedicated declarations | Narrative overview only; no theorem attribution to check |
| 7.2.1 Examples | No dedicated examples | Battle of the Sexes and Chicken correlation examples remain unformalized |
| 7.2.2-7.2.5 | `CorrelatedEq.lean` | Audited declaration by declaration; statement repairs recorded below |
| 7.2.6 Comments | No dedicated declarations | Minimax existence route and the displayed examples remain unformalized |
| 7.3.1-7.3.4 | `Blackwell.lean`; `NoRegret/Basic.lean`; `NoRegret/External.lean`; `NoRegret/Internal.lean`; `NoRegret/Calibration.lean`; `NoRegret/EmpiricalDistribution.lean`; `NoRegret/Process.lean`; `StochasticMatrix.lean`; `HannanThreeCycle.lean` | Audited declaration by declaration. Every numbered definition, theorem, lemma, proposition, and Example 7.3.14 has a source-aligned declaration or example; canonical generated-process theorems are available for Propositions 7.3.4, 7.3.7, 7.3.10, and 7.3.18. Remarks 7.3.8 and 7.3.11 remain explanatory prose rather than formal theorem statements. |
| 7.4.1-7.4.2 | `BayesianGame/Basic.lean`; `BayesianGame/Continuous.lean`; `BayesianGame/WarOfAttrition.lean`; `BayesianGame/WarOfAttrition/CompactApproximation.lean`; Bayesian knowledge nodes | Audited declaration by declaration. The finite primitive/reduced model and finite existence theorem are proved. Standard-Borel random-seed and disintegration correspondences, the nonatomic equilibrium definition, and all three parts of the continuous war-of-attrition example are proved with their analytic side conditions explicit. The bounded-support part derives its equilibrium, quantile coupling, shrinking-support estimate, and weak convergence rather than storing them as certificates. |
| 7.5 Exercises | No Chapter 7 exercise module | Outside current implementation; no coverage claim is made |
| 7.6 Comments | No dedicated declarations | Narrative and literature discussion only |

## Cross-source map and comparison rule

| MFoGT Chapter 7 material | MSZ cross-check | Comparison used in this audit |
| --- | --- | --- |
| Sections 7.2.2-7.2.5, information extensions and correlated distributions | Section 8.2, especially Definition 8.4, Theorem 8.5, Definition 8.6, Theorems 8.7 and 8.9, and Remark 8.10 | Exact agreement is required for recommendation strategies, unnormalized obedience (including null recommendations), Nash-product inclusion, and finite convex/compact/polytope conclusions. |
| Sections 7.3.1-7.3.4, Blackwell and no-regret procedures | Chapter 14, especially Definition 14.42, Theorem 14.44, and Equations (14.101)-(14.103) | MSZ uses `realized - alternative` and the nonnegative orthant; MFoGT and Lean use the negated vector and the nonpositive orthant. Claims are aligned only after recording this explicit sign isometry. MSZ does not supply the internal-regret/calibration/CED-convergence sequence audited from MFoGT. |
| Sections 7.4.1-7.4.2, Bayesian games | Section 9.4, especially Equations (9.58)-(9.65), Definitions 9.46, 9.49, 9.50, and Theorems 9.51-9.53 | The Lean model is the constant-action-family submodel of MSZ and permits null types. MSZ's ex-ante Nash/interim Bayesian terminology and full-type-support assumption are stated explicitly. The Harsanyi strategic form in Lean is not misidentified as MSZ's separate agent-form game. |

The MSZ comparison is a semantic cross-calibration, not a claim that Chapter 7
of MFoGT and Chapters 8, 9, and 14 of MSZ have identical scope. Where one book
is strictly more general or uses a different quantifier convention, the
difference is recorded as a coverage boundary rather than silently erased.

The audit distinguishes three questions:

1. whether a Lean theorem is correct under its formal hypotheses;
2. whether its definitions denote the same game-theoretic object as the cited
   source;
3. whether its documentation claims more source coverage than the theorem
   actually supplies.

No proved Lean theorem in the audited code has a known counterexample under
its stated formal definitions. The serious findings below are semantic-model
gaps or incomplete source coverage, not contradictions derived inside Lean.

## Implemented alignment

The Section 7.2 alignment includes:

- `PureContingentPlan` and `contingentPlanExtension` encode MFoGT Definition
  7.2.2 literally: pure strategies are complete signal-to-action maps;
- `MixedContingentPlan` is a probability distribution over complete plans;
- `ExtendedStrategy` is signal-contingent and simplex-valued;
- `extendedActionProbability` is the conditional product probability from the
  finite formula in MFoGT;
- `inducedDistribution` averages those conditional product probabilities under
  the common prior;
- `MixedContingentPlanCorrelatedEquilibriumDistributions` records the literal
  mixed-plan union in MFoGT Definition 7.2.4;
- `mixedContingentPlanCorrelatedEquilibriumDistributions_eq_behavioral` proves
  that this is exactly `CorrelatedEquilibriumDistributions`, the finite
  behavioral union; `NashCorrelatedEquilibriumDistributions` is only an
  explicit synonym for that behavioral Nash presentation;
- `SignalwiseCorrelatedEquilibriumDistributions` separately names the ex-post
  presentation, and `correlatedEquilibriumDistributions_eq_signalwise` proves
  that it is the same set;
- `IsMixedPlanCorrelatedEquilibrium` denotes mixed Nash equilibrium of the
  source's complete-plan extension; `IsCorrelatedEquilibrium` denotes Nash
  equilibrium of its behavioral realization, while
  `IsSignalwiseCorrelatedEquilibrium` states mixed best response after every
  signal;
- `expectedPayoff_contingentPlanExtension_eq_extendBy` and
  `isMixedContingentPlanNashEquilibrium_iff_behavioral` prove equality of
  payoffs and equilibrium equivalence between the two representations;
- `isExtendedNashEquilibrium_iff_signalwise` proves the finite ex-ante/ex-post
  equivalence stated after MFoGT Definition 7.2.2, and
  `isSignalwiseCorrelatedEquilibrium_iff_actionwise` connects that condition to
  the unnormalized actionwise obedience inequalities;
- the same equivalence is proved between the source's Nash-based
  `CanonicalCorrelatedEquilibriumDistributions` and
  `SignalwiseCanonicalCorrelatedEquilibriumDistributions`;
- canonical truthful behavior is represented by point-mass mixed actions;
- `canonicalCorrelatedEquilibriumDistributions_eq_correlatedEquilibriumDistributions`
  and `mem_correlatedEquilibriumDistributions_iff_obedience` now state MFoGT
  Theorems 7.2.6 and 7.2.7 against the Nash-based sets;
- `isExtendedNashEquilibrium_trivial_iff_isMixedNashEq` proves that trivial
  information recovers ordinary mixed Nash equilibrium;
- `inducedDistribution_trivial_eq_piProduct` and
  `piProduct_mem_correlatedEquilibriumDistributions_of_isMixedNashEq` prove
  MSZ Equation (8.10) and Theorem 8.7 directly;
- `piProduct_mem_correlatedEquilibriumDistributions_of_mixedNashEquilibrium`
  connects the same conclusion to the all-mixed-deviations predicate returned
  by the library's Brouwer-based Nash existence theorem;
- `vertex_mem_correlatedEquilibriumDistributions_iff_isNashEquilibrium`
  closes the point-mass boundary in both directions, so the knowledge node for
  degenerate correlated equilibrium no longer relies on a profile-level
  definitional shorthand;
- the former proposition-only `HasCEDHRepresentation` wrapper has been replaced
  by an explicit ambient-vector set containing nonnegativity, total-mass, and
  finite linear obedience constraints;
- `correlatedEquilibriumDistributions_image_convex` proves the convexity noted
  after MFoGT Definition 7.2.4.

No placeholder proof was introduced. Both the former Nash/signalwise gap and
the mixed-complete-plan/behavioral-representation gap are closed. MFoGT
Corollary 7.2.8 is also complete for the source-aligned real model:
`finiteLinearInequalitySet_eq_convexHull_finset` proves the required bounded
finite H-to-V theorem, and
`correlatedEquilibriumDistributions_eq_convexHull_finset` applies it to obtain
the exact finite convex-hull representation of `CED(G)`. The completed theorem
and its prerequisites are tracked in the knowledge node
[`correlated_equilibrium_convex_compact.md`](../knowledge/staged/strategic_game/correlated_equilibrium_convex_compact.md).

The Section 7.3 alignment includes:

- `EconCSLib.Blackwell.blackwell_approach_closedConvex_ae` proves the full
  nonempty-closed-convex projection criterion of MFoGT Theorem 7.3.2 in any
  finite-dimensional real Hilbert space, while
  `blackwell_projectionDistance_tendsto_zero_ae` exposes the source-literal
  almost-sure distance-to-target limit;
- support-based predicates are explicitly named `IsRobustPathwise...` and are
  no longer presented as MFoGT's almost-sure strategy definitions;
- the probability-layer predicates and reusable conditional theorem names say
  `OnGeneratedProcessesAE`, while `NoRegret/Process.lean` separately constructs
  canonical Ionescu--Tulcea trajectory laws;
- the invariant-measure rule records that its `Classical.choose` selector is
  not known measurable on unrestricted real-valued histories; the canonical
  construction avoids this gap because the relevant action-history domains
  are finite and discrete;
- generated-process forms of MFoGT Propositions 7.3.4 and 7.3.7 are proved
  against every bounded finite-history predictable payoff rule;
- the generated-process regret-matching theorems are composed directly with
  the empirical-distribution identities for Propositions 7.3.13 and 7.3.16,
  so the public API also exposes the algorithm-to-target implications rather
  than only their two proof layers;
- the coordinatewise external-regret predicate is proved equivalent both to
  the finite maximum criterion and to convergence of that nonnegative maximum
  to zero, exactly as in MFoGT Definition 7.3.1;
- the coordinatewise internal-regret predicate is likewise proved equivalent
  to convergence to zero of the maximum positive entry of the finite regret
  matrix, making the whole-matrix consequence explicit;
- a generated-process form of Proposition 7.3.10 constructs an
  `epsilon`-calibrated forecast law against every finite-history predictable
  outcome rule, `ForecastGrid` enforces distinct forecast points, and
  `IsEpsilonCalibrated`/`IsEpsilonCalibratedAE` now expose Definition 7.3.9
  directly rather than only through the generated-process wrapper;
- `directCalibrationError_eq_calibrationError` proves that the source's direct
  empirical residual-vector formula is exactly the frequency-weighted
  conditional-frequency formula used by the calibration API, including unused
  forecast points, and
  `isEpsilonCalibrated_iff_directCalibrationError` exposes the resulting
  source-literal asymptotic predicate;
- the generated-process form of Proposition 7.3.18 constructs the joint law of
  independently randomized player procedures, proves every player's internal
  regret vanishes almost surely, and then proves convergence of the empirical
  distribution to `CED(G)` for every finite real-payoff game with nonempty
  action sets;
- `correlatedEquilibriumDistributions_nonempty_of_internalRegretProcess`
  formalizes the existence consequence stated after Proposition 7.3.18;
- Propositions 7.3.13, 7.3.16, and 7.3.18 are documented as consequences for
  already-realized paths or random processes, not as process-construction
  theorems;
- the ex-post helper versions of Propositions 7.3.17 and 7.3.18 retain their
  signalwise names, while `allPlayersNoInternalRegretSet_eq_CED` and
  `noInternalRegret_allPlayers_empiricalDistribution_approaches_CED` now expose
  the source's Nash-based targets;
- `noCRegretSet_subset_hannanSet` now formalizes the inclusion stated after
  MFoGT Definition 7.3.15;
- `hannanSets_zeroSum_marginals_optimal_and_payoff_eq_value` proves the
  zero-sum consequence following Proposition 7.3.13, including equality of
  correlated payoff, product-marginal payoff, and game value;
- `HannanThreeCycle.lean` formalizes Example 7.3.14: the diagonal distribution
  lies in both Hannan sets but violates a positive internal-comparison gain;
- the predictable-outcome calibration comments now distinguish an outcome
  fixed in the pre-randomization filtration from an outcome observed by the
  forecaster; the latter would give the wrong information structure.

The Section 7.4 alignment includes:

- `PrimitiveBayesianGame` represents the finite state space, state-dependent
  payoffs, signal maps, and behavioral strategies introduced in Section 7.4.1;
- `PrimitiveBayesianGame.toReduced` pushes the state prior to type profiles and
  conditions payoffs on each type-profile fiber;
- `toReduced_behavioralExpectedPayoff` and
  `toReduced_isBayesianEquilibrium` prove preservation of ex-ante payoffs and
  Bayesian equilibrium under that reduction;
- `conditionalInterimBehaviorPayoffOfMixedAction` gives the normalized
  own-type-conditioned payoff displayed in the source, and
  `isBayesianEquilibrium_iff_conditionalInterimBestResponses` proves the exact
  ex-ante/interim equivalence for positive-probability types;
- `interimBehaviorPayoffOfMixedAction_eq_sum_pure` proves linearity in the
  acting type's mixed action, and
  `isConditionalInterimBestResponse_iff_pureAction` closes the gap between the
  mixed-deviation predicate and the pure-action inequalities stated literally
  in MSZ Definition 9.49;
- `IsExAnteNashEquilibrium`, `IsInterimBayesianEquilibrium`, and
  `HasFullTypeSupport` expose the distinction in MSZ Definitions 9.46 and 9.49,
  while
  `isExAnteNashEquilibrium_iff_isInterimBayesianEquilibrium_of_fullTypeSupport`
  gives the reusable mixed-deviation specialization of MSZ Theorem 9.53, and
  `isExAnteNashEquilibrium_iff_allConditionalInterimPureActionBestResponses_of_fullTypeSupport`
  gives its source-facing pure-action statement in the fixed-action-family
  specialization;
- `behavioralExpectedPayoff_eq_sum_typeMarginal_mul_conditionalInterim` proves
  the displayed identity
  `gamma^i(sigma) = sum_t Pi^i(t) B^i(t)`, including a proved null-type
  convention rather than an implicit division by zero;
- own-type-conditioned optimality is consistently called interim, while the
  source's local use of the word "ex-post" is documented;
- mixed strategies over pure contingent plans and behavioral strategies remain
  distinct representations; the formalization proves equality of the realized
  action distributions at every type profile, equality of ex-ante payoffs, and
  equivalence of mixed-plan Nash equilibrium with behavioral Bayesian
  equilibrium;
- `exists_isMixedBayesianEquilibrium` and
  `exists_isBayesianEquilibrium` derive finite ex-ante existence from the
  repository's Nash theorem, including the vacuous empty-player case;
- `exists_isInterimBayesianEquilibrium` and
  `exists_allConditionalInterimPureActionBestResponses_of_fullTypeSupport`
  separately expose the guarded and all-type, pure-action
  fixed-action-family forms of MSZ Theorem 9.52;
- the behavioral/distributional correspondence is exact at every type: a null
  type has zero joint type-action mass, although its conditional behavioral
  representative is not unique;
- the continuous track separately formalizes standard-Borel random-seed and
  disintegration representations, the war-of-attrition example, and the
  nonatomic equilibrium model without weakening their measure-theoretic side
  conditions;
- the module and knowledge nodes explicitly record that `Act i` does not
  formalize MSZ's more general type-dependent action sets `A_i(t_i)`, and that
  `strategicForm` is the original-player complete-plan game rather than the
  player-type agent form of MSZ Definition 9.50.

## Severity convention

- **S1 - semantic mismatch:** the formal object is not yet the object defined
  in the source, or a source attribution requires a missing equivalence.
- **S2 - incomplete theorem:** the main mathematical statement is only
  conditional, weaker, or structurally less informative than the cited result.
- **S3 - documentation/API issue:** the mathematics is sound, but terminology,
  naming, or comments can mislead a user about its meaning.

## Executive findings

### Mixed contingent plans and behavioral strategies - S1 (resolved)

MFoGT Definition 7.2.2 first describes deterministic contingent plans, while
the subsequent finite mixed-strategy formula uses signal-contingent mixed
actions. At state `omega`, the conditional probability of an action profile is
the product

```text
q(omega, s) = product_i sigma_i(theta_i(omega))(s_i),
```

and `Q(s)` is its expectation under the prior. The formalization now contains
both representations. `contingentPlanExtension` uses the source's complete pure
plans, while `extendBy` uses signalwise mixed actions. `stdSimplex.piProduct`
constructs an independent mixed-plan coupling for every behavioral strategy,
and `stdSimplex.coordinateMarginal` sends every mixed plan to its signalwise
action marginals. The formal payoff, Nash, induced-distribution, and union-level
equivalence theorems prove that the behavioral API is an exact finite
realization of the source model rather than merely a documented analogy.

### Realization of stochastic learning procedures - S1 (resolved for the cited propositions)

`NoRegret/Process.lean` now constructs a common filtered probability space with
fresh stagewise randomization from Mathlib's Ionescu--Tulcea trajectory
measure. It proves the exact conditional action laws, realizes the external and
internal regret procedures against finite-history predictable environments,
realizes the calibration rule, and constructs the independent simultaneous
joint play required by Proposition 7.3.18.

The unrestricted `Classical.choose` invariant-measure selector is still not
proved measurable as a function on the full real-valued history space. This no
longer makes the proposition-level theorems vacuous: after composition with a
finite action-history rule, the kernel domain is finite and discrete. Processes
with additional exogenous random state remain covered by the reusable
conditional theorems rather than by a separate universal construction theorem.

### Primitive versus reduced Bayesian games - S1 (resolved in the finite model)

MFoGT Section 7.4 begins with a state space, state-dependent payoffs, and player
signals, and then obtains a type-profile formulation by conditioning on the
signals. `PrimitiveBayesianGame` now represents the finite primitive data, and
`toReduced` constructs the induced type-profile prior and conditional expected
payoffs. The payoff- and equilibrium-preservation theorems verify that this is
the reduction used in the source rather than an unrelated reduced model.

## Section-by-section findings

### Section 7.2.2 - Information structures and extended games

**Sound content**

- The finite event space, common prior, finite signal spaces, and signal maps
  are the discrete specialization of MFoGT Definition 7.2.1.
- The ex-ante payoff of an extension is correctly an expectation over the
  underlying event.

**Resolved findings**

- **Resolved S1:** The source's pure complete-plan extension and its mixed
  strategy space are encoded directly. The behavioral extension remains a
  separate representation, and the formal marginal/product-coupling bridge
  proves payoff and Nash equivalence in both directions.
- **Resolved S2:** `isExtendedNashEquilibrium_iff_signalwise` proves the
  equivalence between ex-ante equilibrium and best response after every signal.
  The unnormalized formulation handles null signals without division.
- **Resolved S3:** Using the payoff field itself as the scalar type of the
  common prior is an algebraic generalization. The module documentation now
  states explicitly that `U = ℝ` is the source specialization.

### Section 7.2.3 - Correlated equilibrium distributions

**Sound content**

- Defining a correlated equilibrium as an equilibrium of an information
  extension and comparing equilibria through their induced distributions is
  the correct conceptual organization.

**Resolved findings**

- **Resolved S1:** The induced distribution now averages the product
  distribution of players' signal-contingent mixed actions.
- **Resolved S1:** `inducedMixedContingentPlanDistribution_val` proves the
  direct fiber-sum formula for mixed complete plans, and
  `mixedContingentPlanCorrelatedEquilibriumDistributions_eq_behavioral` proves
  that the literal MFoGT union and the behavioral union coincide.
- **Resolved S2:** `isExtendedNashEquilibrium_trivial_iff_isMixedNashEq`
  formalizes the observation that a trivial information structure recovers
  ordinary mixed Nash equilibrium.
- **Resolved S2:** `inducedDistribution_trivial_eq_piProduct` identifies the
  induced distribution with MSZ Equation (8.10), and
  `piProduct_mem_correlatedEquilibriumDistributions_of_isMixedNashEq` proves
  MSZ Theorem 8.7. The separate
  `..._of_mixedNashEquilibrium` theorem closes the formal predicate bridge to
  Nash existence rather than relying on an informal equivalence of the two
  Nash APIs.
- **Resolved S3:**
  `vertex_mem_correlatedEquilibriumDistributions_iff_isNashEquilibrium`
  supplies the actual point-mass-distribution theorem. The older
  `nash_iff_degenerate_ce` remains only an unfolding lemma for a
  profile-level shorthand and is no longer used as evidence for the
  distribution-level claim.
- **Resolved S2:** `correlatedEquilibriumDistributions_image_convex` proves
  convexity of `CED(G)` in the ambient profile-weight vector space.

### Section 7.2.4 - Canonical correlation

**Sound content**

- The canonical state space is the pure-profile space, player `i` observes the
  `i`-th component, and truthful play selects the recommended action.
- The obedience proof for the canonical construction has the correct economic
  direction.

**Resolved findings**

- **Resolved S1:**
  `canonicalCorrelatedEquilibriumDistributions_eq_correlatedEquilibriumDistributions`
  proves the Nash-based `CCED(G) = CED(G)` statement from MFoGT Theorem 7.2.6.
  The proof factors through the separately proved ex-ante/ex-post equivalence.

### Section 7.2.5 - Characterization

**Sound content**

- The obedience inequality has the correct sign and correctly avoids division
  by the probability of a recommendation.
- `mem_correlatedEquilibriumDistributions_iff_obedience` gives the exact
  Nash-based membership equivalence in MFoGT Theorem 7.2.7.

**Resolved findings**

- **Resolved S2:** The former proposition-only `HasCEDHRepresentation` wrapper
  was replaced by an explicit ambient set containing simplex and finite linear
  obedience constraints.
- **Resolved S2:**
  `correlatedEquilibriumDistributions_eq_finiteLinearInequalitySet` gives the
  exact finite H-description of the Nash-based `CED(G)`, and
  `correlatedEquilibriumDistributions_image_convex` proves convexity.
  `correlatedEquilibriumDistributions_eq_convexHull_finset` now proves the
  final finite-vertex/convex-hull conclusion of MFoGT Corollary 7.2.8 for real
  payoffs.
- **Resolved S3:** The finite-linear-inequality and finite-convex-hull theorems
  both target the Nash-based source set.

### Section 7.3.1 - External regret

**Sound content**

- External regret, average regret, regret matching, the Blackwell condition,
  and the implication corresponding to MFoGT Proposition 7.3.4 have the correct
  signs and quantifiers.
- `hasNoExternalRegret_iff_tendsto_maximalPositiveAverageExternalRegret_zero`
  identifies the coordinatewise predicate with the book's maximum-positive-
  regret limit.
- Relative to MSZ Definition 14.42 and Equation (14.101), every regret
  coordinate has the opposite sign: Lean uses
  `alternative payoff - realized payoff` and the nonpositive orthant, while
  MSZ uses `realized payoff - alternative payoff` and the nonnegative
  orthant. Negation is an exact coordinatewise isometry, so the no-regret
  condition and approachability target agree.

**Verified alignment**

- **Resolved S1:**
  `externalRegretMatchingStrategy_hasNoExternalRegretAE_against_predictable`
  connects the displayed kernel to an explicit adapted trajectory process and
  proves Proposition 7.3.4 for every bounded finite-history predictable payoff
  rule.
- **Resolved S2:** `EconCSLib.Blackwell.blackwell_approach_closedConvex_ae`
  proves MFoGT Theorem 7.3.2 for an arbitrary bundled nonempty closed convex
  target. `blackwell_projectionDistance_tendsto_zero_ae` gives exactly the
  displayed `d(bar x_n,D) -> 0` conclusion. The finite-coordinate theorem
  `blackwell_approach_negativeOrthant_ae` is the specialization used by the
  regret proofs, while the reusable library theorem supports arbitrary closed
  convex targets.
- **Resolved S3:** The support-based predicate is now named
  `IsRobustPathwiseNoExternalRegretStrategy`; the source-facing AE statement is
  kept in the generated-process layer.
- **Resolved S3:** Filtration comments now describe measurability relative to
  pre-action information and explicitly avoid claiming that the filtration is
  exactly the history supplied to the strategy.
- **Scope qualification:** MSZ Definition 14.42 quantifies over every fixed
  state sequence in an expert problem. The canonical Lean theorem permits the
  payoff rule to depend on finite past history but requires it to be fixed
  before the current fresh action draw. This is a stronger nonanticipating
  adversary model, not permission to react to the current random action.

### Section 7.3.2 - Internal regret

**Sound content**

- The internal-regret matrix, invariant-measure condition, orthogonality
  identity, and conditional Blackwell argument match MFoGT.
- `MatrixGame.exists_invariant_measure_nonneg` supplies the finite
  nonnegative-matrix invariant measure invoked before MFoGT Lemma 7.3.6.
- `invariantMeasure_internalRegret_orthogonal` assumes only invariance: the
  nonnegativity used to obtain an invariant measure is not unnecessarily
  imposed on the algebraic identity itself.
- `hasNoInternalRegret_iff_tendsto_maximalPositiveAverageInternalRegret_zero`
  identifies the coordinatewise predicate with the book's maximum-positive-
  matrix-entry limit.

**Verified alignment and coverage boundary**

- **S1, narrowed:** The generic regret-matching strategy uses an arbitrary
  classical choice of invariant measure. Measurability of that selector on the
  unrestricted real-valued history space is not proved. The canonical
  finite-history realization in `NoRegret/Process.lean` is nevertheless valid,
  because every map out of its finite discrete history domain is measurable.
- **Resolved S1:** `internalRegretMatchingStrategy_hasNoInternalRegretAE_against_predictable`
  constructs the trajectory measure and proves Proposition 7.3.7 against every
  bounded finite-history predictable payoff rule.
- **Resolved S3:** The predicate is now named
  `IsRobustPathwiseNoInternalRegretStrategy`.
- **Narrative boundary:** MFoGT Remark 7.3.8 is an interpretation in terms of
  external and adaptive experts, not a new theorem or definition. It is
  documented but has no dedicated declaration.

### Section 7.3.3 - Calibration

**Sound content**

- The calibration error, loss-vector reduction, finite grid, and
  Cauchy-Schwarz estimate agree with MFoGT Definition 7.3.9 and the surrounding
  argument.

**Verified alignment and coverage boundary**

- **Resolved S1:** `exists_forecastRule_isEpsilonCalibratedAE_against_predictable`
  constructs a finite grid, forecast rule, and canonical trajectory measure for
  every finite-history predictable outcome rule. The conditional theorem also
  covers processes with additional exogenous randomness.
- **Resolved S3:** `IsEpsilonCalibrated` is the direct realized-path
  `limsup <= epsilon` predicate justified by the source proof's
  `epsilon + o(1)` bound, and `IsEpsilonCalibratedAE` is its direct
  almost-sure lifting. Generated-process predicates now reuse this API.
- **Narrative boundary:** MFoGT Remark 7.3.11 sketches a separate
  calibration-to-approachability proof with an unspecified martingale
  argument; it is not a precise new theorem statement and has no dedicated
  declaration here.
- **Resolved S3:** `ForecastGrid.forecast_injective` makes the indexed grid an
  actual finite set of distinct forecast distributions, matching the source's
  finite subset `V` of the outcome simplex.
- **Resolved S3:** Membership of the current outcome in the pre-randomization
  filtration expresses that the environment fixes it before the fresh forecast
  draw. It does not mean that the current outcome is an argument of the
  forecasting strategy.

### Section 7.3.4.1 - Hannan consistency

**Sound content**

- The Hannan set, marginal payoff vector, empirical identity, and the pathwise
  and almost-sure versions of MFoGT Proposition 7.3.13 are correct.

**Verified alignment**

- The pathwise and almost-sure Proposition 7.3.13 theorems have the source's
  exact hypothesis and conclusion.
  `externalRegretMatchingStrategy_empiricalDistribution_approaches_hannan_ae`
  composes the generated proportional-regret process with this implication
  under the explicit nonanticipation and `[-1,1]` payoff assumptions.
- **Resolved S2:** `jointFirstMarginal`, `jointSecondMarginal`,
  `ColumnHannanSet`, and
  `hannanSets_zeroSum_marginals_optimal_and_payoff_eq_value` prove the full
  zero-sum consequence following Proposition 7.3.13.
- **Resolved S2:** `HannanThreeCycle.lean` proves the claims represented by
  MFoGT Example 7.3.14, including membership in both Hannan sets and failure of
  the row no-comparison-regret constraint.

### Section 7.3.4.2 - Internal consistency and CED

**Sound content**

- The comparison vector `C(j,k)`, the no-`C`-regret set, and the algebra behind
  MFoGT Propositions 7.3.16-7.3.18 have the correct signs and empirical
  identities.

**Verified alignment**

- **Resolved S1:** `allPlayersInternalRegret_empiricalDistribution_approaches_CED_ae`
  constructs the joint independently randomized repeated-game process, proves
  every player's no-internal-regret property under that same law, and obtains
  the claimed almost-sure `CED(G)` convergence for arbitrary finite real-payoff
  games with nonempty action sets. The proof correctly averages
  over simultaneous opponents' fresh actions instead of misclassifying the
  current payoff vector as globally predictable.
- **Resolved S1:** `allPlayersNoInternalRegretSet_eq_CED` and the pathwise/AE
  `...approaches_CED` theorems now target MFoGT's Nash-based `CED(G)`, using the
  proved Section 7.2 ex-ante/ex-post equivalence.
- **Resolved S2:** `noCRegretSet_subset_hannanSet` states and proves the
  no-`C`-regret/Hannan inclusion.
- **Resolved S2:**
  `internalRegretMatchingStrategy_empiricalDistribution_approaches_playerSet_ae`
  composes the generated invariant-measure process with Proposition 7.3.16
  under the explicit nonanticipation and boundedness assumptions.
- **Resolved S2:** `independentProfileAction_expectedInternalRegret` and
  `independentProfileAction_internalRegret_orthogonal` expose the
  conditional-vector/product-mixture step used in the source proof.
- **Resolved S2:**
  `correlatedEquilibriumDistributions_nonempty_of_internalRegretProcess`
  derives nonemptiness of `CED(G)` from the generated process, formalizing the
  existence consequence stated immediately after Proposition 7.3.18.

### Section 7.3 final statement and generality audit

- No source-facing Section 7.3 theorem depends on `sorryAx`, and no
  counterexample exists under its formal hypotheses: every listed result has a
  checked Lean proof.
- The full Blackwell theorem assumes exactly finite dimensionality, a Borel
  measurable structure, adaptedness, uniform almost-sure boundedness,
  conditional expectation, and the projection inequality. Completeness is
  derived internally from finite dimensionality and is not an extra public
  assumption. The reusable metric-projection API remains valid in arbitrary
  complete real Hilbert spaces.
- `Fintype` and `Nonempty` assumptions on action/outcome sets express the
  finite nonempty model used by the source. `DecidableEq` assumptions support
  finite indicators and are computational typeclass data, not added
  game-theoretic restrictions.
- The book's `[-1,1]^K` payoff bound is retained by the online-process API.
  The reusable Blackwell theorem is more general and accepts any common finite
  norm bound.
- The invariant-measure existence theorem requires a nonnegative matrix, while
  the orthogonality identity requires only invariance. This separates the
  logically necessary assumptions and avoids an overstrong lemma statement.
- `IsEpsilonCalibrated` does not assert existence of an ordinary limit that
  the source proof does not establish. It records the standard
  `limsup <= epsilon` meaning of the displayed `epsilon + o(1)` estimate.
- The matrix-game value and optimal-strategy API now permits the row and column
  action types to inhabit different universes. Only the later dependent
  strategic-game embedding retains a same-universe restriction, where Lean's
  single strategy family actually requires it.
- Pathwise implications, universal generated-process guarantees, and explicit
  canonical trajectory constructions have distinct names and statements. In
  particular, no conditional implication is documented as if it constructed
  a stochastic process.

### Section 7.4.1 - Bayesian games and equilibrium

**Sound content**

- In the finite primitive and reduced models, behavioral strategies, product
  action probabilities, ex-ante payoffs, Bayesian equilibrium, and the
  positive-probability-type best-response equivalence are correct.
- The source's two payoff decompositions are both proved: conditioning the
  primitive state model on full type profiles preserves ex-ante payoff, and
  conditioning a reduced payoff on one player's own type gives the displayed
  marginal-weighted interim formula.
- MSZ Equations (9.60)-(9.65) agree with the product action law, ex-ante
  payoff, normalized interim payoff, and marginal-weighted decomposition after
  specializing its type-dependent action sets to `A_i(t_i) = Act i`.

**Resolved findings and coverage boundary**

- **Resolved S1:** `PrimitiveBayesianGame`, `toReduced`,
  `toReduced_behavioralExpectedPayoff`, and
  `toReduced_isBayesianEquilibrium` formalize the finite primitive model,
  type-profile reduction, and preservation claims.
- **Resolved S2:** `conditionalInterimBehaviorPayoffOfMixedAction` gives the
  normalized conditional payoff, while
  `isBayesianEquilibrium_iff_conditionalInterimBestResponses` states the exact
  positive-type conditional best-response characterization.
- **Resolved S2:** MSZ Definition 9.49 quantifies over pure action deviations,
  whereas the reusable Lean predicate quantifies over all mixed actions.
  `interimBehaviorPayoffOfMixedAction_eq_sum_pure` proves the required
  linearity and `isConditionalInterimBestResponse_iff_pureAction` proves the
  two formulations equivalent; the source-literal inequality is therefore
  no longer justified only by an informal convexity argument.
- **Resolved S2:** The former marginal-only mixed/behavioral bridge is now
  strengthened by `mixedPlanActionDistribution_eq_piProduct_behavior`,
  `mixedPlanExpectedPayoff_eq_behavioralExpectedPayoff`, and
  `isMixedBayesianEquilibrium_iff_behavioral`.
- **Resolved S2:** Finite ex-ante and interim behavioral equilibrium existence
  are now separate theorems rather than a single result whose MFoGT-facing
  name was also cited for MSZ Theorem 9.52. Under full type support,
  `exists_allConditionalInterimPureActionBestResponses_of_fullTypeSupport`
  states the all-type, pure-action conclusion for the constant-action-family
  specialization. It does not cover MSZ's type-dependent action sets.
- **Source qualification:** the sentence "for each signal" is literally false
  for a signal of zero marginal probability if conditional payoff is left
  undefined and behavior there is unrestricted. The source-facing Lean theorem
  correctly quantifies over positive-probability types. A separately named
  all-type theorem is valid only because the API explicitly sets null-type
  conditional payoff to zero.
- **Resolved S3:** The source calls the own-type-conditioned condition
  "ex-post" in this passage, while standard Bayesian-game terminology calls it
  interim. The code now uses the standard term and documents the source's
  usage.
- **Resolved cross-source naming issue:**
  `IsExAnteNashEquilibrium` explicitly names the existing ex-ante predicate in
  MSZ Definition 9.46, while `IsInterimBayesianEquilibrium` names the guarded
  interim predicate in MSZ Definition 9.49. `HasFullTypeSupport` records the
  assumption that MSZ builds into Definition 9.39, and the full-support
  theorem states the all-type form of MSZ Theorem 9.53. Its
  `...PureActionBestResponses...` companion states the literal pure-deviation
  formulation rather than leaving the linearity composition to users.
- **Coverage boundary:** the primitive model is a finite specialization of the
  source's general probability space. No theorem claims the measure-theoretic
  generality of the displayed integral.
- **Coverage boundary relative to MSZ:** the action family is `Act i`, not
  `A_i(t_i)`. Thus the Lean game is a proper submodel of MSZ Definition 9.39
  when action availability varies with type.
- **Assumption audit:** the stored finiteness, nonemptiness, and decidable
  equality instances support the finite computational API. Nonempty action
  sets are mathematically needed for behavioral strategies and existence;
  decidable equality is not a substantive classical restriction on finite
  types. Full type support is deliberately not stored because MFoGT permits
  the null-signal issue that the guarded theorems handle explicitly.

### Section 7.4.2 - Mixed, behavioral, and distributional strategies

**Sound content**

- Pure plans, behavioral strategies, mixed strategies over pure plans, and
  distributional strategies are all represented.
- The compatibility equation and the exact finite correspondence between
  behavioral and distributional joint laws are correct.

**Resolved findings and coverage boundary**

- **Resolved S2:** `mixedBayesianStrategyToBehavior` takes the typewise action
  marginals of a mixed contingent plan.
- **Resolved S2:** `behaviorStrategyToMixedBayesian` constructs the product
  distribution over contingent plans, and
  `mixedBayesianStrategyToBehavior_behaviorStrategyToMixedBayesian` proves
  that its typewise marginals recover the original behavioral strategy.
- **Resolved S2:** The profile-level action-law and payoff theorems show full
  realization equivalence; the equilibrium theorem proves that unilateral
  deviations are preserved in both directions.
- **Resolved S3:** The original-player complete-plan `strategicForm` is
  documented as distinct from MSZ's agent-form game, whose player set contains
  one player for every original player-type pair.
- **Resolved S2:** `distributionalStrategyToBehavior_isInduced` strengthens the
  old positive-type-only conclusion to the exact joint-law equality at every
  type. Nonnegativity plus a zero type marginal forces every corresponding
  joint mass to be zero.
- **Resolved S2:** `ContinuousBehaviorStrategy.exists_randomSeedStrategy`
  supplies a jointly measurable uniform-`[0,1]` realization of every
  standard-Borel behavioral kernel. The equality of induced kernels and joint
  type-action laws is proved.
- **Resolved S2:** `ContinuousDistributionalStrategy.exists_behaviorStrategy`
  uses standard-Borel disintegration and proves exact recovery of the
  compatible joint law.
- **Coverage boundary (S2):** MSZ Definition 9.50 and Theorem 9.51 are recorded
  in the agent-normal-form knowledge node but are not represented by a Lean
  `agentForm` declaration. No existing strategic-form theorem is cited as if
  it proved that separate result.

### Section 7.4.2 - Example 7.4.1 and nonatomic continuation

- **Resolved S1:** `isSymmetricEquilibrium_exponentialConcessionLaw` computes
  the original payoff integral and proves equilibrium against all probability
  deviations supported almost everywhere on nonnegative concession times,
  while `mixedPayoffIntegrable_exponentialOpponent` proves that every such
  deviation satisfies the genuine iterated-integrability guard. The
  exponential law is explicitly constructed as
  `RegularFullSupportEquilibrium.exponential`, excluding a vacuous uniqueness
  class. Regular full-support uniqueness is
  `RegularFullSupportEquilibrium.measure_eq_exponential`.
- **Resolved S1:** `DensityModel.interimExpectedPayoff_eq_cutoff` proves that
  the cutoff calculation is the actual expected payoff. Under explicit
  positive-density and tail/onto hypotheses,
  `candidate_isRegularSymmetricEquilibrium` proves the displayed strategy is
  an equilibrium. `regularEquilibrium_eq_candidate` derives uniqueness from
  almost-everywhere optimality and local absolute continuity.
- **Resolved S2:** `CompactDensityModel` makes the regularity suppressed by the
  short example explicit: a continuous density is positive on the interior of
  its compact support and zero off it, and the actual CDF has the stated
  derivative and endpoint values.
  `candidate_isSymmetricBayesianEquilibrium` proves the displayed strategy is
  optimal against every nonnegative concession-time deviation.
  `candidate_absolutelyContinuousOnInterval` makes the regular uniqueness
  class inhabited, while `regularEquilibrium_eq_candidate` proves uniqueness
  in that locally absolutely continuous class.
  `dist_candidate_center_mul_hazard_le` derives the source's
  shrinking-support estimate, `map_exponentialQuantile` constructs the common
  exponential coupling, and
  `CompactActionLawSequence.convergesToExponentialLaw` proves convergence
  against every bounded continuous test function. No coupling, equilibrium,
  or convergence certificate is a structure field. The source's
  $G_n\Rightarrow\delta_v$ premise is redundant under the shrinking supports;
  the Lean result allows arbitrary error radii tending to zero, including
  $1/n$.
- **Resolved S2:** `NonatomicBayesianGame.IsDistributionalEquilibrium`
  represents the atomless agent law, both marginals, measurable best-response
  graph, and measure-one condition.
  `isDistributionalEquilibrium_iff_ae` proves its exact almost-everywhere
  formulation.

## Exact source-to-declaration matrix

The following tables are the final line-by-line coverage check. "Exact" means
that the finite statement has the same signs, conditioning direction, and
quantifier content after the repository's zero-based `n + 1` indexing shift.
"Conditional" means that the displayed mathematical implication is proved for
an already-generated process. The companion canonical-process declarations are
listed explicitly when they also supply a realization.

### MFoGT Section 7.3

| Source item | Repository declaration(s) | Strict conclusion |
| --- | --- | --- |
| Definition 7.3.1, no external regret | `HasNoExternalRegret`, `hasNoExternalRegret_iff_maximalPositiveAverageExternalRegret`, `hasNoExternalRegret_iff_tendsto_maximalPositiveAverageExternalRegret_zero`, `HasNoExternalRegretAE`, `HasNoExternalRegretOnGeneratedProcessesAE` | The coordinatewise positive-part criterion is equivalent to the source's finite maximum criterion and to convergence of that nonnegative maximum to zero. The pathwise and AE meanings are correct. |
| Theorem 7.3.2, approachability criterion | `EconCSLib.Blackwell.blackwell_approach_closedConvex_ae`; `EconCSLib.Blackwell.blackwell_projectionDistance_tendsto_zero_ae`; negative-orthant specialization `blackwell_approach_negativeOrthant_ae` | Exact finite-dimensional real-Hilbert generalization of the source's `R^K` statement. The first theorem gives set approach, the second gives the source-literal metric-projection distance limit. `hadapted` makes explicit the natural-history adaptedness implicit in the source; omitting it makes the arbitrary-filtration statement false. |
| Lemma 7.3.3, external-regret orthogonality | `expected_externalRegret_orthogonal` | Exact. `externalRegretStage choice U k = U k - U choice`, so the sign and scalar product agree with the book. |
| Proposition 7.3.4, proportional-regret rule | `externalRegretMatchingStrategy_hasNoExternalRegretOnGeneratedProcessesAE`; `externalRegretMatchingStrategy_hasNoExternalRegretAE_against_predictable` | The first theorem is the reusable conditional form. The second constructs the canonical law and proves the source conclusion against every bounded finite-history predictable payoff rule. The mixed action is proportional to positive regret with a uniform fallback when all positive regrets vanish. |
| Definition 7.3.5, no internal regret | `internalRegretStage`, `HasNoInternalRegret`, `maximalPositiveAverageInternalRegret`, `hasNoInternalRegret_iff_maximalPositiveAverageInternalRegret`, `hasNoInternalRegret_iff_tendsto_maximalPositiveAverageInternalRegret_zero`, `HasNoInternalRegretAE` | Exact coordinatewise pathwise quantity and AE lifting. For a finite action set, the source predicate is additionally proved equivalent to convergence to zero of the maximum positive entry of the whole regret matrix. |
| Invariant-measure equation before Lemma 7.3.6 | `IsInvariantMeasureFor`, `MatrixGame.exists_invariant_measure_nonneg` | Exact row/column orientation: `sum_k mu(k) A(k,l) = mu(l) sum_k A(l,k)`. Existence for every finite nonnegative matrix is proved. |
| Lemma 7.3.6, internal-regret orthogonality | `invariantMeasure_internalRegret_orthogonal` | Exact, and stated under the weakest relevant hypothesis: invariance alone. Matrix nonnegativity is needed only by the preceding existence theorem. |
| Proposition 7.3.7, invariant-measure rule | `internalRegretMatchingStrategy_hasNoInternalRegretOnGeneratedProcessesAE`; `internalRegretMatchingStrategy_hasNoInternalRegretAE_against_predictable` | The algebra and invariant-measure equation are exact. The second theorem constructs a realization against every bounded finite-history predictable payoff rule. Global measurability of the classical selector on unrestricted real histories is not asserted or needed for this finite-domain construction. |
| Remark 7.3.8, expert interpretations | no dedicated declaration | Not formalized. |
| Definition 7.3.9, epsilon-calibration | `calibrationResidual`, `directCalibrationError`, `calibrationError`, `directCalibrationError_eq_calibrationError`, `isEpsilonCalibrated_iff_directCalibrationError`, `IsEpsilonCalibrated`, `IsEpsilonCalibratedAE`, `IsRobustPathwiseEpsilonCalibrated`, `IsEpsilonCalibratedOnGeneratedProcessesAE` | The direct empirical residual-vector formula is proved equal to the frequency-weighted conditional-frequency `L2` error, including unused forecasts, and the path predicate is proved equivalent in the two presentations. `IsEpsilonCalibratedAE` is the direct source-facing almost-sure predicate; the generated-process property universally quantifies it over admissible processes. The asymptotic relation is the proof-valid `limsup <= epsilon` interpretation of the book's `epsilon + o(1)` estimate. |
| Proposition 7.3.10, existence of epsilon-calibrated rules | `isEpsilonCalibrated_of_hasNoInternalRegret`, `exists_forecastGrid_meshLe`, `exists_forecastRule_isEpsilonCalibratedOnGeneratedProcessesAE`, `exists_forecastRule_isEpsilonCalibratedAE_against_predictable` | The grid, loss identity, and Cauchy--Schwarz reduction are exact. The final declaration constructs the canonical forecast law against every finite-history predictable outcome rule and proves `epsilon`-calibration almost surely. |
| Remark 7.3.11, calibration and approachability | no dedicated declaration | Not formalized. |
| Definition 7.3.12, Hannan set | `HannanSet` | Exact payoff inequality and sign. |
| Proposition 7.3.13, external regret implies approach to Hannan set | `noExternalRegret_empiricalDistribution_approaches_hannan`, AE lifting; `externalRegretMatchingStrategy_empiricalDistribution_approaches_hannan_ae` | Exact realized-path implication and AE lifting. The final theorem composes it with the generated proportional-regret process under explicit nonanticipation and `[-1,1]` boundedness. |
| Zero-sum consequence after Proposition 7.3.13 | `hannanSets_zeroSum_marginals_optimal_and_payoff_eq_value` | Exact. Both marginals are optimal, and the product-marginal payoff, correlated payoff, and matrix-game value coincide without assuming the joint distribution is independent. |
| Example 7.3.14 | `HannanThreeCycle.hannanThreeCycleDiagonal_mem_rowHannan`, `...mem_columnHannan`, `...comparisonGain_zero_two`, `...not_mem_noCRegretSet` | The displayed matrix and diagonal distribution are formalized. The distribution satisfies both Hannan conditions and has value payoff, but a row replacement has gain `1/3`, so it fails internal consistency. |
| Definition 7.3.15, no-`C`-regret set | `comparisonGain`, `NoCRegretSet` | Exact. `noCRegretSet_subset_hannanSet` also proves the inclusion immediately following the definition. |
| Proposition 7.3.16 | `noInternalRegret_empiricalDistribution_approaches_playerSet`, AE lifting; `internalRegretMatchingStrategy_empiricalDistribution_approaches_playerSet_ae` | Exact realized-path implication and AE lifting. The final theorem composes it with the generated invariant-measure process under explicit nonanticipation and `[-1,1]` boundedness. |
| Proposition 7.3.17 | `allPlayersNoInternalRegretSet_eq_CED` | Exact, including the source's Nash-based `CED(G)` target through the separately proved Section 7.2 equivalence. |
| Proposition 7.3.18 | `noInternalRegret_allPlayers_empiricalDistribution_approaches_CED`, AE lifting; `allPlayersInternalRegret_empiricalDistribution_approaches_CED_ae`; `correlatedEquilibriumDistributions_nonempty_of_internalRegretProcess` | The conditional implication is exact. The generated-process theorem explicitly constructs independent simultaneous play by the unilateral internal-regret procedures and proves almost-sure convergence to the Nash-based `CED(G)` for arbitrary finite real-payoff games with nonempty action sets. The final declaration gives the stated correlated-equilibrium existence consequence. |

### MFoGT Section 7.4

| Source item | Repository declaration(s) | Strict conclusion |
| --- | --- | --- |
| Primitive information structure, state-dependent game, and signals | `PrimitiveBayesianGame`, `PrimitiveBayesianGame.behavioralActionProbability`, `PrimitiveBayesianGame.behavioralExpectedPayoff` | Exact finite specialization of the state, signal, behavioral strategy, product action law, and state-dependent ex-ante payoff in Section 7.4.1. |
| Induced type-profile prior and conditional reduced payoff | `PrimitiveBayesianGame.typeProfileProbability`, `PrimitiveBayesianGame.conditionalPayoff`, `PrimitiveBayesianGame.toReduced`, `PrimitiveBayesianGame.toReduced_behavioralExpectedPayoff`, `PrimitiveBayesianGame.toReduced_isBayesianEquilibrium` | Exact finite pushforward and conditional-expectation reduction. Null type-profile fibers receive payoff zero, which cannot affect ex-ante payoffs or equilibrium. Payoffs and Bayesian equilibrium are proved invariant under the reduction. |
| Behavioral strategy and product action law | `BehaviorStrategy`, `behavioralActionProbability` | Exact finite reduced form, with independent behavioral randomization conditional on the type profile. |
| Ex-ante payoff and own-type decomposition | `behavioralExpectedPayoff`, `behavioralExpectedPayoff_eq_sum_typeMarginal_mul_conditionalInterim` | Exact finite sum corresponding to the source's integral and exact proof of `gamma^i(sigma) = sum_t Pi^i(t) B^i(t)`. The null-type product is proved to be zero. |
| Own-type-conditioned best response | `conditionalInterimBehaviorPayoffOfMixedAction`, `IsConditionalInterimBestResponse`, `IsConditionalInterimPureActionBestResponse`, `interimBehaviorPayoffOfMixedAction_eq_sum_pure`, `isConditionalInterimBestResponse_iff_pureAction`, `isBayesianEquilibrium_iff_conditionalInterimBestResponses` | Exact normalized conditional payoff and ex-ante/interim equivalence for positive-probability types. Linearity proves that checking every mixed deviation is equivalent to the pure-action inequalities written in MSZ Definition 9.49. The unnormalized API is retained as an algebraically convenient equivalent. |
| Pure strategy in Section 7.4.2 | `PureStrategy` | Exact map from type to action. |
| Behavioral strategy in Section 7.4.2 | `BehaviorStrategy` | Exact map from type to a mixed action. |
| Mixed strategy in Section 7.4.2 | `MixedBayesianStrategy`, `mixedBayesianStrategyToBehavior`, `behaviorStrategyToMixedBayesian`, `mixedBayesianStrategyToBehavior_behaviorStrategyToMixedBayesian`, `mixedPlanActionDistribution_eq_piProduct_behavior`, `mixedPlanExpectedPayoff_eq_behavioralExpectedPayoff` | A mixed strategy is a distribution over pure contingent plans. Its typewise marginals give a behavioral strategy; the product coupling realizes every behavioral strategy. Realized action laws and ex-ante payoffs are proved equal, not merely asserted from matching marginals. |
| Equilibrium under mixed and behavioral representations | `IsMixedBayesianEquilibrium`, `isMixedBayesianEquilibrium_iff_behavioral`, `exists_isMixedBayesianEquilibrium`, `exists_isBayesianEquilibrium`, `exists_isInterimBayesianEquilibrium` | Exact finite strategic-form/behavioral equivalence and separate ex-ante/interim finite existence consequences. These are proved consequences of the Section 7.4 setup, not separately numbered theorems in MFoGT. |
| Distributional strategy and compatibility | `DistributionalStrategy`, `behaviorStrategyToDistributional`, `distributionalStrategyToBehavior`, `distributionalStrategyToBehavior_isInduced`, `distributionalStrategy_corresponds_to_behaviorStrategy` | Exact finite joint-law correspondence. Conditional behavior is determined only at positive-probability types, but zero marginal forces all joint masses at a null type to vanish, so an arbitrary conditional representative there still satisfies the exact induction identity. |
| Uniform random-seed representation of mixed strategies | `ContinuousBehaviorStrategy.RandomSeedStrategy`, `exists_randomSeedStrategy`, `RandomSeedStrategy.inducedDistribution_eq_behavior` | Exact for measurable type spaces and nonempty standard Borel action spaces. The seed map is jointly measurable, uniform on `[0,1]`, and induces both the original kernel and the same joint type-action law. |
| Continuous distributional/behavioral correspondence | `ContinuousDistributionalStrategy`, `ofBehavior_toBehavior`, `exists_behaviorStrategy` | Exact under standard-Borel disintegration. The type marginal is an equality of measures and recomposition recovers the joint law exactly. |
| Example 7.4.1, war of attrition | `mixedPayoffIntegrable_exponentialOpponent`; `isSymmetricEquilibrium_exponentialConcessionLaw`; `RegularFullSupportEquilibrium.exponential`; `RegularFullSupportEquilibrium.measure_eq_exponential`; `DensityModel.candidate_isRegularSymmetricEquilibrium`; `DensityModel.regularEquilibrium_eq_candidate`; `CompactDensityModel.candidate_isSymmetricBayesianEquilibrium`; `CompactDensityModel.candidate_absolutelyContinuousOnInterval`; `CompactDensityModel.regularEquilibrium_eq_candidate`; `CompactDensityModel.dist_candidate_center_mul_hazard_le`; `map_exponentialQuantile`; `CompactActionLawSequence.candidate_isEquilibrium`; `CompactActionLawSequence.convergesToExponentialLaw` | All three items are proved in explicit, inhabited regularity classes. For item 3, the displayed compact-support strategy is an actual equilibrium at every index, regular uniqueness is proved, the uniform-quantile coupling and shrinking-support estimate are derived, and the resulting action laws converge to $Q_v$ against every bounded continuous test. Shrinking support makes the separately stated convergence of the type laws to $\delta_v$ automatic. |
| Nonatomic-game continuation | `NonatomicBayesianGame`, `IsDistributionalEquilibrium`, `isDistributionalEquilibrium_iff_ae` | Exact definition with a probability and atomless agent law, prescribed type marginal, endogenous action marginal, measurable best-response graph, and equivalent measure-one/almost-everywhere conditions. No existence theorem is attributed to the source passage. |

### MSZ cross-check matrix

| MSZ source item | Repository declaration(s) | Strict conclusion |
| --- | --- | --- |
| Definition 8.4, recommendation-contingent strategy | `PureContingentPlan`; canonical identity plan `truthfulCanonicalContingentPlanProfile` | Exact finite function from recommendation to action. |
| Theorem 8.5 and Definition 8.6, obedience | `obedienceDifference`; `ObedienceInequality`; `mem_correlatedEquilibriumDistributions_iff_obedience` | Exact unnormalized inequality. A zero-probability recommendation makes every term zero, matching the null-recommendation argument below MSZ Equation (8.8). |
| Equation (8.10) and Theorem 8.7, Nash product distribution | `inducedDistribution_trivial_eq_piProduct`; `piProduct_mem_correlatedEquilibriumDistributions_of_isMixedNashEq`; `piProduct_mem_correlatedEquilibriumDistributions_of_mixedNashEquilibrium` | Exact. The product distribution of every mixed Nash equilibrium belongs to `CED(G)`, for both mixed-Nash predicates used in the repository. |
| Pure point-mass boundary of Theorem 8.7 | `vertex_mem_correlatedEquilibriumDistributions_iff_isNashEquilibrium` | Stronger iff statement: a simplex vertex is correlated exactly when its pure profile is Nash. |
| Corollary 8.8 | Nash-product theorem plus finite Nash existence; independently, `correlatedEquilibriumDistributions_nonempty_of_internalRegretProcess` | Both the classical Nash route and MFoGT's no-internal-regret route are represented. |
| Theorem 8.9 and Remark 8.10 | `correlatedEquilibriumDistributions_image_convex`; `correlatedEquilibriumDistributions_image_isCompact`; `correlatedEquilibriumDistributions_eq_convexHull_finset` | Exact finite real convexity, compactness, and polytope/finite-convex-hull conclusions. |
| Equations (9.58)-(9.65), strategies and payoffs | `PureStrategy`; `MixedBayesianStrategy`; `BehaviorStrategy`; mixed/behavioral bridge; `behavioralActionProbability`; conditional and ex-ante payoff decompositions | Exact for the constant-action-family specialization `A_i(t_i) = Act i`. The general dependent action family in MSZ is not formalized. |
| Definition 9.46, ex-ante Nash equilibrium | `IsBayesianEquilibrium`; explicit synonym `IsExAnteNashEquilibrium` | Exact no-whole-contingent-plan-deviation predicate. The old name follows MFoGT; the synonym exposes MSZ terminology. |
| Definition 9.49 and Theorem 9.53, interim Bayesian equilibrium and equivalence | `IsInterimBayesianEquilibrium`; `IsConditionalInterimPureActionBestResponse`; `isConditionalInterimBestResponse_iff_pureAction`; `HasFullTypeSupport`; `isExAnteNashEquilibrium_iff_isInterimBayesianEquilibrium_of_fullTypeSupport`; `isExAnteNashEquilibrium_iff_allConditionalInterimPureActionBestResponses_of_fullTypeSupport` | Exact after specializing MSZ's action family to `A_i(t_i) = Act i`. The pure-action deviations and positive type marginals match the source; the theorem is not the full dependent-action statement. |
| Definition 9.50 and Theorem 9.51, agent form | no Lean declaration; `bayesian_agent_normal_form.md` only | Not formalized. `BayesianGame.strategicForm` is deliberately not identified with the agent form. |
| Theorems 9.47 and 9.52, finite existence | `exists_isMixedBayesianEquilibrium`; `exists_isBayesianEquilibrium`; `exists_isInterimBayesianEquilibrium`; `exists_allConditionalInterimPureActionBestResponses_of_fullTypeSupport` | Under the full-type-support convention in MSZ Definition 9.39, these give the ex-ante and all-type pure-action interim conclusions for the constant-action-family specialization. Type-dependent action sets remain outside the Lean model. The repository also includes a harmless vacuous empty-player extension not discussed in MSZ. |
| Definition 14.42 and Theorem 14.44, no regret | `HasNoExternalRegret`; `HasNoExternalRegretAE`; `externalRegretMatchingStrategy_hasNoExternalRegretAE_against_predictable` | Equivalent after negating coordinates. The generated-process theorem handles every bounded finite-history nonanticipating payoff rule, which includes fixed state sequences. |
| Equations (14.101)-(14.103), vector payoff and orthant | coordinate family `externalRegretStage`; `blackwell_approach_negativeOrthant_ae` | Exact sign dual: Lean's `alternative - realized` and nonpositive orthant are the negatives of MSZ's `realized - alternative` and nonnegative orthant. |

## Mechanical and foundational checks

- All averages use stages `0,...,n` with denominator `n + 1`; this is a
  consistent index shift from the book's stages `1,...,n` and does not change
  any asymptotic statement.
- External regret, internal regret, Hannan gaps, comparison gains, and
  correlated-obedience differences were checked in both algebraic directions;
  no sign reversal was found.
- The probability layer conditions on pre-action/pre-forecast information and
  pulls predictable payoffs or outcomes through conditional expectation. It
  does not permit the environment to react to the current fresh draw.
- Bayesian payoff identities were checked with both conditioning directions:
  the primitive reduction conditions on the full type profile, while the
  interim theorem conditions only on the acting player's own type. Null fibers
  are handled by proved zero-mass lemmas, not cancellation by a zero
  denominator.
- No declaration is allowed to rely on `sorry` or `admit`; the repository
  placeholder check is part of the final verification.
- A second non-vacuity pass checked every theorem family whose conclusion
  could otherwise be hidden in a hypothesis. The generated-process structures
  contain only filtration, conditional-law, and boundedness data; their
  no-regret or calibration conclusions are proved separately.
  `RegularFullSupportEquilibrium.exponential`,
  `DensityModel.candidate_isRegularSymmetricEquilibrium`, and
  `CompactDensityModel.candidate_isRegularSymmetricBayesianEquilibrium`
  explicitly inhabit the three regularity classes used by uniqueness
  theorems. `CompactActionLawSequence` stores only shrinking-support data:
  equilibrium and weak convergence are derived theorems, not structure
  fields.
- Every numbered definition, theorem, lemma, proposition, and Example 7.3.14
  in MFoGT Sections 7.3.1-7.3.4 is covered. The separate deterministic
  Blackwell-sequence exercise from MFoGT Section 2.8 remains a knowledge-node
  proof gap, but it is not a dependency of the proved stochastic projection
  theorem or any Section 7.3 result. MFoGT's narrative Remarks 7.3.8 and
  7.3.11 intentionally remain prose.

The 2026-07-20 verification run completed `lake build`,
`lake build EconCSLib.Examples`, the Lean placeholder checker, the knowledge
reference unit tests, the knowledge reference checker, `mdblueprint-check`,
and `git diff --check`; `mdblueprint-check` reported zero errors and zero
warnings.
`#print axioms` on the source-facing 7.3/7.4 theorems, including the direct
calibration bridge, generated-process conclusions, finite Bayesian
representation/existence results, and all three war-of-attrition parts,
reported only the standard `propext`, `Classical.choice`, and `Quot.sound`
dependencies and no `sorryAx`.
A second `#print axioms` pass covered 34 representative source-facing and
non-vacuity declarations spanning every Section 7.3 theorem family, the finite
and continuous Section 7.4 representation theorems, all equilibrium existence
results, and all three war-of-attrition parts. It produced the same axiom list
and no `sorryAx`.
The semantic audit found no false proposition in the finite Bayesian core.
It did find and repair a vacuity risk in the complete-information uniqueness
class: global continuity of a nonnegative-support density at zero excluded the
exponential candidate. Continuity is now required only on positive times, and
`RegularFullSupportEquilibrium.exponential` formally proves that the class
contains the source's candidate.
Two tempting stronger statements are deliberately absent because they would
be false or unsupported: all-type interim optimality without a positive type
marginal, and the full MSZ theorem with type-dependent action sets. The
bounded-support war-of-attrition proof explicitly assumes a continuous density
positive on the interior of its support; it does not silently claim the
textbook formula for irregular densities whose CDF may have flat pieces.
Within that stated regularity class, item 3 is complete and no convergence
certificate is assumed.

## References

- Rida Laraki, Jérôme Renault, and Sylvain Sorin, *Mathematical Foundations of
  Game Theory*, Springer, 2019, Chapter 7.
- Michael Maschler, Eilon Solan, and Shmuel Zamir, *Game Theory*, Cambridge
  University Press, 2013, Chapters 8, 9, and 14.
- Paul R. Milgrom and Robert J. Weber, "Distributional Strategies for Games
  with Incomplete Information," *Mathematics of Operations Research* 10(4),
  1985, 619-632.
- D. T. Bishop and C. Cannings, "A Generalized War of Attrition," *Journal of
  Theoretical Biology* 70(1), 1978, 85-124.
