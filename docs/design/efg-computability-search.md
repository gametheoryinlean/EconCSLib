# Computable implementations of the existing EFG declarations

> Historical development ledger. Counts and checkpoints below describe their
> dated development snapshots. The completed publication subset excludes
> sequential-equilibrium and arbitrary-measure pure-strategy prototypes and
> their adapters. Use `efg-module-status.md` and the live audit tools for the
> submitted module and declaration census.

This review covers all **138** noncomputable identities in the historical R checkpoint:
**58 library declarations and 80 example declarations**. The live scanner now audits
**265 modules** after adding the seven-module `Effective` probability family; the R
checkpoint itself used 227 modules. It searches for implementations of the existing mathematical
operations, keeping their original signatures and hypotheses.

At the original-signature search checkpoint, one replacement was implemented:
`Examples.ObservedNonAtomicKernelBoundary.historyUnitAction`. The remaining set
is **137** (58 library, 79 examples), with no new noncomputable identity. The
identity baseline remains unchanged. The API-growth baseline was unchanged at
that checkpoint; the later A19 architecture decision adds only two
zero-declaration aggregate paths and retains the declaration ceiling.
For the other 137 entries, the routes below record candidates and their missing
inputs or different result representations. They are not claims that those
original declarations have become computable, nor impossibility theorems.
The per-declaration machine-readable record is
[`efg_computability_classification.json`](../../scripts/efg_computability_classification.json).

The subsequent [strict library review](efg-library-computability.md) and its
[58-declaration ledger](efg-library-computability-declarations.md) refine the
library conclusions. They distinguish Lean compilation from guaranteed
numerical evaluation, supply a compilable measurable-embedding pushforward,
and prove finite-prefix witnesses for the original total eventual utility.
They also record the existing almost-everywhere constructive continuation
version; a general disintegration obstruction is not a proof that this
structured conditional kernel has no effective version.

## Effective implementations with explicit representations

The subsequent implementation step supplies executable counterparts for six
retained identities. The original analytic declarations remain at **137**;
the new finite-law and event-query outputs have exact interpretation theorems.
No original construction is replaced by a caller-supplied result or certificate.

| Original operations | Executable interface | Exact semantic connection |
|---|---|---|
| `eventArena` transition and `eventPolicy` | `transitionLaw`, `actionLaw`, `stepLaw` in [EventHistoryKernelBoundary](../../EconCSLib/Examples/ExtensiveGame/EventHistoryKernelBoundary.lean) | `transitionLaw_eq_kernel`, `actionLaw_eq_kernel`, and `stepLaw_eq_kernel`; `stepLaw_eventMass` handles every Boolean next-event query. |
| `historyArena` transition and `historyPolicy` | The corresponding three finite-law operations in [HistoryDependentKernelBoundary](../../EconCSLib/Examples/ExtensiveGame/HistoryDependentKernelBoundary.lean) | The corresponding kernel equalities and `stepLaw_eventMass`, on every complete incoming state prefix. |
| Non-atomic `abstractMeasure` | `RationalIntervals.abstractProbability information intervals` in [ObservedNonAtomicKernelBoundary](../../EconCSLib/Examples/ExtensiveGame/ObservedNonAtomicKernelBoundary.lean) | `abstractProbability_eq` preserves both unit-interval volume at root information and zero mass at terminal information. |
| Non-atomic `statePathMeasure` | `RationalIntervals.probability intervals` for the represented coordinate-one cylinder | `statePathMeasure_cylinder` equates the computed rational probability with the original complete path measure. |

The finite-law constructors use the existing concrete inputs without extra
hypotheses. They compute rationally weighted outcomes, rather than exposing a
`Measure` on arbitrary predicates. The event-history result records the actual
selected action; equal state projections still yield different recorded-action
laws. The state-history result preserves the first state in the prefix; it
does not silently become a stationary state policy. The proofs cover arbitrary
prefixes, not only the two closed regression inputs.

The non-atomic query accepts a `List (ℚ × ℚ)` describing a union of closed
intervals inside `[0,1]`. It clips interval lengths and uses recursive
inclusion-exclusion, including exact subtraction of overlap. It accepts empty,
overlapping, repeated, reversed, out-of-range, and singleton intervals without
additional certificates. `probability_nonneg` and `probability_le_one` prove
that the result lies in `[0,1]`. Kernel-checked numerical results and compiled
execution cover all these cases, including touching endpoints. The algorithm
has exponential worst-case cost in the number of intervals; it is an exact
reference implementation for finite descriptors, not a general event evaluator.
The original non-atomic law is preserved; no finitely supported replacement of
that law is asserted.

## A19 effective counterparts in the main library

A19 adds effective counterparts for four retained analytic identities without
changing their original signatures or removing their `noncomputable`
definitions. The pure `EconCSLib.Math.Probability.Effective` aggregate owns the
coded-event algorithms; `Effective.Analytic` exposes the proof-only
`Denotes`/`Represents` layer. The two EFG bridge modules are reached through
`Interface.Equilibrium.Analytic`.

| Original identities | Executable operation | Representation certificate |
|---|---|---|
| S082 `marginal` | `EffectiveLaw.map` with a coordinate preimage compiler | `effective_marginal_represents` |
| S085 `outcomeLaw` | `EffectiveLaw.map` with an evaluator preimage compiler | `effective_outcomeLaw_represents` |
| S086 `pathLaw` | `EffectiveLaw.map` with a complete-play preimage compiler | `effective_pathLaw_represents` |
| S101 `PathUtility.expectedUtility` | `EffectiveLaw.expect` on a finite rational `SimpleObservable` | `effective_expectedUtility_represents` when the caller supplies the observable's `Denotes` certificate |

Together with the six earlier finite-law and rational-event counterparts above,
the machine record now tracks ten retained identities with effective
counterparts, four of them added by A19. The current scan covers 265 modules and
still finds 137 retained identities in 35 modules, with no A19 addition.
Arbitrary measurable sets, arbitrary integrable real functions, event languages
without executable preimages or observable pullbacks, and pointwise regular
conditional versions at null prefixes remain outside this algorithmic contract.

## Exact replacement

`Set.projIcc` takes an entire `LinearOrder` dictionary, bringing the classical
`Real.linearOrder` into the original data body. Its value is nevertheless just
`max 0 (min 1 x)`. Mathlib already implements real `Min` and `Max` by mapping
rational Cauchy sequences through the quotient (`Mathlib/Data/Real/Basic.lean`,
`Real.instMin`, `Real.instMax`). The replacement builds the interval subtype
directly, keeping its inequalities in erased proof fields.

[`historyUnitAction_eq_projIcc`](../../EconCSLib/Examples/ExtensiveGame/ObservedNonAtomicKernelBoundary.lean)
is proved by `rfl`. It identifies the new function with the original function
on **every history**, including out-of-range terminal actions outside the
profile's support. No new data, assumptions, real comparison, or approximation
is introduced. The existing measurability, generated terminal observation,
and non-atomic cylinder-law proofs remain consumers of the same function.
Compilability here means producing a real Cauchy-quotient value; it does not
provide a decimal evaluator or decidable equality/order on arbitrary reals.

## Why the first compiler error is not the whole analysis

Copies of all 35 nonzero modules were elaborated with `noncomputable` removed.
Each of the 138 original source spans produced its own compiler diagnostic;
the diagnostic agrees with the recorded pre-change obstruction. These probes
leave mathematical bodies and declaration signatures unchanged. The exact
replacement then passes ordinary compilation and the environment's
`Lean.isNoncomputable` check.

Three narrower probes further separate representation from algorithm:

- Removing the measurability guard from a pushforward and using
  `(OuterMeasure.map f μ.toOuterMeasure).toMeasure ...` still fails at
  `OuterMeasure.toMeasure`. The original measure has a trimmed outer measure;
  merely defining its value as `μ (f ⁻¹' s)` for every set is not justified.
  `Measure.map_apply` gives that formula on measurable sets.
- `@Measure.dirac Unit ⊤ ()` still fails at `Measure.dirac`, even though there
  is only one possible state. A `Measure` exposes values on arbitrary
  `Set Unit`, whose membership is `Prop`, not an executable Boolean.
- Attempting `if event () then (1 : ℚ) else 0` for `event : Unit → Prop`
  needs a `Decidable (event ())` instance. Making the carrier finite does not
  provide this instance for arbitrary predicates. By contrast,
  `FiniteLaw.eventMass` deliberately accepts an executable Boolean event.

These observations justify retaining the current analytic carrier while
computing effective observables in an appropriate interface. They do not say
that Dirac sampling, non-atomic sampling, computable probability measures, or
finite marginal calculations are mathematically impossible.
The newer measurable-embedding construction also shows that returning a
`Measure` does not itself prevent compilation; its stronger mapping hypothesis
does not cover every original measurable pushforward.

## Candidate routes and semantic obligations

Each table row below names its direct route(s). Inherited routes conservatively
track elaborated dependencies, which can include erased types and proofs; they
are search context, not a runtime dependency proof. `W` means that the current body is a wrapper around
listed analytic data. The exact dependencies and original types are retained
in the JSON record. A route is a proposal unless explicitly identified as an
existing, proved special case or the implemented clamp.

### C — Exact real clamp

Construct the subtype using max 0 (min 1 x), with the bounds confined to proof fields.

**Contract:** None: original input and result types, hypotheses, and all-history behavior are unchanged.

### D — Dirac and deterministic kernels

Compute the existing selected point or action and represent its law by FiniteLaw.pure; interpret it by the original Dirac measure in proofs.

**Contract:** Returning FiniteLaw instead of Measure/Kernel changes the result representation. No support enumeration is needed for a Dirac atom; querying an arbitrary event still requires executable membership.

### F — Finite rational measure embeddings

Retain the existing finite rational atoms; use FiniteLaw.map/bind/eventMass/expectRat before the analytic embedding.

**Contract:** The finite atoms already exist in this construction. Event queries require a Bool predicate; expectRat requires rational rewards. The original Measure-valued result is retained as analytic denotation.

### V — Non-atomic volume

For unit-interval volume, compute finite rational interval-union probabilities
by inclusion-exclusion; retain the original non-atomic measure as denotation.

**Contract:** The implemented `RationalIntervals` interface takes an effective
event description and proves agreement with volume and the existing path law.
It computes probabilities for this event family, not the original arbitrary-set
`Measure` result. `FiniteLaw` is not an exact representation of this law.

### M — General measurable pushforward

Push forward effective source laws through effective maps; for a supplied Measure, a measurable-event query reduces to evaluating the supplied measure on a preimage.

**Contract:** The query only consumes a supplied measure evaluator. A general Measure-valued replacement still needs the trimmed outer measure, including nonmeasurable sets; a Bool-event or effective-law interface changes the contract.

### K — Kernel composition and realization

In the finite rational case, implement joint draws by FiniteLaw.bind and deterministic projection by FiniteLaw.map, retaining the prefix and dependent action bundle.

**Contract:** General analytic kernels need an effective representation and integration procedure. FiniteLaw inputs are a stronger restriction; supplying the composed kernel itself would assume the original conclusion.

### B — Terminal and domain branching

Use the concrete constructor/Bool terminal test when available, followed by the same killed or absorbing branch.

**Contract:** General measurable terminal/domain sets need an executable decision. Even with that decision, Dirac measures and kernel composition remain. A decision alone does not make the original result computable.

### T — Complete trajectory laws

Compute finite prefixes from effective one-step laws. In the bounded terminating finite-law case, FiniteCompletePath.completePaths represents the complete absorbing paths exactly.

**Contract:** The general signature admits non-atomic transitions and no finite termination bound. Effective cylinders are a different representation from Measure on all path events; a supplied complete law is not its construction.

### P — Finite coordinate and prefix laws

Replace a full-trajectory marginal calculation by finite iteration; with finite rational laws use the retained-history executor and FiniteLaw.map/eventMass.

**Contract:** A finite horizon does not make arbitrary analytic one-step kernels executable. Requires effective transition/action laws and event decisions; the full Measure-valued output still crosses the analytic embedding.

### Q — Conditional distributions

At a positive finite observation atom, compute the joint finite law and normalize using FiniteLaw.conditionOnFiber; use FiniteConditionalContinuation for continuation payoffs.

**Contract:** Requires a finite joint law and decidable observation equality. General standard-Borel disintegration supplies no effective conditional kernel. At null prefixes an arbitrary regular conditional version is not pointwise the constructive continuation law.

### I — Expected utilities

Use expectRat for finite rational laws, the finite-chain solver for its exact absorbing Markov subcase, or FiniteTruncation.approximate for positive-tolerance terminal expectations.

**Contract:** Finite exact algorithms require their stated finite/rational inputs. Approximation requires effective policies, rational rewards/bounds, positive tolerance, and almost-sure reachability. Boundedness/integrability alone supplies none of these algorithms.

### E — Zero-guarded eventual utility

On lawful absorbing paths with executable terminal decisions and a reachability proof, search for the first hit and return the original payoff; the existing stoppedUtility handles a supplied bound.

**Contract:** The original function is total on every raw infinite path, including nonabsorbing and malformed paths. First-hit search changes that domain/termination contract; eventual constancy cannot be tested by any fixed prefix. A payoff projection is not real-number evaluation.

### W — Inherited analytic data

Keep the existing structural wrapper and resolve the listed underlying constructions first; there is no separate numerical algorithm in this wrapper.

**Contract:** Replacing its analytic fields by caller-supplied outputs would shift the construction to the caller. Type/proof references alone do not establish a runtime obstruction; the compiler probe does.

## Existing proved special cases

- [`FiniteLawIntegral`](../../EconCSLib/Examples/ExtensiveGame/FiniteLawIntegral.lean):
  `measure_eventMass` identifies Boolean-event probabilities;
  `integral_eq_expectRat` identifies exact rational expectations with the
  original integral. These are observable equalities, not a computable
  constructor for arbitrary `Measure` values.
- [`FiniteExecutionIntegral`](../../EconCSLib/Examples/ExtensiveGame/FiniteExecutionIntegral.lean):
  `historyLaw_eq_coordinate` and `integral_stoppedUtility` connect finite
  retained-history execution to the actual analytic coordinate and payoff.
  General non-atomic one-step kernels are outside these hypotheses.
- [`FiniteConditionalContinuation`](../../EconCSLib/Examples/ExtensiveGame/FiniteConditionalContinuation.lean):
  `conditionalLaw_joint` and `conditionalPayoff_joint_integral` preserve
  finite conditioning and payoff at positive observations. Impossible
  observations return `none`; they do not choose a version of `condDistrib`
  at a null infinite-path prefix.
- [`FiniteCompletePath`](../../EconCSLib/Examples/ExtensiveGame/FiniteCompletePath.lean):
  `completePaths` computes finite laws of absorbing infinite paths;
  `exists_pathLaw` constructs their analytic interpretation in a theorem.
  Positive atoms must terminate by the supplied bound. General trajectories
  cannot be replaced by this result without that hypothesis.
- [`FiniteTruncation`](../../EconCSLib/Examples/ExtensiveGame/FiniteTruncation.lean):
  `approximate_correct` bounds the error relative to the original eventual
  terminal integral at positive tolerance. It preserves almost-sure
  reachability as a proof premise and discovers its horizon by search.
  It is an approximation guarantee, not an exact general integral algorithm.
- [`FiniteMarkovChainSemantics`](../../EconCSLib/Examples/ExtensiveGame/FiniteMarkovChainSemantics.lean):
  `autoSolve_correct` identifies the finite rational chain solver with actual
  first-hit reward and time integrals after its global absorption check.
  Finite-state Markov and rational-reward restrictions do not follow from an
  arbitrary measurable behavioral profile.

A bounded marginal or continuation computation must retain the incoming
complete history, absolute time, and recorded actions. Fresh-clock restart,
absolute-prefix continuation, and conditioning have different semantics in
this repository; choosing a finite representation does not identify them.
In particular, a full path law cannot be replaced by an arbitrary family of
marginals without proving consistency and the required path-law equality.

## Per-declaration results

`Implemented` means the original signature is executable. `Retained` means no
such replacement was found; its route describes the available special case
or proposed interface and the required contract change above. The blocker is
the **original** modifier-only compiler diagnostic, not an assertion of an
unavoidable dependency in every possible implementation. Identities are fully
qualified to distinguish similarly named declarations in different modules.
The five names beginning with `Examples.ExtensiveGame` in this table are
relative to the `EconCSLib` namespace; the JSON retains their full names.

| ID / declaration | Original blocker | Routes (inherited) | Result |
|---|---|---|---|

### [Examples.ExtensiveGame.EventHistoryKernelBoundary](../../EconCSLib/Examples/ExtensiveGame/EventHistoryKernelBoundary.lean)

| ID / declaration | Original blocker | Routes (inherited) | Result |
|---|---|---|---|
| S004 `Examples.ExtensiveGame.EventHistoryKernelBoundary.eventArena` | `Kernel.deterministic` | D | Retained; finite-law counterpart implemented |
| S005 `Examples.ExtensiveGame.EventHistoryKernelBoundary.eventPolicy` | `Kernel.deterministic` | D | Retained; finite-law counterpart implemented |

### [Examples.ExtensiveGame.HistoryDependentKernelBoundary](../../EconCSLib/Examples/ExtensiveGame/HistoryDependentKernelBoundary.lean)

| ID / declaration | Original blocker | Routes (inherited) | Result |
|---|---|---|---|
| S006 `Examples.ExtensiveGame.HistoryDependentKernelBoundary.historyArena` | `Kernel.deterministic` | D | Retained; finite-law counterpart implemented |
| S007 `Examples.ExtensiveGame.HistoryDependentKernelBoundary.historyPolicy` | `Kernel.deterministic` | D | Retained; finite-law counterpart implemented |

### [Examples.ExtensiveGame.MeasurableKernelContinuationNashBoundary](../../EconCSLib/Examples/ExtensiveGame/MeasurableKernelContinuationNashBoundary.lean)

| ID / declaration | Original blocker | Routes (inherited) | Result |
|---|---|---|---|
| S008 `Examples.MeasurableKernelContinuationNashBoundary.AnalyticArena` | `historyModel` | W (F) | Retained |
| S009 `Examples.MeasurableKernelContinuationNashBoundary.assembledBaseline` | `historyModel` | W (D, F) | Retained |
| S010 `Examples.MeasurableKernelContinuationNashBoundary.assembledDeviation` | `historyModel` | W (D, F) | Retained |
| S011 `Examples.MeasurableKernelContinuationNashBoundary.baselineProfile` | `Kernel.deterministic` | D (F) | Retained |
| S012 `Examples.MeasurableKernelContinuationNashBoundary.deviatedProfile` | `historyModel` | W (D, F) | Retained |
| S013 `Examples.MeasurableKernelContinuationNashBoundary.goodStrategy` | `Kernel.deterministic` | D (F) | Retained |
| S014 `Examples.MeasurableKernelContinuationNashBoundary.historyModel` | `ObservedGame.MeasurableHistoryModel.discrete` | W (F) | Retained |
| S015 `Examples.MeasurableKernelContinuationNashBoundary.presentation` | `realization` | W (D, F) | Retained |
| S016 `Examples.MeasurableKernelContinuationNashBoundary.realization` | `historyModel` | W (D, F) | Retained |
| S017 `Examples.MeasurableKernelContinuationNashBoundary.realizationKernel` | `Kernel.deterministic` | D (F) | Retained |

### [Examples.ExtensiveGame.MeasurableKernelFreshRestartClockBoundary](../../EconCSLib/Examples/ExtensiveGame/MeasurableKernelFreshRestartClockBoundary.lean)

| ID / declaration | Original blocker | Routes (inherited) | Result |
|---|---|---|---|
| S018 `Examples.MeasurableKernelFreshRestartClockBoundary.arena` | `KernelArena.toMeasurable` | W (F) | Retained |
| S019 `Examples.MeasurableKernelFreshRestartClockBoundary.policy` | `Classical.propDecidable` | B, D (F) | Retained |
| S020 `Examples.MeasurableKernelFreshRestartClockBoundary.stationaryEventPolicy` | `arena` | W (B, F) | Retained |
| S021 `Examples.MeasurableKernelFreshRestartClockBoundary.stationaryPolicy` | `KernelArena.Policy.toMeasurable` | W (B, F) | Retained |

### [Examples.ExtensiveGame.MeasurableKernelRestartInformationRebaseBoundary](../../EconCSLib/Examples/ExtensiveGame/MeasurableKernelRestartInformationRebaseBoundary.lean)

| ID / declaration | Original blocker | Routes (inherited) | Result |
|---|---|---|---|
| S022 `Examples.MeasurableKernelRestartInformationRebaseBoundary.arena` | `KernelArena.toMeasurable` | W (F) | Retained |
| S023 `Examples.MeasurableKernelRestartInformationRebaseBoundary.stationaryInformationPolicy` | `Kernel.deterministic` | D (F) | Retained |
| S024 `Examples.MeasurableKernelRestartInformationRebaseBoundary.timeSensitiveInformationPolicy` | `Kernel.deterministic` | D (F) | Retained |

### [Examples.ExtensiveGame.NonmeasurableFiberLegalityBoundary](../../EconCSLib/Examples/ExtensiveGame/NonmeasurableFiberLegalityBoundary.lean)

| ID / declaration | Original blocker | Routes (inherited) | Result |
|---|---|---|---|
| S025 `Examples.NonmeasurableFiberLegalityBoundary.arena` | `Measure.dirac` | D | Retained |
| S026 `Examples.NonmeasurableFiberLegalityBoundary.badKernel` | `arena` | D | Retained |

### [Examples.ExtensiveGame.ObservedChanceKernelBridgeBoundary](../../EconCSLib/Examples/ExtensiveGame/ObservedChanceKernelBridgeBoundary.lean)

| ID / declaration | Original blocker | Routes (inherited) | Result |
|---|---|---|---|
| S027 `Examples.ObservedChanceKernelBridgeBoundary.liftedArena` | `KernelArena.toMeasurable` | W (F) | Retained |

### [Examples.ExtensiveGame.ObservedChanceMeasurableUncountableBoundary](../../EconCSLib/Examples/ExtensiveGame/ObservedChanceMeasurableUncountableBoundary.lean)

| ID / declaration | Original blocker | Routes (inherited) | Result |
|---|---|---|---|
| S028 `Examples.ObservedChanceMeasurableUncountableBoundary.AnalyticArena` | `measurableHistoryModel` | W (D) | Retained |
| S029 `Examples.ObservedChanceMeasurableUncountableBoundary.abstractKernel` | `abstractMeasure` | W (F) | Retained |
| S030 `Examples.ObservedChanceMeasurableUncountableBoundary.abstractMeasure` | `ENNReal.instCommSemiring` | F | Retained |
| S031 `Examples.ObservedChanceMeasurableUncountableBoundary.eventPathLaw` | `ObservedChanceGame.MeasurablePresentation.eventPathMeasure` | W (B, D, F, K, M, T) | Retained |
| S032 `Examples.ObservedChanceMeasurableUncountableBoundary.measurableHistoryModel` | `Kernel.deterministic` | D | Retained |
| S033 `Examples.ObservedChanceMeasurableUncountableBoundary.policy` | `abstractKernel` | W (B, D, F) | Retained |
| S034 `Examples.ObservedChanceMeasurableUncountableBoundary.presentation` | `realization` | W (B, D, F) | Retained |
| S035 `Examples.ObservedChanceMeasurableUncountableBoundary.realization` | `realizationKernel` | W (B, D) | Retained |
| S036 `Examples.ObservedChanceMeasurableUncountableBoundary.realizationKernel` | `AnalyticArena` | B, D | Retained |
| S037 `Examples.ObservedChanceMeasurableUncountableBoundary.statePathLaw` | `ObservedChanceGame.MeasurablePresentation.statePathMeasure` | W (B, D, F, K, M, T) | Retained |

### [Examples.ExtensiveGame.ObservedChanceRealizedPresentationBoundary](../../EconCSLib/Examples/ExtensiveGame/ObservedChanceRealizedPresentationBoundary.lean)

| ID / declaration | Original blocker | Routes (inherited) | Result |
|---|---|---|---|
| S038 `Examples.ObservedChanceRealizedPresentationBoundary.presentation` | `unitRealization` | W (B, D, F) | Retained |

### [Examples.ExtensiveGame.ObservedEventKernelBoundary](../../EconCSLib/Examples/ExtensiveGame/ObservedEventKernelBoundary.lean)

| ID / declaration | Original blocker | Routes (inherited) | Result |
|---|---|---|---|
| S039 `Examples.ExtensiveGame.ObservedEventKernelBoundary.blindFalsePolicy` | `Kernel.deterministic` | D | Retained |

### [Examples.ExtensiveGame.ObservedKernelProfileAssemblyBoundary](../../EconCSLib/Examples/ExtensiveGame/ObservedKernelProfileAssemblyBoundary.lean)

| ID / declaration | Original blocker | Routes (inherited) | Result |
|---|---|---|---|
| S040 `Examples.ObservedKernelProfileAssemblyBoundary.AnalyticArena` | `historyModel` | W (F) | Retained |
| S041 `Examples.ObservedKernelProfileAssemblyBoundary.baselineKernel` | `Kernel.deterministic` | D (B, F) | Retained |
| S042 `Examples.ObservedKernelProfileAssemblyBoundary.baselineProfile` | `baselineKernel` | W (B, D, F) | Retained |
| S043 `Examples.ObservedKernelProfileAssemblyBoundary.deviatedProfile` | `historyModel` | W (B, D, F, V) | Retained |
| S044 `Examples.ObservedKernelProfileAssemblyBoundary.historyModel` | `ObservedGame.MeasurableHistoryModel.discrete` | W (F) | Retained |
| S045 `Examples.ObservedKernelProfileAssemblyBoundary.presentation` | `realization` | W (B, D, F) | Retained |
| S046 `Examples.ObservedKernelProfileAssemblyBoundary.realization` | `realizationKernel` | W (B, D, F) | Retained |
| S047 `Examples.ObservedKernelProfileAssemblyBoundary.realizationKernel` | `AnalyticArena` | B, D (F) | Retained |
| S048 `Examples.ObservedKernelProfileAssemblyBoundary.secondPlayerStrategy` | `unitInterval.instMeasureSpaceElemReal` | V, D (B, F) | Retained |

### [Examples.ExtensiveGame.ObservedMeasurableKernelAlmostSureOutcomeBoundary](../../EconCSLib/Examples/ExtensiveGame/ObservedMeasurableKernelAlmostSureOutcomeBoundary.lean)

| ID / declaration | Original blocker | Routes (inherited) | Result |
|---|---|---|---|
| S049 `Examples.ObservedMeasurableKernelAlmostSureOutcomeBoundary.historyModel` | `ObservedChanceGame.MeasurableHistoryModel.discrete` | W (F) | Retained |

### [Examples.ExtensiveGame.ObservedMeasurableKernelOutcomeBoundary](../../EconCSLib/Examples/ExtensiveGame/ObservedMeasurableKernelOutcomeBoundary.lean)

| ID / declaration | Original blocker | Routes (inherited) | Result |
|---|---|---|---|
| S050 `Examples.ObservedMeasurableKernelOutcomeBoundary.AnalyticArena` | `historyModel` | W (F) | Retained |
| S051 `Examples.ObservedMeasurableKernelOutcomeBoundary.assembledBaseline` | `historyModel` | W (D, F) | Retained |
| S052 `Examples.ObservedMeasurableKernelOutcomeBoundary.assembledDeviation` | `historyModel` | W (D, F) | Retained |
| S053 `Examples.ObservedMeasurableKernelOutcomeBoundary.baselineProfile` | `Kernel.deterministic` | D (F) | Retained |
| S054 `Examples.ObservedMeasurableKernelOutcomeBoundary.deviatedProfile` | `historyModel` | W (D, F) | Retained |
| S055 `Examples.ObservedMeasurableKernelOutcomeBoundary.historyModel` | `ObservedGame.MeasurableHistoryModel.discrete` | W (F) | Retained |
| S056 `Examples.ObservedMeasurableKernelOutcomeBoundary.presentation` | `realization` | W (D, F) | Retained |
| S057 `Examples.ObservedMeasurableKernelOutcomeBoundary.realization` | `realizationKernel` | W (D, F) | Retained |
| S058 `Examples.ObservedMeasurableKernelOutcomeBoundary.realizationKernel` | `Kernel.deterministic` | D (F) | Retained |
| S059 `Examples.ObservedMeasurableKernelOutcomeBoundary.trueStrategy` | `Kernel.deterministic` | D (F) | Retained |

### [Examples.ExtensiveGame.ObservedNonAtomicKernelBoundary](../../EconCSLib/Examples/ExtensiveGame/ObservedNonAtomicKernelBoundary.lean)

| ID / declaration | Original blocker | Routes (inherited) | Result |
|---|---|---|---|
| S060 `Examples.ObservedNonAtomicKernelBoundary.AnalyticArena` | `ObservedChanceMeasurableUncountableBoundary.AnalyticArena` | W (D) | Retained |
| S061 `Examples.ObservedNonAtomicKernelBoundary.abstractKernel` | `abstractMeasure` | W (V) | Retained |
| S062 `Examples.ObservedNonAtomicKernelBoundary.abstractMeasure` | `unitInterval.instMeasureSpaceElemReal` | V | Retained; exact event query implemented |
| S063 `Examples.ObservedNonAtomicKernelBoundary.chanceHistoryModel` | `Kernel.deterministic` | D | Retained |
| S064 `Examples.ObservedNonAtomicKernelBoundary.chancePresentation` | `realization` | W (B, D, K, V) | Retained |
| S065 `Examples.ObservedNonAtomicKernelBoundary.chanceProfile` | `policy` | W (B, D, K, V) | Retained |
| S066 `Examples.ObservedNonAtomicKernelBoundary.concreteRootLaw` | `Measure.map` | V, M | Retained |
| S067 `Examples.ObservedNonAtomicKernelBoundary.eventPathMeasure` | `ObservedGame.MeasurableKernelPresentation.KernelBehavioralProfile.eventPathMeasure` | W (B, D, K, M, T, V) | Retained |
| S068 `Examples.ObservedNonAtomicKernelBoundary.historyUnitAction` | `Real.linearOrder` | C | Implemented |
| S069 `Examples.ObservedNonAtomicKernelBoundary.policy` | `abstractKernel` | W (B, D, V) | Retained |
| S070 `Examples.ObservedNonAtomicKernelBoundary.presentation` | `realization` | W (B, D) | Retained |
| S071 `Examples.ObservedNonAtomicKernelBoundary.profile` | `policy` | W (B, D, V) | Retained |
| S072 `Examples.ObservedNonAtomicKernelBoundary.realization` | `realizationKernel` | W (B, D) | Retained |
| S073 `Examples.ObservedNonAtomicKernelBoundary.realizationKernel` | `ObservedChanceMeasurableUncountableBoundary.AnalyticArena` | W (B, D) | Retained |
| S074 `Examples.ObservedNonAtomicKernelBoundary.statePathMeasure` | `ObservedGame.MeasurableKernelPresentation.KernelBehavioralProfile.statePathMeasure` | W (B, D, K, M, T, V) | Retained; exact event query implemented |

### [Examples.ExtensiveGame.RealizedInformationBoundary](../../EconCSLib/Examples/ExtensiveGame/RealizedInformationBoundary.lean)

| ID / declaration | Original blocker | Routes (inherited) | Result |
|---|---|---|---|
| S075 `Examples.RealizedInformationBoundary.unitAbstractKernel` | `Classical.propDecidable` | B, D | Retained |
| S076 `Examples.RealizedInformationBoundary.unitPolicy` | `unitAbstractKernel` | W (B, D, F) | Retained |
| S077 `Examples.RealizedInformationBoundary.unitRealization` | `Kernel.deterministic` | D (F) | Retained |

### [Examples.ExtensiveGame.ReusableSemantics](../../EconCSLib/Examples/ExtensiveGame/ReusableSemantics.lean)

| ID / declaration | Original blocker | Routes (inherited) | Result |
|---|---|---|---|
| S078 `Examples.ReusableSemantics.controlledMeasureSemantics` | `Measure.dirac` | D | Retained |
| S079 `Examples.ReusableSemantics.finiteAndDistinguishedTopSemantics` | `Measure.dirac` | D | Retained |
| S080 `Examples.ReusableSemantics.observedMeasureSemantics` | `controlledMeasureSemantics` | W (D) | Retained |

### [GameTheory.ExtensiveGame.Observed.Controlled.Law.Analytic](../../EconCSLib/GameTheory/ExtensiveGame/Observed/Controlled/Law/Analytic.lean)

| ID / declaration | Original blocker | Routes (inherited) | Result |
|---|---|---|---|
| S081 `ExtensiveGame.ObservedGame.MeasurableKernelPresentation.kernelBehavioralCompletePathLawSemantics` | `KernelBehavioralProfile.statePathMeasure` | M (B, D, K, T) | Retained |

| ID / declaration | Original blocker | Routes (inherited) | Result |
|---|---|---|---|

### [GameTheory.ExtensiveGame.Simulation.Continuation.Conditioning](../../EconCSLib/GameTheory/ExtensiveGame/Simulation/Continuation/Conditioning.lean)

| ID / declaration | Original blocker | Routes (inherited) | Result |
|---|---|---|---|
| S088 `MeasurableKernelArena.EventHistoryActionPolicy.conditionalTailKernel` | `condDistrib` | Q (B, D, K, M, T) | Retained |
| S089 `MeasurableKernelArena.EventHistoryActionPolicy.continuationTailKernel` | `Kernel.map` | T, M (B, D, K) | Retained |

### [GameTheory.ExtensiveGame.Simulation.Continuation.Observed](../../EconCSLib/GameTheory/ExtensiveGame/Simulation/Continuation/Observed.lean)

| ID / declaration | Original blocker | Routes (inherited) | Result |
|---|---|---|---|
| S090 `ExtensiveGame.ObservedGame.MeasurableHistoryModel.BoundedPathUtility.continuationExpectedUtility` | `integral` | I (B, D, K, M, T) | Retained |
| S091 `ExtensiveGame.ObservedGame.MeasurableHistoryModel.BoundedTerminalPayoffExtension.continuationExpectedEventualUtility` | `integral` | I (B, D, E, K, M, T) | Retained |
| S092 `ExtensiveGame.ObservedGame.MeasurableKernelPresentation.KernelBehavioralProfile.continuationEventPathMeasure` | `MeasurableKernelArena.EventHistoryActionPolicy.tailEventPathMeasureFromPrefix` | W (B, D, K, M, T) | Retained |
| S093 `ExtensiveGame.ObservedGame.MeasurableKernelPresentation.KernelBehavioralProfile.continuationStatePathMeasure` | `MeasurableKernelArena.EventHistoryActionPolicy.tailStatePathMeasureFromPrefix` | W (B, D, K, M, T) | Retained |
| S094 `ExtensiveGame.ObservedGame.MeasurableKernelPresentation.KernelBehavioralProfile.freshRestartStatePathMeasure` | `statePathMeasure` | W (B, D, K, M, T) | Retained |

### [GameTheory.ExtensiveGame.Simulation.Continuation.Path](../../EconCSLib/GameTheory/ExtensiveGame/Simulation/Continuation/Path.lean)

| ID / declaration | Original blocker | Routes (inherited) | Result |
|---|---|---|---|
| S095 `MeasurableKernelArena.EventHistoryActionPolicy.absolutePathMeasureFromPrefix` | `Kernel.traj` | T (B, D, K, M) | Retained |
| S096 `MeasurableKernelArena.EventHistoryActionPolicy.tailEventPathMeasureFromPrefix` | `Measure.map` | M (B, D, K, T) | Retained |
| S097 `MeasurableKernelArena.EventHistoryActionPolicy.tailStatePathMeasureFromPrefix` | `Measure.map` | M (B, D, K, T) | Retained |

### [GameTheory.ExtensiveGame.Simulation.Equilibrium.Outcome](../../EconCSLib/GameTheory/ExtensiveGame/Simulation/Equilibrium/Outcome.lean)

| ID / declaration | Original blocker | Routes (inherited) | Result |
|---|---|---|---|
| S098 `ExtensiveGame.ObservedGame.MeasurableHistoryModel.BoundedPathUtility.expectedUtility` | `PathUtility.expectedUtility` | W (B, D, I, K, M, T) | Retained |
| S099 `ExtensiveGame.ObservedGame.MeasurableHistoryModel.BoundedTerminalPayoffExtension.eventualUtility` | `Classical.propDecidable` | E | Retained |
| S100 `ExtensiveGame.ObservedGame.MeasurableHistoryModel.BoundedTerminalPayoffExtension.expectedEventualUtility` | `integral` | I (B, D, E, K, M, T) | Retained |
| S101 `ExtensiveGame.ObservedGame.MeasurableHistoryModel.PathUtility.expectedUtility` | `integral` | I (B, D, K, M, T) | Retained |
| S102 `ExtensiveGame.ObservedGame.MeasurableKernelPresentation.KernelBehavioralProfile.unfinishedMass` | `statePathMeasure` | P (B, D, K, M, T) | Retained |

### [GameTheory.ExtensiveGame.Simulation.Kernel.Arena](../../EconCSLib/GameTheory/ExtensiveGame/Simulation/Kernel/Arena.lean)

| ID / declaration | Original blocker | Routes (inherited) | Result |
|---|---|---|---|
| S103 `KernelArena.toMeasurable` | `ENNReal.instCommSemiring` | F | Retained |

### [GameTheory.ExtensiveGame.Simulation.Kernel.EventPath](../../EconCSLib/GameTheory/ExtensiveGame/Simulation/Kernel/EventPath.lean)

| ID / declaration | Original blocker | Routes (inherited) | Result |
|---|---|---|---|
| S104 `MeasurableKernelArena.EventHistoryActionPolicy.actionStepKernel` | `Kernel.comp` | K (D, M) | Retained |
| S105 `MeasurableKernelArena.EventHistoryActionPolicy.coordinateMeasure` | `Measure.map` | P (B, D, K, M, T) | Retained |
| S106 `MeasurableKernelArena.EventHistoryActionPolicy.pathMeasure` | `Kernel.traj` | T (B, D, K, M) | Retained |
| S107 `MeasurableKernelArena.EventHistoryActionPolicy.pathStepKernel` | `Classical.propDecidable` | B, D (K, M) | Retained |
| S108 `MeasurableKernelArena.EventHistoryActionPolicy.prefixMeasure` | `Measure.map` | P (B, D, K, M, T) | Retained |
| S109 `MeasurableKernelArena.EventHistoryActionPolicy.stateCoordinateMeasure` | `Measure.map` | P (B, D, K, M, T) | Retained |
| S110 `MeasurableKernelArena.EventHistoryActionPolicy.statePathMeasure` | `Measure.map` | M (B, D, K, T) | Retained |
| S111 `MeasurableKernelArena.recordedTransition` | `Kernel.map` | D, M | Retained |

### [GameTheory.ExtensiveGame.Simulation.Kernel.Execution](../../EconCSLib/GameTheory/ExtensiveGame/Simulation/Kernel/Execution.lean)

| ID / declaration | Original blocker | Routes (inherited) | Result |
|---|---|---|---|
| S112 `KernelArena.Policy.toMeasurable` | `toMeasurableKernel` | W (B, F) | Retained |
| S113 `KernelArena.Policy.toMeasurableKernel` | `Classical.propDecidable` | F, B | Retained |
| S114 `MeasurableKernelArena.ActionPolicy.actionStepKernel` | `Kernel.comp` | K | Retained |
| S115 `MeasurableKernelArena.ActionPolicy.stepKernel` | `Classical.propDecidable` | B, D (K) | Retained |

### [GameTheory.ExtensiveGame.Simulation.Kernel.HistoryPath](../../EconCSLib/GameTheory/ExtensiveGame/Simulation/Kernel/HistoryPath.lean)

| ID / declaration | Original blocker | Routes (inherited) | Result |
|---|---|---|---|
| S116 `MeasurableKernelArena.HistoryActionPolicy.actionStepKernel` | `Kernel.comp` | K | Retained |
| S117 `MeasurableKernelArena.HistoryActionPolicy.coordinateMeasure` | `Measure.map` | P (B, D, K, T) | Retained |
| S118 `MeasurableKernelArena.HistoryActionPolicy.pathMeasure` | `Kernel.traj` | T (B, D, K) | Retained |
| S119 `MeasurableKernelArena.HistoryActionPolicy.pathStepKernel` | `Classical.propDecidable` | B, D (K) | Retained |
| S120 `MeasurableKernelArena.HistoryActionPolicy.prefixMeasure` | `Measure.map` | P (B, D, K, T) | Retained |

### [GameTheory.ExtensiveGame.Simulation.Kernel.RealizedInformation](../../EconCSLib/GameTheory/ExtensiveGame/Simulation/Kernel/RealizedInformation.lean)

| ID / declaration | Original blocker | Routes (inherited) | Result |
|---|---|---|---|
| S121 `MeasurableKernelArena.EventInformation.RealizedActionPolicy.realizedKernel` | `Kernel.snd` | K | Retained |
| S122 `MeasurableKernelArena.EventInformation.RealizedActionPolicy.toEventHistoryActionPolicy` | `realizedKernel` | W (K) | Retained |

### [GameTheory.ExtensiveGame.Simulation.Kernel.StatePath](../../EconCSLib/GameTheory/ExtensiveGame/Simulation/Kernel/StatePath.lean)

| ID / declaration | Original blocker | Routes (inherited) | Result |
|---|---|---|---|
| S123 `MeasurableKernelArena.ActionPolicy.pathStepKernel` | `stepKernel` | W (B, D, K) | Retained |

### [GameTheory.ExtensiveGame.Simulation.Presentation.Chance.Measurable](../../EconCSLib/GameTheory/ExtensiveGame/Simulation/Presentation/Chance/Measurable.lean)

| ID / declaration | Original blocker | Routes (inherited) | Result |
|---|---|---|---|
| S124 `ExtensiveGame.ObservedChanceGame.MeasurablePresentation.compiledPolicy` | `MeasurableKernelArena.EventInformation.RealizedActionPolicy.toEventHistoryActionPolicy` | W (K) | Retained |
| S125 `ExtensiveGame.ObservedChanceGame.MeasurablePresentation.eventPathMeasure` | `MeasurableKernelArena.EventHistoryActionPolicy.pathMeasure` | W (B, D, K, M, T) | Retained |
| S126 `ExtensiveGame.ObservedChanceGame.MeasurablePresentation.statePathMeasure` | `MeasurableKernelArena.EventHistoryActionPolicy.statePathMeasure` | W (B, D, K, M, T) | Retained |

### [GameTheory.ExtensiveGame.Simulation.Presentation.Chance.MeasurableHistory](../../EconCSLib/GameTheory/ExtensiveGame/Simulation/Presentation/Chance/MeasurableHistory.lean)

| ID / declaration | Original blocker | Routes (inherited) | Result |
|---|---|---|---|
| S127 `ExtensiveGame.ObservedChanceGame.MeasurableHistoryModel.discrete` | `ObservedGame.MeasurableHistoryModel.discrete` | W (F) | Retained |
| S128 `ExtensiveGame.ObservedGame.MeasurableHistoryModel.discrete` | `KernelArena.toMeasurable` | W (F) | Retained |

### [GameTheory.ExtensiveGame.Simulation.Presentation.Chance.Realized](../../EconCSLib/GameTheory/ExtensiveGame/Simulation/Presentation/Chance/Realized.lean)

| ID / declaration | Original blocker | Routes (inherited) | Result |
|---|---|---|---|
| S129 `ExtensiveGame.ObservedChanceGame.AnalyticHistoryArena` | `KernelArena.toMeasurable` | W (F) | Retained |

### [GameTheory.ExtensiveGame.Simulation.Presentation.Kernel.Core](../../EconCSLib/GameTheory/ExtensiveGame/Simulation/Presentation/Kernel/Core.lean)

| ID / declaration | Original blocker | Routes (inherited) | Result |
|---|---|---|---|
| S130 `ExtensiveGame.ObservedGame.MeasurableKernelPresentation.KernelBehavioralProfile.compiledPolicy` | `MeasurableKernelArena.EventInformation.RealizedActionPolicy.toEventHistoryActionPolicy` | W (K) | Retained |
| S131 `ExtensiveGame.ObservedGame.MeasurableKernelPresentation.KernelBehavioralProfile.eventPathMeasure` | `MeasurableKernelArena.EventHistoryActionPolicy.pathMeasure` | W (B, D, K, M, T) | Retained |
| S132 `ExtensiveGame.ObservedGame.MeasurableKernelPresentation.KernelBehavioralProfile.statePathMeasure` | `MeasurableKernelArena.EventHistoryActionPolicy.statePathMeasure` | W (B, D, K, M, T) | Retained |

### [GameTheory.ExtensiveGame.Simulation.Restart.Observed](../../EconCSLib/GameTheory/ExtensiveGame/Simulation/Restart/Observed.lean)

| ID / declaration | Original blocker | Routes (inherited) | Result |
|---|---|---|---|
| S133 `ExtensiveGame.ObservedGame.MeasurableKernelPresentation.KernelBehavioralProfile.freshRestartEventPathMeasure` | `MeasurableKernelArena.EventHistoryActionPolicy.pathMeasure` | W (B, D, K, M, T) | Retained |
| S134 `ExtensiveGame.ObservedGame.MeasurableKernelPresentation.KernelBehavioralProfile.normalizedContinuationEventPathMeasure` | `Measure.map` | M (B, D, K, T) | Retained |

### [GameTheory.ExtensiveGame.Simulation.Restart.Trajectory](../../EconCSLib/GameTheory/ExtensiveGame/Simulation/Restart/Trajectory.lean)

| ID / declaration | Original blocker | Routes (inherited) | Result |
|---|---|---|---|
| S135 `MeasurableKernelArena.EventHistoryActionPolicy.absoluteFinitePrefixMeasureFromPrefix` | `Measure.map` | P (B, D, K, M, T) | Retained |
| S136 `MeasurableKernelArena.EventHistoryActionPolicy.freshRestartFinitePrefixMeasure` | `Kernel.partialTraj` | P (B, D, K, M) | Retained |
| S137 `MeasurableKernelArena.EventHistoryActionPolicy.splicedFreshAbsolutePathMeasure` | `Measure.map` | M (B, D, K, T) | Retained |
| S138 `MeasurableKernelArena.EventHistoryActionPolicy.splicedFreshFinitePrefixMeasure` | `Measure.map` | P (B, D, K, M, T) | Retained |

## Validation

The implementation is checked by ordinary module compilation, exact functional
equality to `Set.projIcc`, and the existing non-atomic semantic consumers.
Additional local checks cover the root, a negative terminal action, an interior
rational action, and an action above one. Proof axioms and compiled-data
computability are checked separately: classical reasoning in erased proof
fields is permitted, while the function's data body must compile.

Final build and environment-audit results are recorded in the linked
[migration checkpoint](efg-computability-migration.md). Temporary compiler
probes are not library modules and introduce no public API or audit exclusions.
