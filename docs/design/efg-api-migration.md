# EFG Downstream Migration

This note records the source-level changes made while converging the EFG
canonical facades. The current EFG layer is pre-stability: there is no
external source-compatibility guarantee, and evidence-backed hard migration is
allowed when internal consumers, regressions, lifecycle rows, design notes,
and audits are updated together. Redirect-only and zero-consumer duplicate
spellings are not retained for hypothetical users.

## Mathematical review repairs (2026-09-06)

The former `countablySupportedMixedToBehavioral_boundedHistoryLaw` is now
`finiteLawMixedToBehavioral_boundedHistoryLaw`, with the same mathematical
statement and updated internal/example consumers. No compatibility alias is
retained. The current mixed, behavioral, chance, and discrete-general inputs
are finite rational laws; historical PMF descriptions below do not enlarge
their scope. The theorem permits infinite ambient information carriers and
proves bounded-history `FiniteLaw.Equivalent`, not general countably supported
PMF realization or complete infinite-path equality.

Well-founded determinacy signatures are unchanged. Their scope documentation
now explicitly includes the existing `BackwardInductionData` argument and its
complete finite action lists. The structural hypotheses by themselves do not
give an implemented arbitrary-branching determinacy theorem.

## Import migration

| Former dependency | Required import now |
|---|---|
| occurrence-sensitive `GameTree` compiler obtained from `import EconCSLib` | `import EconCSLib.GameTheory.ExtensiveGame.Interface.Compilation.Discrete` |
| bounded deterministic, observed behavioral, or finite-law kernel execution obtained from `Interface.Execution.Discrete` | `Interface.Execution.Finite` |
| infinite discrete supplied `Arena.pathLaw`, finite-marginal certificates, or bounded partial stopping | `Interface.Execution.Infinite` |
| measurable-kernel execution obtained transitively | `Interface.Execution.Analytic` |
| strict representation morphisms, information refinements, PMF couplings, or weak simulations | `Interface.Relations.Discrete` |
| strict/refinement/weak preservation vocabulary, complete-path realizations, law couplings, or compiler preservation packages | `Interface.Preservation` |
| bounded pure/behavioral/mixed Nash, termination, or finite Kuhn transfer | `Interface.Equilibrium.Discrete` |
| measurable path utility, constructive kernel Nash, absolute-prefix continuation, or conditioning | `Interface.Equilibrium.Analytic` |
| fresh-clock restart declarations | `Interface.Restart` |
| finite observed-EFG compilers or PMF FOSG serialization | `Interface.Compilation.Discrete` |
| both restart and compiler branches from one legacy import | import both `Interface.Restart` and `Interface.Compilation.Discrete` explicitly |

### Payoff-free structural ownership and terminal decisions

The canonical minimal carrier/import spine moved to:

```lean
import EconCSLib.GameTheory.ExtensiveGame.Structural.Basic
import EconCSLib.GameTheory.ExtensiveGame.Structural.Reachability
import EconCSLib.GameTheory.ExtensiveGame.Structural.History
```

`ExtensiveGame.Basic` and
`ExtensiveGame.Execution.{Reachability,History}` remain only for the
state-payoff `ExtensiveGame` carrier and its payoff-aware projections. New
payoff-free code should use the `Structural.*` owners or
`Interface.StructuralCore`.

Constructors and maps for `ControlledObservedGame` must now supply
nonterminality to `infoAt`, `infoAt_observe`, and `actionEquiv`, in addition
to the mover equality. The extra proof is a semantic repair: terminal mover
labels are permitted by `ControlledGame`, but they no longer generate
information states or strategy coordinates. Internal complete-information,
morphism, subgame, and recall constructors were migrated in the same change.

The root aggregate exports finite/PMF execution and the standalone finite
`GameTree`/backward-induction and exact zero-sum chance-tree tracks. Infinite
discrete paths, historical endpoint-policy equilibrium, Arena extraction,
Zermelo, and the observed-EFG reference compilers now require explicit
imports.

The old `Interface.Execution.Discrete`, `Interface.Relations`,
`Interface.Equilibrium`, `Interface.Compilation`, and
`Interface.SimulationFramework` paths were deleted. Callers must replace them
with the smallest rows above; no same-name redirect stubs remain.

### Payoff-aware definitions now project to controlled owners

The state-payoff `ObservedGame` carrier remains supported, but its pure
strategy/profile, decision-witness, represented-information,
mover-coherence, and finite-EFG types are now definitional projections of the
corresponding `ControlledObservedGame` owners. Discrete behavioral
strategy/profile types likewise project to the payoff-free declarations in
`Observed.Controlled.Law.Discrete`.

Existing type-directed code remains definitionally compatible. New general
theorems should be stated on the controlled owner and specialized through
`toControlledObservedGame`; only payoff evaluation stays under
`ObservedGame`.

The discrete chance adapter is now bidirectional:

```lean
ObservedChanceGame.toDiscreteControlledObservedChanceGame
ObservedChanceGame.ofDiscreteControlledObservedChanceGame
```

Forgetting after attaching a payoff recovers the payoff-free game, while
reattaching an observed chance game's existing payoff after forgetting
recovers the original payoff-aware game.

### Deleted redirect-only paths

The hard migration also deleted:

- `ExtensiveGame.Play` and `ExtensiveGame.BehaviorStrategy`;
- `FOSG.FOSGSequentialization`;
- `Observed.{Morphism,Refinement,BehaviorRefinement,DeferredSampling,KuhnConditioning}`;
- `Observed.PathLawEquivalence`, whose zero-consumer payoff-aware spellings
  duplicated the authoritative controlled path-law carrier;
- `Simulation.ObservedMeasurableKernelRestartCompatibility`;
- `ExtensiveGame.Probability.{ConditionalSampling,ConditionalProduct,DeferredSampling,FiniteProductCoupling}`;
- `GameForm.Continuation`;
- the declaration-free `Observed.Morphism.Fiber` forwarding path.

Use the defining leaves documented in
[`efg-public-api.md`](efg-public-api.md). The four historical broad-import
boundary examples were removed along with their imports. The canonical
`Observed.Controlled.Infrastructure` and
`Observed.Controlled.Morphism` aggregate facades remain because their exact
navigation roles are governed.

### Controlled infrastructure and morphism import paths

During EFG pre-stability, the flat paths

```lean
import EconCSLib.GameTheory.ExtensiveGame.Observed.ControlledInfrastructure
import EconCSLib.GameTheory.ExtensiveGame.Observed.ControlledMorphism
```

were removed. Their canonical aggregate replacements are:

```lean
import EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Infrastructure
import EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Morphism
```

No forwarding stubs remain at the flat paths. During that path migration every
declaration kept its namespace, parameters, and full declaration name; only
imports changed. New internal code should import the narrow owner:

| Need | Narrow defining import |
|---|---|
| represented information or mover coherence | `Observed.Controlled.Infrastructure.WellFormed` |
| pure controlled execution | `Observed.Controlled.Infrastructure.Core` |
| lawful roots and subgame systems | `Observed.Controlled.Infrastructure.Subgame` |
| finite EFG hypotheses | `Observed.Controlled.Infrastructure.Finite` |
| quasistrategies | `Observed.Controlled.Infrastructure.Quasi` |
| classic or event-clock private/public recall; silent-event traces | `Observed.Controlled.Infrastructure.Recall` |
| structural Hom/Iso, information refinement, or strategy transport | `Observed.Controlled.Morphism.Core` |
| lawful-subgame transport | `Observed.Controlled.Morphism.Subgame` |
| recall transport | `Observed.Controlled.Morphism.Recall` |

This is an import-ownership migration, not a declaration rename.
`Controlled.Infrastructure.Recall` no longer exposes finite or length
declarations transitively, and `Controlled.Morphism.Core` no longer exposes
subgame or recall transport transitively. Callers that intentionally relied
on broad visibility can import the corresponding canonical aggregate facade.

The complete hierarchy and the distinction between a declaration-free
aggregate facade and a payoff-aware module under `.Compat` are catalogued in
[`efg-controlled-api.md`](efg-controlled-api.md).

### FOSG root-free compiler value

The serialized observed chance-game value does not depend on a continuation
root predicate. New code that needs only the compiled game should use:

```lean
FOSG.Sequentialization.observedChanceGameCore G D rootPayoff
```

Attach caller-selected roots separately with
`FOSG.Sequentialization.rootPresentation G D rootPayoff sourceDeclaredRoot`.
The established
`observedChanceGame G D rootPayoff sourceDeclaredRoot` spelling remains a
definitionally equal compatibility wrapper, so existing calls and
dependent types continue to elaborate unchanged.

## Infinite discrete computability migration

The infinite discrete facade no longer constructs `Arena.stepKernel`,
`Arena.trajectoryKernel`, or an Ionescu--Tulcea path measure. Those two kernel
definitions, their Markov instances and step/trajectory helper theorems were
removed. A caller that has an analytic kernel construction supplies its
resulting probability measure and proves the relevant realization equation;
`Simulation.Kernel.DiscreteBridge` records that supplied equality.

The hard-migrated operations are:

| Former contract | Current contract |
|---|---|
| `Arena.pathMarginal ... : Measure History` | executable `FiniteLaw History` computed by bounded evolution |
| `Arena.pathLaw policy current` | `Arena.pathLaw policy current supplied`, a projection of a supplied `ProbabilityMeasure` |
| total `Arena.terminalTime path : WithTop Nat` | bounded `Arena.terminalTime path fuel : Option Nat` |
| zero-defaulting `Arena.terminalPayoff payoff path : Real` | `Arena.terminalPayoff payoff path fuel : Option Real` |
| measure-evaluated unfinished mass | exact executable `ℚ≥0` event mass of the bounded `FiniteLaw` marginal |
| measure-valued `stoppedPayoffLaw` | executable `FiniteLaw Real` |
| internally mapped `terminalPayoffLaw` | projection of a caller-supplied terminal-payoff `ProbabilityMeasure` |

`Observed.InfiniteExecution.pathLaw` and
`DiscreteControlledObservedChanceGame.behavioralPathLaw` likewise take the
complete path law explicitly. Their finite-marginal theorems take the exact
coordinate certificate explicitly. The discrete
`behavioralCompletePathLawSemantics` constructor now receives complete path
laws, bounded measure laws, executable-prefix equalities, coordinate-marginal
equalities, and almost-sure legality. Almost-sure winning under a stochastic
history policy similarly receives the probability law and legality
certificate instead of invoking a hidden canonical constructor.

The measure-producing
`CompletePathLawSemantics.interpretedHistoryLaw` helper was removed. Outcome,
terminal-history, and arbitrary-history equivalence predicates map the
carrier's supplied bounded laws only inside `Prop`. The former namespace
definition `boundedCompleteHistoryLaw` is now a structure field, paired with
`boundedCompleteHistoryLaw_eq_map`.

## Law-semantics migration

The pre-release `CompletePathLawSemantics` record is intentionally stricter.
Direct record literals must now provide:

```lean
{ Strategy := ...
  pathLaw := ...
  pathLaw_isProbability := ...
  pathLaw_ae_legal := ...
  boundedCompleteHistoryLaw := ...
  boundedCompleteHistoryLaw_eq_map := ... }
```

`pathLaw_isProbability` rules out the zero measure and
`pathLaw_ae_legal` uses the canonical initial-coordinate, legal-step, and
terminal-absorption predicate. Local-kernel agreement is no longer inferred
or stored in the maximum carrier; prove `RealizesExecution` or
`ExecutionCoherent` separately. The former downstream
`ObservedChanceGame.CompletePathLawSemantics` compatibility spelling was
hard-deleted after a source/docs/test consumer audit found no client. Use the
authoritative `ControlledObservedGame.CompletePathLawSemantics`,
`CompletePathLawEquivalentAt`, and `CompletePathLawRealization` declarations
directly. The
`DiscreteControlledObservedChanceGame.behavioralCompletePathLawSemantics`
packages caller-supplied discrete complete-path and bounded-marginal data
without introducing a second payoff-aware semantic owner or manufacturing a
measure from finite prefixes.
The carrier is only a family of lawful per-root marginals; it does not
automatically define one common causal process. Restart, conditioning, and
cross-root coherence remain additional certificates.

The bounded discrete raw structure was renamed:

| Former pre-release name | Current contract |
|---|---|
| `BoundedCompleteHistoryLawSemantics` | `BoundedHistoryLawFamily` (raw history-valued PMF data) |
| `behavioralBoundedCompleteHistoryLawSemantics` | `behavioralCertifiedExecutionLaw` (normalization, reachable legality, terminal absorption, and exact behavioral-executor equality) |

Execution-facing downstream code should consume
`CertifiedBehavioralExecutionLaw` or its
`toBoundedHistoryLawFamily` projection rather than present an arbitrary raw
family as execution semantics.

The former generic terminal-law name was split:

| Former pre-release meaning | Current name |
|---|---|
| arbitrary `History → History` transform | `HistoryTransformLawEquivalentAt` |
| transform proved terminal by its codomain | `TerminalHistoryLawEquivalentAt`, using `Arena.TerminalHistoryFrom` |

The maximum carrier has no PMF/countability/chance tag. Use
`Controlled.Law.DiscretePath` for discrete behavioral execution and
`Controlled.Law.Analytic` for an assembled measurable-kernel execution. The
latter requires an explicit almost-sure canonical-legality proof.

Payoff-free declarations now live in `Controlled.Infrastructure`,
`Controlled.Morphism`, `Controlled.Law.Discrete`, `Controlled.Law`,
`Winning.Basic`, and `Winning.Determinacy`. Existing payoff-aware projection
lemmas are available from the corresponding `Controlled.Compat.*` modules.
Clients that imported an implementation file directly may need to add that
explicit adapter import; public `Interface.*` facades provide their documented
surface.

## Reachability, evaluator, and recall migration

- Pure execution/SPE/winning callers should pass
  `ControlledGame.NoChanceOnHistories`. A global `NoChance` proof can be
  converted with `.noChanceOnHistories`; it is no longer necessary to rule out
  chance nodes in unreachable ambient components.
- The old arbitrary-evaluator equilibrium spellings
  `IsSubgamePerfectOnAt` and `IsStandardSubgamePerfectAt` were renamed
  `IsEvaluatorContinuationEquilibriumOnAt` and
  `IsEvaluatorContinuationEquilibriumAt`.
  A short-lived `EvaluatorExecutionCertificate` /
  `IsStandardEFGSubgamePerfectAt` experiment was removed during pre-stability:
  its execution carrier and legality predicate were caller-defined and thus
  did not certify canonical EFG execution. Operational standard-SPE names
  remain on concrete execution layers.
- `HasSignalPerfectRecall`, `SignalPerfectRecall`, and
  `HasPublicPerfectRecall` were hard-renamed to their
  `EventClock`-qualified forms. The old trace appends one signal per
  transition. Asynchronous models should supply `SignalTraceBuilder`, whose
  `eventSignal : ... → Option Signal` permits silent events.
- Pure profiles are inhabited directly because strategies range over
  `RepresentedInfo`. `PureStrategyAvailabilityCertificate` now means the
  stronger legacy property that every raw information value is represented;
  `ReachablePureStrategyModelCertificate` additionally supplies reachable
  no-chance. These bundles intentionally omit finiteness, payoff, probability,
  recall, and termination.

## Record-field migration

`ControlledObservedGame.FiniteEFGHypotheses.finiteAction` was hard-migrated
in place on 2026-09-02 from a per-history `Finite` proposition to a
per-history explicit `Fintype`. This is a one-for-one certificate-type change
with no declaration or module growth. All in-repository certificate literals
now supply constructive enumerations directly; no compatibility field or
alias is retained. The bounded finite unfolding builds its state enumeration
from exact-length history decomposition and does not recover a `Fintype` by
classical choice.

The four finite decision certificates now use the single explicit field

```lean
finiteDecisionPresentation :
  ∀ i,
    (Σ n : ℕ, G.RepresentedInfo i ≃ Fin n) ×
      (∀ information : G.RepresentedInfo i,
        DecidableEq (G.InfoAction i information.1))
```

This hard-replaces the former propositional `finiteRepresentedInfo` field in
`FiniteInformationHypotheses`, `FiniteNoAbsentMindednessHypotheses`, and
`FiniteKuhnHypotheses`, and is also the finite decision field of
`FiniteEFGHypotheses`. The equivalence supplies a stable coordinate order;
the second component supplies constructive equality for dependent action
fibers. These records live in `Type`, and no compatibility field is retained.

`FiniteKuhnHypotheses` now stores `recallCertificate : RecallCertificate`
instead of a `PerfectRecall` proposition. Classic perfect recall follows
directly from `recallCertificate.perfectRecall`, while `noAbsentMindedness`
remains the derived theorem consumed downstream; no replacement selector is
added.
`FiniteEFGHypotheses.toFiniteKuhnHypotheses` consequently takes an explicit
recall certificate. The two `PerfectRecall.toRecallCertificate` data
selectors were deleted: callers must construct or receive certificate data
explicitly. Classical representative selection remains confined to the pure
proposition `Nonempty RecallCertificate ↔ PerfectRecall`.

The following pre-release field labels were semantically too strong. Update
named record literals as follows:

| Structure family | Old field | Current field |
|---|---|---|
| `ContinuationGameForm`, `IndexedContinuationGameForm` | `IsSubgameRoot` | `IsDeclaredRoot` |
| their `Hom`, `Iso`, and relation structures | `map_subgameRoot` | `map_declaredRoot` |
| their root-coverage predicates | `SubgameRootSurjective`, `SubgameRootReflecting` | `DeclaredRootSurjective`, `DeclaredRootReflecting` |
| former `ObservedGame` root fields | `IsDesignatedContinuationRoot`, `init_isDesignatedContinuationRoot` | external `RootPresentation.IsRoot`, `RootPresentation.init_isRoot` |
| observed isomorphism/refinement structures | embedded `map_designatedContinuationRoot` metadata | external root-presentation correspondence predicates |
| `FOSG.WeakSerialization` | target `ObservedGame.IsDesignatedContinuationRoot` | explicit `targetRoots : RootPresentation` and `targetRoots.IsRoot` |

For example:

```lean
-- before
{ Strategy := Strategy
  Root := Root
  IsSubgameRoot := roots
  Outcome := Outcome
  outcome := outcome }

-- now
{ Strategy := Strategy
  Root := Root
  IsDeclaredRoot := roots
  Outcome := Outcome
  outcome := outcome }
```

An observed presentation and its analysis roots now use separate values:

```lean
def observed : ObservedGame N U :=
  { base := base
    -- observation and information fields omitted
  }

def roots : observed.RootPresentation :=
  { IsRoot := selected
    init_isRoot := init_mem }
```

Changing `roots` no longer changes observed-game identity. The former embedded
designated-root declaration and its all-history compatibility adapter were
removed: no value can recover arbitrary root metadata formerly stored in a
record value, and widening it would be unsound. Root-aware Nash, continuation,
and realization APIs accept a `RootPresentation` explicitly.

## Partial conditioning and explicit off-path migration

`FiniteLaw.conditionOnFiber` now returns `Option (FiniteLaw α)`. A
zero-mass fiber returns `none`; the conditioning layer no longer manufactures
an arbitrary law for an impossible observation. The successful branch is
carried explicitly: `mass_conditionOnFiber` takes both the resulting
`conditioned` law and an equality
`conditionOnFiber ... = some conditioned`. Equivalence and finite-product
conditioning theorems use `Option.Rel`, so they preserve absence instead of
silently choosing a replacement posterior.

The Kuhn posterior API propagates the same partiality. In particular,
`MixedStrategy.conditionOnDecisions`, `conditionalActionLaw`,
`posteriorAfterDecisions`, and `sequentialConditionalActionLaw`, together with
`BehavioralStrategy.actionLawsAfterDecisions`, all return `Option`. The two
sequential posterior builders use `List.foldlM`, and therefore stop at the
first zero-mass prefix. `MixedProfile.posteriorAfterDecisions` returns the
dependent family `(i : N) → Option (G.MixedStrategy i)`, rather than choosing
one total posterior profile. Results that consume a concrete posterior now
take success evidence explicitly: for example,
`toMixed_posteriorAfterDecisions_actionMarginal` takes
`hposterior : ... = some posterior`, while
`posteriorMixedHistoryLawAlong_eq_behavioral` takes a concrete
`posteriorProfile` and a successful-posterior equality for every player.

Total behavioral strategies are formed only at the next layer.
`behavioralizeMixedFrom`, `behavioralizeMixedProfileFrom`, and
`FiniteKuhnHypotheses.mixedToBehavioralProfileAt` take a caller-supplied
`offPath` strategy or profile and use it exactly when the posterior is `none`.
The arbitrary-mixed execution and law APIs thread that assessment through
their calls, including `mixedToBehavioral_stoppedHistoryLawFrom`,
`finiteLawMixedToBehavioral_boundedHistoryLaw`,
`mixedToBehavioral_stoppedPayoffLawFrom`, `mixedToBehavioralLawHomAt`, the
mixed-deviation and finite-Kuhn realization/Nash theorems, and the three
`mixedToBehavioral_*LawEquivalentAt` declarations in `LawEquivalence`.
Behavioral-table realization uses the source behavioral strategy itself as
the corresponding fallback.

Generic posterior, behavioralization, execution, and law-equivalence APIs now
require the dependent constructive instance

```lean
∀ (i : N) (information : G.RepresentedInfo i),
  DecidableEq (G.InfoAction i information.1)
```

Callers of the generic APIs must provide it. Finite-Kuhn wrappers install it
from `FiniteKuhnHypotheses.finiteDecisionPresentation`. This was a hard
migration: no total zero-mass conditioning wrapper, implicit off-path default,
or old-signature compatibility alias is retained.

## `SubgameSystem` literals

`ObservedGame.SubgameSystem` separates selection from structural lawfulness.
Construct it with exactly:

```lean
{ IsRoot := roots
  init_isRoot := init_mem
  lawful := by
    intro root hroot
    exact
      { root_information_singleton := by
          -- prove the proper-root singleton condition
          ...
        information_closed := by
          -- prove information-set closure after the root
          ... } }
```

`root_information_singleton` and `information_closed` remain derived
accessors on a completed `SubgameSystem`. Presentation designation is not a
field; prove `SubgameSystem.IsVisibleIn roots` separately when needed.
Use `CompleteSubgameSystem` only when the selected roots cover every
`IsLawfulSubgameRoot`.

## Solution-concept names

The old `IsSPEForPayoff` and unqualified `Is...SubgamePerfect` spellings were
not retained. Choose the name that states the actual root scope:

- `IsNashOnRoots...` or `IsNashOnPresentationAt ... roots` for explicitly
  selected presentation roots;
- `Is...SubgamePerfectOn ... system` for one explicit lawful system; or
- `Is...StandardSubgamePerfect ... completeSystem` for coverage of every
  structurally lawful root.

For arbitrary `ContinuationSemantics`, use the
`IsEvaluatorContinuationEquilibrium...` names. There is intentionally no
generic standard-EFG-SPE spelling for an arbitrary evaluator. A future common
operational abstraction must first be derived from at least two concrete
execution modes and must use canonical root-local strategies, deviations, and
complete-play/path-law execution rather than caller-defined legality.

A caller-declared or presentation-designated root predicate is not, by itself,
a standard-subgame certificate. New code must pass roots explicitly.

## Completed declaration migrations

### Supplied analytic data and effective profile assembly (2026-09-03)

This is a **partial migration of computability prompts 8–10**, not their
completion. The elaborated audit decreased from **262 declarations / 52
modules** to **214 declarations / 45 modules** (62 library, 152 example
declarations). All 48 removed identities are listed below. There are no new
identities, no per-module increases, and no changes to the checked baseline.

| Surface | Current supplied data or executable input |
|---|---|
| `ActionPolicy.endpointKernel`, `endpointMeasure`, and their endpoint equations | A supplied `EndpointExecution policy hterminal` contains the finite-horizon kernel family and exact zero/successor equations. Kernel composition is used in certificates and proofs, not in the data projections. |
| `ActionPolicy.pathMeasure`, `prefixMeasure`, `coordinateMeasure`, and their law theorems | A supplied `PathExecution policy hterminal` contains the full state-path measure and exact prefix/coordinate marginals. The stopped step and its Ionescu–Tulcea law remain the mathematical specification. |
| Stationary-history path comparisons, the complete discrete/analytic path bridge, and `AnalyticPresentation.compiled_statePathMeasure` | Their state-path-law inputs now include the corresponding `PathExecution`. The finite-discrete coordinate theorem still proves the same exact `FiniteLaw` equality. |
| `InformationRoles` and player-profile assembly | Three new data fields provide tag equality and terminal/player membership decisions: `playerTagDecidableEq`, `terminalInformationDecidable`, and `playerInformationDecidable`. The three concrete role examples use explicit finite-node decisions. Profile assembly and unilateral replacement use these decisions with the supplied kernels. |
| `MeasurablePresentation.fixedChanceKernel` | Projects the new supplied `chanceKernel`; `chanceKernel_isSFinite` and `chanceKernel_eq` certify s-finiteness and agreement at every represented chance prefix. The reference-profile choice and empty-profile default are gone. |
| `AnalyticPresentation.toMeasurablePresentation` | Requires the concrete chance-kernel family, its s-finiteness, and its chance-prefix compatibility certificate as explicit arguments. |
| `canonicalContinuationPrefixMass` and conditional event/state laws | A supplied `ConditionalContinuation profile` owns exact prefix masses and conditional measures. Both conditional-law functions now require an explicit `hpositive : prefixMass ≠ 0`. Zero-mass roots have no value in this partial interface. |
| `conditionalContinuationExpectedUtility` | Requires `ConditionalEvaluation evaluation profile`, with supplied values certified to equal the conditional integrals, and the same positive-mass witness. |
| Continuous kernel regression | `AnalyticInput` supplies the uniform transition and unique-action kernels with exact volume/Dirac certificates. Endpoint and path certificates are supplied separately. The no-discrete-PMF results are preserved. |

`EndpointExecution.nonempty`, `PathExecution.nonempty`,
`ConditionalContinuation.nonempty`, and `ConditionalEvaluation.nonempty`
prove mathematical existence in `Prop`. None installs a default instance or
extracts data into an executable definition. Proof-local use of existence
preserves earlier mathematical conclusions without adding runtime selectors.
The analytic import regression rejects use of a conditional event law without
its positive-mass witness.

The endpoint, observed-information, player-profile-assembly,
chance-profile-assembly, observed-conditioning, restart-factorization, and
continuous-example owners are now at zero. The direct prompt owners still
contain **22 identities for prompt 8, 9 for prompt 9, and 16 for prompt 10**.
Remaining work includes arena/one-step adapters, history/event execution,
realized action composition, the remaining analytic presentations, absolute
continuation and restart laws, and their analytic example consumers. The
structural pullbacks, explicit canonical history-prefix builders, and
proposition-valued equilibrium predicates retained their types when their
unnecessary `noncomputable` annotations were removed.

Before migration, the removed identities fell into four categories: structural
kernel pullback or supplied-field projection; analytic measure/kernel or
expectation production; hidden reference-profile selection or classical role
branching; and proof-only equilibrium predicates. Supplied laws replace the
analytic outputs, explicit decisions replace the branching, and proofs remain
in `Prop`.

The following are the exact removed **audit** identities; names that now
project data or perform structural operations remain available in Lean.

- Under `EconCSLib.Examples.ExtensiveGame.ContinuousKernelBoundary`: `continuousArena`, `continuousPolicy`.
- Under `ExtensiveGame.ObservedChanceGame.AnalyticPresentation`: `toMeasurablePresentation`.
- Under `ExtensiveGame.ObservedChanceGame.MeasurablePresentation`: `fixedChanceKernel`, `toKernelBehavioralProfile`, `toKernelPresentation`, `profileAssembly`.
- Under `ExtensiveGame.ObservedGame.MeasurableHistoryModel`: `canonicalContinuationPrefix`, `canonicalEventPrefixOfHistory`, `toArena`.
- Under `ExtensiveGame.ObservedGame.MeasurableHistoryModel.BoundedPathUtility`: `conditionalContinuationExpectedUtility`.
- Under `ExtensiveGame.ObservedGame.MeasurableHistoryModel.BoundedTerminalPayoffExtension`: `IsFreshRestartStandardSubgamePerfect`, `IsFreshRestartSubgamePerfectOn`, `IsNashAtContinuation`, `IsNashAtFreshRestart`, `IsNashOnFreshRestartPresentation`, `IsNashOnPresentation`, `IsStandardSubgamePerfect`, `IsSubgamePerfectOn`.
- Under `ExtensiveGame.ObservedGame.MeasurableKernelPresentation.KernelBehavioralProfile`: `canonicalContinuationPrefixMass`, `conditionalContinuationEventPathMeasure`, `conditionalContinuationStatePathMeasure`.
- Under `ExtensiveGame.ObservedGame.MeasurableKernelPresentation.ProfileAssembly`: `abstractKernel`, `instPlayerInputMeasurableSpace`, `nonterminalAbstractKernel`, `ofReference`, `playerAbstractKernel`, `toKernelBehavioralProfile`, `toRealizedActionPolicy`.
- Under `ExtensiveGame.ObservedGame.MeasurableKernelPresentation.ProfileAssembly.PlayerKernelProfile`: `deviate`, `ofKernelBehavioralProfile`.
- Under `ExtensiveGame.ObservedGame.MeasurableKernelPresentation.ProfileAssembly.PlayerStrategy`: `onPlayerInput`.
- Under `MeasurableKernelArena.ActionPolicy`: `endpointKernel`, `endpointMeasure`, `toHistoryActionPolicy`, `toLatestStateInformationActionPolicy`, `coordinateMeasure`, `pathMeasure`, `prefixMeasure`.
- Under `MeasurableKernelArena.EventHistoryActionPolicy`: `toFullInformationActionPolicy`.
- Under `MeasurableKernelArena.EventHistoryStatistic`: `actionLawIgnoringClock`.
- Under `MeasurableKernelArena.EventInformation.ActionPolicy`: `pullback`, `toEventHistoryActionPolicy`.
- Under `MeasurableKernelArena.EventInformation.ActionRealization`: `pullback`.
- Under `MeasurableKernelArena.EventInformation.RealizedActionPolicy`: `prefixAbstractKernel`, `pullback`.
- Under `MeasurableKernelArena.HistoryActionPolicy`: `toEventHistoryActionPolicy`, `toStatePrefixInformationActionPolicy`.

Verification: the library, complete example suite, finite-law smoke test,
placeholder check, API-growth guard, elaborated computability audit,
governance check, and 18 checker unit tests passed.

### Effective countable presentations (2026-09-03)

Prompt 7 hard-migrated the countable owner and its complete consumer cone.
The elaborated audit decreased from **297 declarations / 55 modules** to
**262 declarations / 52 modules** (108 library, 154 example declarations).
The owner and both countable example modules are zero. No audited identity
was added, no module grew, and the checked baseline was not tightened.

The former automatic analytic constructor has been removed, not wrapped or
aliased. Countability proves a cardinality proposition; it does not provide
runtime enumeration, decidable reachability, measurable kernels, or a
measurable profile. Analytic consumers now take the existing
`AnalyticPresentation` or `MeasurableKernelPresentation` and its profile as
supplied certified data. The generic represented-information, concrete
player/chance compilation, and finite-marginal equalities remain available
from those owners. The fair repeat-or-stop example additionally receives the
exact finite-marginal certificate and still proves unfinished mass `2⁻n`,
almost-sure termination, absence of a finite termination bound, and payoff
convergence from it. This is an explicit assumption boundary, not a claim
that the library now constructs that analytic presentation.

| Former API | Current computational input / API change |
|---|---|
| `CountablePresentation.informationAtHistory` | Requires the state-indexed `Decidable (isTerminal state)` input; its four branch theorems carry the same input |
| `CountablePresentation.informationOfPlayerInformation` | Takes an executable reachability-decision function and returns `Option (CountableInformation G)`; unreachable points return `none`, and the represented-history theorem returns `some` |
| `CountablePresentation.realizedAction` | Takes a concrete complete history instead of an analytic event prefix, plus `DecidableEq (CountableInformation G)`; returns `Option (CompleteHistoryAction G)` |
| `realizedAction_fst`, `realizedAction_player`, `realizedAction_chance` | History preservation requires successful `some bundle` output; matching player/chance equations explicitly return `some` |
| `fallbackAction` | Removed; a mismatched tag produces `none` |
| automatic countability and measurable-space instances | Removed; clients provide actual `Encodable` data and explicit analytic spaces; the existing singleton proofs remain proof-only |
| `eventInformation`, `realization`, `policy`, abstract/realization measure and kernel constructors, `presentation` | Removed; use fields of the supplied `AnalyticPresentation` directly |
| `measurablePresentation`, `kernelPresentation`, `kernelBehavioralProfile` and the countable adapter theorem | Removed; use the existing supplied measurable/kernel presentation and profile interfaces directly |
| countable example theorem families | Take an explicit `AnalyticPresentation`; executable history/action encoders, partial decoders, terminal decisions, tag equality, and reachability decisions are constructed locally |
| fair-termination analytic theorem family | Takes a supplied kernel profile and exact finite-coordinate marginal certificate; its finite `FiniteLaw` process and probability formulas are unchanged |

The complete removed **audit** identity list follows. The three operational
selectors remain under their original names but are now computable; the
remaining listed data constructors/instances were removed. Prefixes below
are exact Lean namespaces.

- Under `ExtensiveGame.ObservedChanceGame.CountablePresentation`:
  `abstractKernel`, `abstractMeasure`, `eventInformation`, `fallbackAction`,
  `informationAtHistory`, `informationOfPlayerInformation`,
  `kernelBehavioralProfile`, `kernelPresentation`, `measurablePresentation`,
  `policy`, `presentation`, `realization`, `realizationKernel`,
  `realizationMeasure`, `realizedAction`.
- Under `ExtensiveGame.ObservedChanceGame`:
  `instCountableAnalyticHistoryActionBundle`,
  `instCountableAnalyticHistoryEventPrefix`,
  `instCountableAnalyticHistoryPathEvent`, `instCountableCountableAction`,
  `instCountableCountableInformation`,
  `instCountableCountableInformationAction`,
  `instCountableReachablePlayerInformation`,
  `instMeasurableSpaceCountableAction`,
  `instMeasurableSpaceCountableInformation`.
- Under `Examples.ObservedChanceCountablePresentationBoundary`:
  `baseHistoryCountable`, `gameHistoryCountable`, `gameInfoActionCountable`,
  `gameInfoStateCountable`, `gameLocalActionCountable`, `presentation`.
- Under `Examples.ObservedChanceCountableSparsePlayersBoundary`:
  `completeHistoryActionCountable`, `historyCountable`, `presentation`.
- Under `Examples.ObservedMeasurableKernelAlmostSureOutcomeBoundary`:
  `analyticProfile`, `presentation`.

Classification before migration: `informationAtHistory` and `realizedAction`
were finite operations with hidden decisions; `informationOfPlayerInformation`
and `fallbackAction` hid reachability/inhabitation witnesses; the seven
countability instances and seven corresponding example instances were
proof-only cardinality results; the two measurable-space instances and all
remaining constructors/projections were analytic presentation data. No
countability proof is eliminated to produce an encoding in the replacement.

Constructor-specific proof helpers were removed with their data constructors:
`eventInformation_apply`, `realizationKernel_apply_terminal`,
`realizationKernel_apply_nonterminal`, `bind_mapped_realization`,
`realizationKernel_isFinite`, `abstractKernel_terminal`,
`abstractKernel_player`, `abstractKernel_chance`,
`abstractKernel_bind_realization_of_mover`,
`abstractKernel_bind_realization_of_chance`, `abstractKernel_isFinite`,
`compiled_kernel`, `compiled`, and
`kernelBehavioralProfile_compiledPolicy` in `CountablePresentation`.
They are not compatibility aliases. For a supplied analytic presentation,
use its `compiled` certificate and the existing
`AnalyticPresentation.compiled_kernel`, `compiled_kernel_of_mover`,
`compiled_kernel_of_chance`, `abstractKernel_eq_of_player_infoAt_eq`, and
`compiled_finite_state_law` theorems. A particular abstract tagged-kernel
formula is now part of the model's supplied analytic data, not a formula
manufactured from countability.

### Computability migration prompts 1–5 (2026-09-02)

The first five computability tasks hard-migrated the finite execution,
termination, GameTree, determinacy, and FOSG sequentialization cones. The
checked elaborated audit fell from 342 declarations in 69 modules to 313 in
59 modules without adding an audited declaration identity.

| Former API or hidden runtime dependency | Current API | Semantic effect |
|---|---|---|
| implicit `KernelArena.instDecidableIsEmptyAction` | an explicit state-indexed `Decidable (IsEmpty (Action state))` input on finite execution and coupling operations | Terminal stopping is executable and no global classical instance is installed |
| `terminalFuel` extracted from `PureTerminatesFrom` | `PureTerminatesAtFuel` plus `PureTerminationPlanAt` | Callers supply executable fuel and prove terminality separately; terminal history, payoff, objective, Nash, and SPE APIs consume that data |
| `GameTree.Subtree.toArenaHistory` | `observedOutcomeFrom` on an explicitly supplied `HistoryFrom` | A proof-only subtree occurrence is no longer eliminated into runtime history data |
| `observedStrategyToPlayerStrategy` and `observedProfileToPlayerProfile` | direct `observedActionAtNode` / `observedOutcomeFrom` evaluation | Observed profiles are evaluated without choosing an inverse strategy, while distinct occurrences remain distinct |
| choice-based `observedToGameForm` | computable `observedToGameForm` using the direct initial-history outcome | Finite compiled outcomes are executable |
| `terminalWinner`, `backwardWinner`, `backwardAction`, `backwardRepresentative`, and `backwardStrategy` with hidden choice | the same computational operations parameterized by `BackwardInductionData` | Terminal winners, action traversal order, and represented-information witnesses are explicit; the first winner-preserving listed action is selected |
| hidden fallback action/history-policy choice in `macroDeterministicPolicy`, `macroPolicy`, `probabilisticWeakSimulation`, `macroExecutionAction`, `initialPolicy`, and `weakSerialization` | `FallbackHistoryPolicy` | Unreachable/off-canonical player states use caller-supplied executable policy data and `DecidableEq` evidence |
| hidden related-source selection in `serializedMacroPolicy`, `macroKernelSimulation`, `serializedMacroPolicy_match`, `serializedBehavioralMacroPolicy`, and `initializedTargetStateLaw` | `MacroPolicyData` | The target boundary resolver, its completeness proof, and target fallback policy are supplied explicitly |

The FOSG continuation and equilibrium APIs now thread `MacroPolicyData` where
their proofs pass through macro execution, and thread only
`FallbackHistoryPolicy` where the weak serializer needs no target-boundary
resolver. Finite state/trace/payoff laws remain `FiniteLaw` values; theorem
statements compare them through `FiniteLaw.Equivalent` and constructive
couplings.

The following former names have explicit replacements. During the 2026-08-03
pre-stability API-debt closeout, every remaining exact deprecated alias in
this table had zero repository source consumers and was hard-deleted. The
table remains as a migration map, not as an inventory of live aliases.

| Removed declaration | Replacement | Since | Semantics |
|---|---|---|---|
| `ControlledObservedGame.PerfectRecall.toRecallCertificate` | explicit `ControlledObservedGame.RecallCertificate` input | 2026-09-02 | Deleted classical data selector; the existence equivalence remains only as a proposition |
| `ObservedGame.PerfectRecall.toRecallCertificate` | explicit `ObservedGame.RecallCertificate` input | 2026-09-02 | Payoff-aware selector deleted with its controlled owner |
| `ControlledObservedGame.AllDecisionInfoRepresented.nonempty_pureStrategy` | `ControlledObservedGame.nonempty_pureStrategy` | 2026-08-14 | The strategy domain is `RepresentedInfo`, so inhabitation needs no full raw-information representation premise |
| `ControlledObservedGame.AllDecisionInfoRepresented.nonempty_pureProfile` | `ControlledObservedGame.nonempty_pureProfile` | 2026-08-14 | Same general inhabitation theorem at profile level |
| `ObservedGame.AllDecisionInfoRepresented.nonempty_pureStrategy` | `ObservedGame.nonempty_pureStrategy` | 2026-08-14 | Payoff-aware projection of the general controlled theorem |
| `ObservedGame.AllDecisionInfoRepresented.nonempty_pureProfile` | `ObservedGame.nonempty_pureProfile` | 2026-08-14 | Payoff-aware projection of the general controlled theorem |
| `ControlledObservedGame.PureStrategyAvailabilityCertificate.nonempty_pureProfile` | `ControlledObservedGame.nonempty_pureProfile` | 2026-08-14 | Removed wrapper ignored its availability certificate |
| `ControlledObservedGame.FiniteEFGHypotheses.nonempty_pureProfile` | `ControlledObservedGame.nonempty_pureProfile` | 2026-08-14 | Removed wrapper ignored its finite certificate |
| `ObservedGame.FiniteEFGHypotheses.nonempty_pureStrategy` | `ObservedGame.nonempty_pureStrategy` | 2026-08-14 | Removed wrapper ignored its finite certificate |
| `ObservedGame.FiniteEFGHypotheses.nonempty_pureProfile` | `ObservedGame.nonempty_pureProfile` | 2026-08-14 | Removed wrapper ignored its finite certificate |
| `FiniteImperfectGame.actionAt_same_info_label` | `FiniteImperfectGame.actionAt_same_info` | 2026-07-29 | Identical transport-aware information-consistency statement |
| `PathOutcomeFromHistory.continueAt` | `PathOutcomeFromHistory.rebaseTailAt` | 2026-07-31 | Same absolute-tail rebasing operation; root objectives now use `PathOutcome.afterHistory` |
| `WinningConditionFrom.continueAt` | `WinningConditionFrom.rebaseTailAt` | 2026-07-31 | Same absolute-tail rebasing operation; root objectives now use `WinningCondition.afterHistory` |
| `WinningConditionFrom.mem_continueAt_iff` | `WinningConditionFrom.mem_rebaseTailAt_iff` | 2026-07-31 | Same membership equivalence |
| `ObservedGame.HasWinningStrategy` | `ObservedGame.HasPathwiseWinningStrategy` | 2026-07-31 | Same pathwise robust predicate; profile-based winning is now separately named |
| `ObservedGame.WinningStrategies` | `ObservedGame.PathwiseWinningStrategies` | 2026-07-31 | Same bundled pathwise strategies |
| `ObservedGame.IsDetermined` | `ObservedGame.HasSomePathwiseWinningStrategy` | 2026-07-31 | Same generic existential; standard determinacy naming is reserved for the two-player disjunction |
| `ObservedGame.isDetermined_of_hasWinningStrategy` | `ObservedGame.hasSomePathwiseWinningStrategy_of_hasPathwiseWinningStrategy` | 2026-07-31 | Same existential packaging result |
| `ObservedGame.isDetermined_iff_isTwoPlayerDetermined` | `ObservedGame.hasSomePathwiseWinningStrategy_iff_isTwoPlayerDetermined` | 2026-07-31 | Same two-player equivalence |
| `ObservedGame.not_both_haveWinningStrategy` | `ObservedGame.not_both_havePathwiseWinningStrategy` | 2026-07-31 | Same exclusivity theorem with explicit pathwise semantics |
| `ObservedGame.GeneralStrategy` | `ObservedGame.DiscreteGeneralStrategy` | 2026-07-31 | Same countably supported `PMF` carrier; the new name does not imply analytic generality |
| `ObservedGame.GeneralProfile` | `ObservedGame.DiscreteGeneralProfile` | 2026-07-31 | Same playerwise discrete carrier |
| `BehavioralStrategy.toGeneral` | `BehavioralStrategy.toDiscreteGeneral` | 2026-07-31 | Same Dirac embedding |
| `BehavioralProfile.toGeneral` | `BehavioralProfile.toDiscreteGeneral` | 2026-07-31 | Same componentwise Dirac embedding |
| former embedded designated-root predicate | `roots.IsRoot` | 2026-08-01 | Removed rather than widened; callers must supply the original root set explicitly |
| former zero-argument root-presentation adapter | explicit `ObservedGame.RootPresentation` value | 2026-08-01 | Removed because no lossless default can recover the former embedded metadata |
| `ObservedGame.IsPresentationVisible` | `ObservedGame.SubgameSystem.IsVisibleIn roots` | 2026-07-31 | Presentation visibility now names the explicit external root presentation |
| `ContinuationSemantics.toIndexedGameForm` | `ContinuationSemantics.toIndexedGameFormOnPresentation roots` | 2026-07-31 | Explicit external root presentation |
| `ContinuationSemantics.toIndexedGameForm_outcome` | `ContinuationSemantics.toIndexedGameFormOnPresentation_outcome roots` | 2026-07-31 | Same outcome computation on an explicit root presentation |
| `ContinuationSemantics.IsNashOnDesignatedContinuationsAt` | `ContinuationSemantics.IsNashOnPresentationAt roots` | 2026-07-31 | Explicit external root presentation |
| `ContinuationSemantics.isNashOnDesignatedContinuationsAt_iff` | `ContinuationSemantics.isNashOnPresentationAt_iff roots` | 2026-07-31 | Same Nash characterization on an explicit root presentation |
| `IsPureNashOnDesignatedContinuationsAtFuel` | `IsPureNashOnRootsAtFuel roots` | 2026-07-31 | Bounded continuation Nash now receives its root scope explicitly |
| `IsBehavioralNashOnDesignatedContinuationsAtFuel` | `IsBehavioralNashOnRootsAtFuel roots` | 2026-07-31 | Bounded behavioral continuation Nash now receives its root scope explicitly |
| `IsMixedNashOnDesignatedContinuationsAtFuel` | `IsMixedNashOnRootsAtFuel roots` | 2026-07-31 | Bounded mixed continuation Nash now receives its root scope explicitly |
| `PureTerminating` | `PureTerminatingOnRoots roots` | 2026-07-31 | Termination is stated on an explicit family of continuation roots |
| `IsPureNashOnDesignatedContinuations` | `IsPureNashOnRoots roots` | 2026-07-31 | Unbounded continuation Nash now receives its root scope explicitly |
| `PureStrategy.toGeneral` | `PureStrategy.toDiscreteGeneral` | 2026-07-31 | Same pure-to-behavioral Dirac embedding |
| `PureProfile.toGeneral` | `PureProfile.toDiscreteGeneral` | 2026-07-31 | Same componentwise embedding |
| `GeneralProfile.behavioralProfileLaw` | `DiscreteGeneralProfile.behavioralProfileLaw` | 2026-07-31 | Same independent PMF product |
| `GeneralProfile.deviate` | `DiscreteGeneralProfile.deviate` | 2026-07-31 | Same component update |
| `GeneralProfile.deviate_same` | `DiscreteGeneralProfile.deviate_same` | 2026-07-31 | Same update-at-player theorem |
| `GeneralProfile.deviate_of_ne` | `DiscreteGeneralProfile.deviate_of_ne` | 2026-07-31 | Same update-away-from-player theorem |

The exact aliases once qualified for `@[deprecated replacement]` because
their statements were unchanged. They are no longer retained because no
external EFG compatibility period has begun. Endpoint versus occurrence
strategies, state re-rooting versus lawful subgames, and designated-root
versus complete-system solution concepts never received aliases because
their semantics differ.

## Example-placement migration

Regression declarations are opt-in examples, not reusable EFG API:

| Former owner | Opt-in module / current namespace |
|---|---|
| `Execution.History` (`Examples.HistoryDiamond.*`) | `EconCSLib.Examples.ExtensiveGame.HistoryDiamond`; declaration names unchanged |
| `Execution.StoppedExecution` (`Examples.TerminalStoppedExecution.*`) | `EconCSLib.Examples.ExtensiveGame.TerminalStoppedExecution`; declaration names unchanged |
| `ImperfectInformation` and `Compiler.FiniteImperfectObserved` (`Examples.ImperfectInformation.*`) | `EconCSLib.Examples.ExtensiveGame.FiniteImperfectCompilation`; declaration names unchanged |
| `StochasticGameTree` (`StochasticGameTree.fairCoin*`) | `EconCSLib.Examples.ExtensiveGame.StochasticTreeCompilation`; names now live under `Examples.ExtensiveGame.StochasticTreeCompilation` |

The recommended library root and granular compilation facade do not import these
examples. Negative import regressions enforce that the former core-namespace
spellings stay absent.

## Completed root migration

On 2026-07-30 the root replaced `Interface.Execution.Discrete` with
`Interface.Execution.Finite`. Infinite path laws are available from
`Interface.Execution.Infinite`; the old combined path was subsequently
deleted during the pre-stability hard migration.
The historical endpoint `GameTreeSPE`, `GameTreeNE`, and
`GameTreeStrategicForm` modules, the niche `FiniteArenaExtraction` bridge, and
`Zermelo` also became explicit imports.

Existing examples now import the implementation paths they use, and
`RootImportBoundary` checks both the retained finite surface and the removed
transitive names. The granular facade and examples builds are the migration
regressions. The later lifecycle closeout deleted redirect-only module paths.
The 2026-08-03 audit additionally removed the zero-consumer
`Observed.PathLawEquivalence` compatibility declarations; the canonical
controlled carrier and its realization theory remain the sole mathematical
owner.

These checks provide machine-checked evidence for source elaboration, the
axiom surface, placeholder policy, module boundaries, and the listed formal
semantic properties. They are not a metamathematically complete certification
of every intended model meaning.

## Executable example decisions and occurrences (2026-09-03, A–C)

The elaborated audit changed from 214 declarations in 45 modules to 194 in
35 modules: 62 library declarations and 132 example declarations remain.
No identity was added and neither checked baseline was changed.

A removed only the two redundant tiny-game modifiers. B replaced eight
classical terminal/equality instances by constructor decisions and executable
finite-field equality. The `AbsentMinded` decision-key instance and
`ReachableNoChance.terminalDecidable` now have example-local scope; their
only consumers were their own examples (the imported bridge consumer also
builds). No general Arena/history instance or mathematical hypothesis changed.

C chooses concrete legal actions for the diamond and reachable one-step
profiles. Equality with the left history inspects the recorded Boolean action.
For `OccurrenceNonIso`, an exhaustive history theorem proves that the only
player-0 decisions are the direct and detour occurrences; their distinct
lengths then decide equality with the second occurrence. This does not replace
general history equality by endpoint or length equality. The old strategy's
exact conditional and its distinction/non-isomorphism theorems remain.
`occurrenceThreatProfile` and `initialContinuationGameForm` needed only marker
removal; `pureHistoryPolicy` becomes executable through the concrete profile.

The two `RandomTermination` Countable instances retain their original names
and propositions, using explicit finite injections inside Prop. This replaces
deriving-generated choice helpers; it neither assumes countability nor adds
an Encodable interface. Countability supports `payoff_measurable`; finite-law
execution and bounded terminal search do not extract its existential witness.

Native execution covers terminal and nonterminal cases (including ghost
states), repeated decision-key erasure, the two route outcomes, a real root
step, distinct occurrence actions, and the lifted threat outcome. Existing
random-termination finite-law and bounded-search regressions still run.
All affected modules/consumers, the stable library and examples,
`tests/FiniteLawSmoke.lean`, placeholder/API-growth/computability/governance
checks, and `git diff --check` passed.

Removed identities (module names below `EconCSLib.Examples.ExtensiveGame`):

| Module | Declaration |
|---|---|
| `AbsentMinded` | `Examples.AbsentMinded.instDecidableEqDecisionKeyFinOfNatNatIntAbsentMindedGame` |
| `DesignatedContinuationSPEBoundary` | `Examples.DesignatedContinuationSPEBoundary.occurrenceThreatProfile` |
| `FiniteImperfectCompilation` | `Examples.ImperfectInformation.tinyObservedGame` |
| `FiniteImperfectCompilation` | `Examples.ImperfectInformation.tinyObservedRecallCertificate` |
| `FiniteReachableUnfolding` | `FiniteReachableUnfolding.routeTerminalOutcome` |
| `HistoryObjectiveContinuation` | `Examples.HistoryObjectiveContinuation.endpointTerminalDecidable` |
| `HistoryObjectiveContinuation` | `Examples.HistoryObjectiveContinuation.profile` |
| `HistoryObjectiveContinuation` | `Examples.HistoryObjectiveContinuation.routeObjective` |
| `HistoryObjectiveContinuation` | `Examples.HistoryObjectiveContinuation.terminalDecidable` |
| `InfiniteInformationKuhnBoundary` | `Examples.InfiniteInformationKuhnBoundary.observedTerminalDecidable` |
| `InfiniteInformationKuhnBoundary` | `Examples.InfiniteInformationKuhnBoundary.terminalDecidable` |
| `OccurrenceNonIso` | `Examples.OccurrenceNonIso.separatingOccurrenceStrategy` |
| `RandomTermination` | `_private.EconCSLib.Examples.ExtensiveGame.RandomTermination.0.Examples.RandomTermination.instCountableHistoryCode.countableToNat._@.EconCSLib.Examples.ExtensiveGame.RandomTermination.1510709156._hygCtx._hyg.9` |
| `RandomTermination` | `_private.EconCSLib.Examples.ExtensiveGame.RandomTermination.0.Examples.RandomTermination.instCountableState.countableToNat._@.EconCSLib.Examples.ExtensiveGame.RandomTermination.4043877091._hygCtx._hyg.12` |
| `ReachableNoChance` | `Examples.ReachableNoChance.initialContinuationGameForm` |
| `ReachableNoChance` | `Examples.ReachableNoChance.profile` |
| `ReachableNoChance` | `Examples.ReachableNoChance.pureHistoryPolicy` |
| `ReachableNoChance` | `Examples.ReachableNoChance.terminalDecidable` |
| `WinningSemantics` | `WinningSemantics.arenaTerminalDecidable` |
| `WinningSemantics` | `WinningSemantics.terminalDecidable` |

## Bounded operations in analytic semantics (2026-09-03, E)

The three existing operations `TerminalPayoffExtension.stoppedUtility`,
`TerminalPayoffExtension.stoppedPathUtility`, and
`BoundedTerminalPayoffExtension.stoppedBoundedPathUtility` in
`ObservedGame.MeasurableHistoryModel` now take
`[(state : G.base.State) → Decidable (G.base.isTerminal state)]`.
They inspect only the requested coordinate and select the supplied terminal
payoff or zero. An effective caller supplies a constructor-based decision;
this does not implement arbitrary real evaluation, integration, or unbounded
termination detection.

Only the nine theorems mentioning those bounded operations and the two
continuation convergence theorems inherit that input. General
`eventualUtility`, its measurability/integrability theorems,
`expectedEventualUtility`, and almost-sure termination retain their original
mathematical hypotheses. Classical instances used in these proofs are local
to Prop; no decision or encoding is added to the general model. In particular,
`stoppedUtility_eventuallyEq_eventualUtility` uses the same classical least
hit as `eventualUtility` inside its proof. General callers can still obtain
all prior stopped-utility conclusions with a proof-local classical decision.
No existence, normalization, legality, or realization result became an input.

`ObservedMeasurableKernelOutcomeBoundary` supplies its terminal test by
matching `Node`. Its `evaluation` specializes the existing stopped wrapper's
fields, reusing the original measurability and bound proofs; the result is
definitionally equal to `terminalPayoff.stoppedBoundedPathUtility 1`. This
avoids passing a closed noncomputable history-model constructor at runtime.
Its expected-zero, expected-one, and strict Nash counterexample proofs remain.
The analogous concrete prefix/field specializations in the reviewed examples
also retain their original types and equations. Their event-history and clock
regressions execute distinct actions at identical states.

The D review's 33 redundant markers, 17 concrete field/prefix operations, and
three stopped-utility operations are removed from the audit, together with
the now-executable outcome `evaluation` consumer. The exact E identity list
is recorded in the computability migration review. Returning a supplied
mathematical object or a proof-erased field is distinguished from constructing
an analytic law. No checked baseline is updated.
