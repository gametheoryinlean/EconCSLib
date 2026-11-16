# EFG Simulation Framework: Formalization Status

Date: 2026-08-02

## Objective

The extensive-form-game layer is organized around an abstract,
simulation-oriented interface rather than one privileged concrete game-tree
encoding. The intended workflow is:

1. model a game in the representation natural to the application;
2. connect representations by the strongest mathematically valid morphism;
3. prove structural or equilibrium results once at an abstract semantic layer;
4. transfer those results through strict isomorphisms, refinements, or
   weak/stuttering simulations.

## Representation hierarchy

| Relation | What it preserves | Intended use |
|---|---|---|
| `ObservedGame.Iso` | Complete histories and actions bijectively; private observations, public states, decision information, terminal payoffs, and presentation-designated roots exactly; arbitrary nonterminal payoff fillers are ignored | Pure structural relabeling, exact two-way designated-root Nash transfer, and transport of certified lawful subgame systems |
| `ObservedChanceGame.Iso` | All strict observed structure plus exact chance-kernel pushforward | Exact behavioral and mixed law transfer |
| Information refinement | Complete dynamics with a directional forgetting/lifting map for information | Comparing fine and coarse information models |
| Arena/kernel simulation and bisimulation | Step matching, optionally through couplings | Non-functional representation comparison |
| Weak/stuttering simulation | One macro step against a positive finite micro execution | FOSG serialization and administrative states |

Strict isomorphism is used whenever the history trees really are bijective.
FOSG sequentialization is not called an isomorphism: one simultaneous macro
step becomes several player and chance micro steps, so the two history arenas
cannot be in one-step bijection. Exactness is retained at macro boundaries by
PMF couplings and weak/stuttering simulation; this is not an approximation.

`ObservedGame.Iso` compares games after fixing one player carrier. Bijective
changes of player labels are normalized first by
`ControlledObservedGame.relabelPlayers` (or its payoff-aware `ObservedGame`
adapter), which also transports dependent pure profiles and complete lawful
subgame systems. Non-bijective player changes remain compiler-specific.

## Implemented semantic transfer

The current modules provide:

- granular `Interface/{Core,Execution,Relations,Equilibrium,Restart,Compilation}`
  facades as dependency-ordered public tiers; pre-release broad aggregates
  were deleted after consumer migration;
- an explicit public API and deprecation policy in
  `docs/design/efg-public-api.md`;
- strict observed-EFG isomorphisms preserving observations, public state,
  decision information, presentation-designated continuation roots, payoffs,
  pure strategies, behavioral strategies, mixed plans, and normalized chance
  kernels; they also transport explicit lawful subgame systems;
- exact bounded pure, behavioral, and mixed history/payoff laws;
- exact bounded Nash transfer on presentation-designated continuations through
  strict isomorphisms, with separate subgame-perfection-on and complete
  standard-SPE predicates;
- directional pure and behavioral transfer through information refinements,
  with two-way results under explicit strategy or semantic-deviation coverage;
- representation-neutral `GameForm`, `LawGameForm`, and
  `ContinuationGameForm` morphisms, isomorphisms, and relational simulations;
- `IndexedContinuationGameForm`, whose horizon and outcome types are arbitrary,
  so total, distinguished-index, or measure-valued evaluators reuse the same equilibrium
  transfer layer rather than introducing a new EFG core;
- `ControlledObservedGame.ContinuationSemantics`, which attaches such an
  evaluator to payoff-free complete-history roots and lawful-subgame systems
  without rebuilding either structure; the `ObservedGame` spelling is a
  compatibility abbreviation that does not inspect state payoffs;
- one `BoundedDesignatedNashBridge` consumer interface with pure, behavioral, mixed, and
  finite-Kuhn constructors;
- coupling-based kernel simulations, finite-trajectory transfer, and
  weak/stuttering serialization;
- `MeasurableKernelArena`, whose normalized Mathlib Markov kernel is defined
  on the measurable dependent state/action bundle, together with an exact
  embedding of every discrete `KernelArena` and its strict morphisms;
- terminal-aware measurable action policies, with zero action mass at leaves,
  almost-sure legality, and a formally normalized absorbing state-step kernel;
- `NonmeasurableFiberLegalityBoundary`, which proves that the former
  outer-measure-one condition accepts an actually illegal policy on a
  nonmeasurable action fiber, while the almost-everywhere legality field
  rejects it; the numerical measure-one API is now only a local consequence
  under singleton measurability;
- exact recovery of every existing discrete policy step after `PMF.toMeasure`,
  using a reusable PMF-bind/measure-bind theorem that does not assume a
  countable carrier;
- normalized finite-horizon analytic endpoint kernels, their
  Chapman--Kolmogorov equations, terminal absorption at every horizon, and
  exact recovery of `KernelArena.stateLawFrom`;
- an Ionescu--Tulcea probability measure on infinite analytic state paths,
  exact equality of every coordinate marginal with the corresponding finite
  endpoint measure, exact discrete PMF-coordinate recovery, and almost-sure
  constant paths from terminal states;
- time- and finite-state-prefix-dependent measurable action policies, their
  normalized Ionescu--Tulcea state-path executor, and an exact whole-path
  embedding of every stationary state-Markov action policy;
- joint state/action event paths and fixed measurable information statistics,
  with exact state-path projection and exact fine-to-coarse policy pullback;
- a complete-history analytic lift for observed chance games, exact player and
  chance branches, and exact recovery of every finite behavioral/chance
  stopped-history PMF measure;
- non-atomic unit-interval regressions proving that neither the analytic
  transition law, its policy-controlled execution step, nor any positive
  finite endpoint law is `PMF.toMeasure` for a discrete probability mass
  function; the full analytic path law is likewise not PMF-representable;
- an exact finite-player FOSG sequentializer and behavioral Nash bridge on
  caller-declared macro continuations;
  its bounded outcome is an optional terminal payoff, so finite-horizon
  exhaustion at a nonterminal state is `none` rather than a filler payoff;
- endpoint-sensitive and occurrence-sensitive `GameTree` compilers, connected
  by refinement rather than a generally false strict isomorphism;
- a root-bound occurrence-sensitive backward-induction profile and
  `Kuhn_exists_occurrencePureSPE`, proved against the complete
  history-contingent deviation space and the all-history lawful subgame
  system; the structural endpoint layer now uses explicit
  `GlobalEndpoint...` names, with deprecated compatibility aliases;
- `OccurrenceNonIso`, which constructs a path-sensitive strategy separating
  two equal-subtree occurrences and proves every lifted endpoint policy must
  choose the same child at both;
- `DesignatedContinuationSPEBoundary`, which exhibits an initial-root Nash
  profile with a profitable off-path continuation deviation and proves that no
  lawful all-relevant-history `SubgameSystem` can certify the root-only
  presentation as standard SPE;
- finite imperfect-information compilation into the observed-EFG interface;
- perfect recall, no-absent-mindedness, and compiler-facing recall
  certificates;
- an Ionescu--Tulcea probability law on infinite terminal-absorbing history
  paths, exact equality of every coordinate marginal with the bounded PMF
  executor, first-terminal stopping times, a.s.-termination payoff
  convergence, vanishing unfinished mass, and weak convergence of real payoff
  laws;
- a uniform-deviation convergence theorem for finite-to-infinite SPE and a
  horizon-dependent counterexample showing that the convergence hypothesis
  cannot be dropped.

## Constructive finite Kuhn realization

The reusable PMF layer is split into
[`FiniteProduct.lean`](../../EconCSLib/Math/Probability/PMF/FiniteProduct.lean),
[`Coupling.lean`](../../EconCSLib/Math/Probability/PMF/Coupling.lean), and
[`Equiv.lean`](../../EconCSLib/Math/Probability/PMF/Equiv.lean).
It characterizes point masses of finite dependent PMF products, proves
arbitrary-coordinate splitting and finite reindexing invariance, and hosts
representation-neutral relational coupling tools. `KernelArena.lean` now
contains only the stochastic transition structure and its morphisms.

[`DeferredSampling.lean`](../../EconCSLib/Math/Probability/PMF/DeferredSampling.lean)
defines a typed fresh-query tree with:

- terminal result nodes;
- arbitrary chance draws;
- adaptive one-use queries into a finite dependent independent-law family.

The theorem `PMF.FreshQueryTree.runPresampled_eq_runOnDemand` proves exact
equality of result PMFs between sampling the complete table before execution
and sampling each coordinate on first use.

`FiniteInformationHypotheses` is the minimal construction layer: finite
decision-information types alone suffice for
`behavioralToMixedStrategy`, `behavioralToMixedProfile`, and their abstract and
concrete local action marginals. It requires neither player decidable equality,
no-absent-mindedness, nor perfect recall.

[`DeferredSampling/Realization.lean`](../../EconCSLib/GameTheory/ExtensiveGame/Observed/DeferredSampling/Realization.lean)
compiles bounded observed chance-EFG execution to this tree. Its
`FutureDecisionKeysAvailable` invariant is future-closed: chance steps retain
the available set, while player steps erase the current player/information
key. No-absent-mindedness proves that an erased key cannot recur.

Adding no-absent-mindedness gives
`FiniteNoAbsentMindednessHypotheses`, under which the execution-level
behavioral-to-mixed direction provides:

- `behavioralToMixed_stoppedHistoryLawFrom_of_noAbsentMindedness`: independent complete pure-plan
  sampling and local behavioral sampling have identical bounded complete
  history laws from every continuation root;
- `behavioralToMixed_stoppedPayoffLawFrom_of_noAbsentMindedness`: the corresponding optional payoff
  laws are identical;
- `behavioralToMixedContinuationHom_of_noAbsentMindedness`: these equalities form one global
  continuation-family morphism;
- `isBehavioralNashOnDesignatedContinuationsAtFuel_of_behavioralToMixed_of_noAbsentMindedness`:
  bounded mixed Nash of the constructed plan profile on every
  presentation-designated continuation reflects to the corresponding
  behavioral property.

The established `FiniteKuhnHypotheses` names remain compatibility wrappers.
Perfect recall is retained for the mixed-to-behavioral construction and for:

- `isBehavioralNashOnDesignatedContinuationsAtFuel_iff_mixed_of_deviationComplete`: two-way
  bounded designated-continuation Nash follows from the exact additional
  premise of rootwise semantic deviation completeness.

[`ConditionalSampling.lean`](../../EconCSLib/Math/Probability/PMF/ConditionalSampling.lean)
defines total discrete conditioning on a fiber, with an explicit impossible
event fallback, and proves exact disintegration.
[`ConditionalProduct.lean`](../../EconCSLib/Math/Probability/PMF/ConditionalProduct.lean)
proves that conditioning a finite independent dependent product on one
coordinate updates exactly that coordinate.

[`KuhnConditioning/Realization.lean`](../../EconCSLib/GameTheory/ExtensiveGame/Observed/KuhnConditioning/Realization.lean)
combines those probability results with perfect recall. For each continuation
root it conditions an arbitrary mixed contingent plan on the player's own
post-root information/action records. The following are formal:

- `mixedToBehavioral_stoppedHistoryLawFrom` and
  `mixedToBehavioral_stoppedPayoffLawFrom`: exact bounded complete-history and
  optional-payoff laws from the selected root;
- `finiteKuhnMixedBehavioralRealizationAt`: a root-scoped realization
  certificate with exact unilateral behavioral-deviation coverage;
- `finiteKuhn_isNash_iff`: two-way Nash transfer at any selected root;
- `behavioralToMixedContinuationHom_outcomeDeviationCompleteAt`: every
  arbitrary mixed unilateral deviation from an independently sampled
  behavioral profile is realized exactly by a root-scoped behavioral
  deviation;
- `isBehavioralNashOnDesignatedContinuationsAtFuel_iff_mixed`: the full
  two-way bounded designated-continuation Nash equivalence between a
  behavioral profile and its independently sampled complete pure-plan
  profile.

## Exact boundary

Both finite Kuhn directions are now constructive and exact at the level of
bounded history and payoff laws. The mixed-to-behavioral map is intentionally
indexed by the continuation root. It does not assert that every arbitrary
mixed contingent plan has one root-independent behavioralization preserving
all off-path continuations: ex-ante correlations inside a mixed plan make
that claim false in general.

Full bounded designated-continuation Nash transfer does not require that false
global map. Instead, the proof establishes semantic deviation coverage
separately at every presentation-designated root for the one global
behavioral-to-mixed continuation morphism.
A stronger continuation-wide mixed-to-behavioral certificate remains an
explicit hypothesis when genuinely available.

The finite regression examples guard four common overstatements:

- occurrence-sensitive and endpoint-sensitive compilers need not be strictly
  isomorphic;
- root-scoped mixed-to-behavioral realization need not extend to one
  root-independent behavioral profile;
- no-absent-mindedness is necessary for erasing a consumed future decision
  key;
- an exact relational coupling is weaker than strict chance-law pushforward,
  including at the `ObservedChanceGame.Iso.map_chanceKernel` integration layer.

The analytic kernel arena now has a terminal-aware measurable policy,
normalized one-step execution, finite endpoint iteration, and a joint
Ionescu--Tulcea state/action event-path probability law. Its complete-history
bridge executes existing observed behavioral and chance policies and recovers
their finite stopped-history laws exactly. The later abstract-action
realization and observed measurable-kernel presentation layers resolve the
concrete action-bundle information-fiber boundary: they support fixed
profile-independent realization, non-atomic player and chance kernels,
constructive profile/deviation assembly, bounded and almost-sure terminal
payoff evaluation, absolute continuation, explicitly qualified fresh
restart, and deviation-complete designated-continuation Nash,
subgame-perfection-on, and complete standard-SPE transfer. Continuous time remains
outside this layer. The continuous-state endpoint and path regressions prove
strict expressive gain over `PMF`; they do not claim holding-time,
non-explosion, or càdlàg path semantics.

## Pull-request review map

Review the current implementation in dependency order:

1. `Math/Probability/PMF/`: equivalence pushforwards, finite dependent
   products, couplings, conditioning, and deferred sampling. These modules
   must remain independent of EFG domain structures.
2. `Execution/`, `Simulation/`, `Observed/Game.lean`, and the granular
   `Observed/{Morphism,Refinement,BehaviorRefinement}/` leaves: bounded
   execution semantics and the exact distinctions between isomorphism,
   directional refinement, coupling simulation, and weak/stuttering
   simulation.
3. `Observed/{PerfectRecall,Kuhn}.lean`,
   `Observed/{DeferredSampling,KuhnConditioning}/`, and
   `FOSG/Sequentialization/`: the two constructive finite Kuhn directions and
   the exact FOSG micro/macro law. Their implementation is split into
   dependency-ordered concept modules together with
   `GameForm/Continuation/`.
4. `Compiler/` and `Examples/ExtensiveGame/`: concrete representation bridges,
   the N-1 through N-4 guardrail regressions, and the non-atomic analytic-kernel
   boundary.
5. Granular `Interface/{Core,Execution,Relations,Equilibrium,Restart,Compilation}`
   facades and these design documents: minimal build surfaces, lifecycle, and
   reviewer handoff.

The removed PascalCase aggregates have no redirect stubs. Large proof chains
are now split at existing semantic boundaries: continuation
core/simulation/isomorphism, dependent-fiber/observed-morphism structure/inverse/
operational/continuation, refinement structure/bounded/termination,
behavior-refinement structure/execution, deferred-sampling
core/execution/realization, conditioning posterior/core/execution/realization,
and FOSG core/policy/macro-law/trajectory/witness/equilibrium. The largest
restart leaf is currently `Restart/Certificates.lean` at 1,168 lines;
the other restart leaves are at most 818 lines. The compatibility aggregate
and the short EFG-local `Probability/` redirects were deleted; reusable
probability implementations live only under `Math/Probability/PMF/`.

Bounded designated-continuation Nash entry-point consolidation is complete: the shortest relation-local
strict-Iso theorems remain canonical direct entries, while
`ObservedStrategyBridge` packages pure, behavioral, mixed, and Kuhn transfer
through one `BoundedDesignatedNashBridge` interface. The two `via...` families remain
documented route regressions. The relation normalization follow-up is complete:
`GameForm`, continuation, strict Arena morphisms/isomorphisms, observed
isomorphism, information refinement, and chance-aware relations expose the
applicable `@[ext]`, identity, associativity, and mapping normal forms.
Dependent information-action transport is centralized in `Equiv.fiberEquivAt` /
`Equiv.fiberEquivOverAt` and relation-local `infoActionEquivAt` APIs shared by
pure and behavioral semantics.

The original stochastic executor remains discrete and fuel-bounded.
`Execution/InfiniteTrajectory.lean` now extends it, without changing it, to a
genuine discrete event-time infinite path probability measure and proves exact
finite-coordinate compatibility. `Examples/ExtensiveGame/ReusableSemantics.lean`
has been explicitly downgraded to a distinguished-`⊤`, measure-valued
interface smoke test: it is not a limit or convergence theorem.

The separate analytic-kernel path layer in
`Simulation/Kernel/StatePath.lean` applies the same
Ionescu--Tulcea principle to `MeasurableKernelArena.ActionPolicy`. Its
coordinate laws are exactly the audited analytic endpoint measures, including
exact recovery of the discrete stopped state PMFs after embedding.
`Simulation/Kernel/HistoryPath.lean` then removes the stationary
policy restriction by allowing the action kernel to inspect the complete
finite state prefix. The original path measure is recovered exactly through
the stationary embedding.
`Simulation/Kernel/EventPath.lean` next retains selected action
occurrences in a joint event path and allows policies to inspect complete
finite event prefixes. State-history policies embed by forgetting those
occurrences; finite-prefix naturality and projective-limit uniqueness prove
exact recovery of the entire state-path pushforward.
`Simulation/Kernel/ObservedEvent.lean` then fixes measurable
information statistics on event prefixes. Information-indexed action kernels
compile by comap, equal information gives equal action laws, and pulling
coarse policies back along measurable information factors leaves the raw
event executor and full event-path law unchanged. Full event, state-prefix,
and latest-state information recover the preceding interfaces. The new
`latestEventState_eq_of_informationAt_eq` theorem also records the concrete
bundle boundary: one information value cannot serve distinct nonterminal
latest-state fibers.

`Simulation/Presentation/Chance/KernelBridge.lean` adds the complete-history
player/mover-aware execution bridge. It makes complete histories the states of
a deterministic `KernelArena`, reuses the existing behavioral/chance history
policy stationarily, proves exact player and chance one-step laws, and proves
that every finite analytic endpoint is `PMF.toMeasure` of the old stopped
history law. The absent-minded regression confirms both that one abstract
behavioral law is reused across two distinct player histories and that the
current concrete-bundle information policy cannot identify those analytic
states. Completing the analytic `InfoState` bridge therefore requires
abstract information actions with history-dependent concrete realization.

`Simulation/Kernel/RealizedInformation.lean` supplies that generic
realization layer. It keeps the information structure and action
interpretation fixed, lets policies choose only measurable abstract laws,
compiles them by measure bind into normalized legal concrete event policies,
and preserves stopped steps and the whole event-path law under information
pullback. Its information theorem equates abstract laws only; concrete laws
need an explicit almost-everywhere realization-agreement premise. The
terminal-tagged absent-minded regression is a strict positive separation: the
new policy exists, its one shared abstract Dirac law realizes to two unequal
legal concrete Dirac laws, and the old direct concrete-bundle policy on the
same information structure does not exist.

`Simulation/Presentation/Chance/Realized.lean` now defines the explicit
certificate boundary connecting that layer to original observed-game player
information. It fixes information and realization outside the profile,
factors player-controlled histories through the original `InfoState`, and
requires exact equality with the established raw observed-chance executor.
The resulting theorems preserve abstract player-information consistency,
exact player/chance bundle branches, the complete joint event path, the
complete state path, and every finite stopped-history measure. The
absent-minded regression constructs the certificate for all profiles and all
event prefixes, so the interface is not vacuous.

`Simulation/Presentation/Chance/Countable.lean` now makes the
observed-chance integration automatic for the countable-discrete fragment. It
uses terminal/player/chance information tags and a dependent tagged action
sigma type, derives countability of all finite event-prefix and bundle
carriers from countability only of complete histories and their total legal
action bundle, and installs top measurable spaces only where discreteness is
intended. Player tags retain a proof-carrying reachable-information subtype;
its countability follows from player-controlled histories, while a witnessing
`actionEquiv` embeds its action fiber into the countable history-action
carrier. The ambient player identifier type and unreachable declared
information/action fibers need not be countable. The fixed realization uses
`actionEquiv` at a matching player tag, the identical local action at a
matching chance tag, and a classically selected legal fallback only for
mismatched zero-mass tags. The reusable PMF-to-measure bind theorem proves
exact player and chance branches, so the resulting
`AnalyticPresentation.compiled` field is a theorem, not user-supplied
evidence. The absent-minded regression supplies a finite complete-history
cover and receives the presentation automatically. A strict second
regression uses the uncountable player type `Unit ⊕ ℝ`; every unused
real-indexed player has uncountable `ℝ` information and action fibers, and the
reachable-only presentation still obtains exact compilation.

The discrete-policy-to-analytic-policy embedding and
`AnalyticPresentation` certificate no longer expose a terminal-decidability
typeclass. Their terminal splits are classical inside noncomputable measure
kernels. Exact one-step, joint-path, and state-path presentation theorems
therefore need no terminal classifier. The finite theorem comparing those
paths with `stochasticHistoryPMFFrom` still retains the old executable bounded
evaluator's terminal-decidability premise.

`Simulation.Presentation.Chance.MeasurableHistory` and
`Simulation.Presentation.Chance.Measurable` now implement the explicit measurable
extension rather than weakening those countability premises unsoundly.
Measurable spaces on complete histories and dependent legal bundles,
projection, append, terminality, singletons, information, realization, and
profile kernels are all visible certificate data. Exact local player/chance
bundle equations replace a monolithic global equality and yield complete
joint/state path semantics through the existing executor. The old
`AnalyticPresentation` converts exactly, so the countable constructor is a
strict specialization.

The new regression has a real root action and one distinct terminal complete
history for each real. It proves both reachable histories and legal bundles
non-countable, gives explicit measurable equivalences to `Unit ⊕ ℝ` and
Borel `ℝ`, constructs the presentation for every behavioral PMF, and proves
the player kernel exactly.

`Simulation.Presentation.Kernel.Core` now separates that structural
`ObservedGame` from stochastic laws. The fixed chance law is a concrete
measurable action-bundle kernel; a `KernelBehavioralProfile` supplies
measurable abstract kernels indexed by the common information statistic and
must recover that chance law after realization. Equal player information and
unilateral-deviation agreement are stated at the abstract-kernel level. Every
old PMF presentation and the canonical countable constructor embed without
changing their compiled event policy.

The strict `ObservedNonAtomicKernelBoundary` regression uses unit-interval
volume. It proves exact compiled laws at a player-controlled root and at a
separate genuinely chance-controlled root, proves singleton mass zero, and
proves neither concrete law is the measure of any PMF. Integration remains
certificate-driven: `ObservedGame` itself carries no measurable structures,
and arbitrary functions on uncountable information spaces need not be
measurable.

Continuous time remains outside the implemented layer. In particular, no
holding-time kernel, non-explosion theorem, or càdlàg/Skorokhod path-space
weak-convergence result is claimed.

## Verification

The implementation is checked with:

```text
lake build
lake build EconCSLib.Examples
python3 scripts/check_lean_placeholders.py EconCSLib
git diff --check
```

At this status point the seven public interface targets completed with 2,770
jobs, the stable root library completed with 8,652 jobs, and the examples
completed with 8,752 jobs, including the permanent root/equilibrium/compiler
negative import boundaries. The placeholder, knowledge-blueprint, reference,
and whitespace checks passed. Import-surface regressions resolve the
ext/category/transport declarations, all four strategy-bridge constructors,
the three indexed strict-isomorphism adapters, and generic indexed
Nash-on-roots transfer. Representative legality, complete-system finite Kuhn
standard-SPE, strict-transport, fresh-restart, behavioral/mixed,
limit-Nash-on-declared-roots, and failure-boundary declarations use only the
standard logical quotients/choice axioms reported in the strict audit; none
uses `sorryAx` or a custom mathematical axiom.
