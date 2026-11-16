# EFG Preservation Matrix

This note is the common vocabulary for claims made by EFG relations,
realizations, serializers, and compilers. Lean declarations remain
authoritative. A cell marked “premise” means the property is not part of the
relation itself: a transfer theorem must receive an explicit certificate.
The canonical pre-stability import for the formal relation-strength vocabulary
is `EconCSLib.GameTheory.ExtensiveGame.Interface.Preservation`.
The ownership and dependency direction of the structural, finite PMF,
infinite discrete, analytic-kernel, and FOSG regimes is fixed separately by
[`efg-semantic-universes.md`](efg-semantic-universes.md).

## Strength vocabulary

- **Hom**: forward structure map and commuting transition diagram; it need not
  be injective or surjective.
- **Iso**: bijective data and strict commuting diagrams. Endpoint-forgetting,
  macro-step compression, reordered simultaneous moves, and administrative
  stuttering are not strict isomorphisms.
- **InformationRefinement**: same strategic dynamics with a directional map
  from finer to coarser information. Strategy lifting and equilibrium transfer
  are directional.
- **Simulation / Bisimulation**: one-way / two-way step matching. Neither name
  alone asserts equality of probability laws.
- **WeakSimulation / WeakBisimulation**: visible steps may correspond to
  multiple administrative steps. These are the standard relations for
  stuttering and serialization.
- **Realization**: a strategy map whose induced semantic law is preserved
  against the stated opponent class. It is not a raw strategy-space
  isomorphism.
- **Coupling**: a joint law supported on a relation. Equality of pushforward
  laws follows only when the relation/function hypotheses say so.

## Measure vocabulary

These four levels are deliberately different:

1. an arbitrary `Measure` has no normalization or legality guarantee;
2. a probability measure additionally has an `IsProbabilityMeasure`
   certificate;
3. a lawful complete-path probability is a
   `ControlledObservedGame.CompletePathLawSemantics`, whose `pathLaw` is
   normalized and is almost surely supported on
   `Arena.IsCompletePlayPathFrom`; this is a family of per-root marginals, not
   by itself one common causal process;
4. an execution-coherent lawful probability additionally satisfies
   `RealizesExecution` or a caller-supplied `ExecutionCoherent` predicate.

The maximum path-law carrier is payoff-free and stores no local kernel, PMF,
countability assumption, strategic-mode tag, or chance-semantics tag.
Discrete PMF and analytic-kernel execution enter through downstream adapters.
Restart, conditioning, and cross-root coherence are extra certificates rather
than consequences of the per-root carrier.

Finite discrete history laws have a separate two-level contract:

1. `BoundedHistoryLawFamily` is raw history-valued PMF data. The dependent
   `History` carrier witnesses root reachability, but the structure does not
   claim normalization, terminal absorption, or agreement with an executor.
2. `CertifiedBehavioralExecutionLaw` records normalization, reachable
   legality, terminal absorption, and equality with the specified behavioral
   chance-kernel executor. The concrete `behavioralCertifiedExecutionLaw`
   constructs this level.

Likewise, `HistoryTransformLawEquivalentAt` is the honest name for an
arbitrary history transform. `TerminalHistoryLawEquivalentAt` is reserved for
transforms whose codomain is the existing terminal-history subtype.

## Relation-level matrix

| Relation/certificate | Histories/endpoints | Actions | Information | Chance | Complete path/history law | Objectives | Unilateral deviations | Recall | Roots/subgames | Termination |
|---|---|---|---|---|---|---|---|---|---|---|
| `ControlledObservedGame.Hom` | forward strict history map | dependent information-action map only; no concrete-realization square | private/public/info maps | not included | not included | not included | **not included**: a target may have information states with no source preimage | premise | `MapsRootPresentations` is an extra predicate | premise |
| `ControlledObservedGame.Iso` | bijective complete histories | dependent equivalences with concrete-realization square | private/public/info equivalences | not included | structural path equivalence only; stochastic/path-law equality needs a separate naturality premise | payoff-free objectives may be transported by their own theorem | pure-strategy equivalence and update square | classic/private/public recall iff | exact root and lawful-subgame transport theorems | structural certificates transport through the arena equivalence |
| `ObservedGame.PayoffCompatibleIso` | underlying strict payoff-free iso | inherited | inherited | separate | no law field | adds only the terminal-payoff commuting square | inherited only from the structural iso | inherited | inherited | inherited |
| `ControlledObservedGame.InformationRefinement` | shared strict controlled dynamics | exact concrete actions | directional fine-to-coarse information map | separate | requires a concrete strategy/law lifting theorem | not included | source pure strategies lift; reverse coverage is extra | not automatic | external | premise |
| `BoundedHistoryLawFamily` | dependent histories are rooted/reachable by construction | not certified against a policy | arbitrary strategy carrier | not certified | raw bounded PMF family only | not included | profile updates are merely inputs | not included | current history is explicit | not certified |
| `CertifiedBehavioralExecutionLaw` | rooted history support; `exists_suffix_of_mem_support` proves every endpoint is the supplied current history plus a legal typed suffix | exact through `behavioralHistoryLaw` | behavioral profile | specified normalized chance kernel | normalized, terminal-absorbing, and exactly executor-consistent | downstream only through explicit interpretation | behavioral profiles and chance execution are fixed by the equality field | not included | current history is explicit and support is an occurrence-sensitive continuation from it | absorption field; bounded fuel does not assert eventual termination |
| strict `Simulation` / `Bisimulation` | related endpoints per step | related actions/policies | presentation-specific premise | kernel relation required | only when an execution/coupling theorem is supplied | relation-respecting objective premise | deviation completeness is extra | not automatic | external | not automatic |
| `WeakSimulation` / `WeakBisimulation` | visible histories may skip/stutter | macro action versus micro trace | serialization invariant | kernel coupling | visible trajectory law through the stated projection | projection-respecting objective premise | explicit policy/deviation compilation | explicit theorem only | macro-root map, not strict root identity | requires progress/no-divergence certificate |
| same-game `CompleteHistoryLawRealization` | same occurrence-sensitive history carrier | semantic, through induced histories | arbitrary playerwise strategy carriers | supplied by the concrete semantics, not tagged in the relation | exact bounded complete-history PMF | downstream only through explicit interpretations | source deviations map via the playerwise map; target coverage and strategy isomorphism are separate | not included | not included | bounded fuel only |
| cross-game `CrossGameBoundedCompleteHistoryLawRealization` | explicit source-to-target history map | semantic | arbitrary playerwise strategy carriers | supplied by each concrete semantics | exact PMF pushforward at every profile/current history/fuel | downstream only through explicit interpretations | source update square proved; target coverage is not stored | not included | current history maps explicitly | bounded fuel only |
| same-game `CompletePathLawRealization` | identity history/path carrier | semantic | arbitrary playerwise strategy carriers | supplied by each lawful semantic model | exact whole lawful path-probability equality | measurable pushforwards follow | source update square proved; target coverage and strategy isomorphism are separate | not included | every current history, with no stored root selection | a.s. termination is a separate law property |
| cross-game `CrossGameCompletePathLawRealization` | explicit measurable history and coordinatewise path maps | semantic | arbitrary playerwise strategy carriers | supplied by each lawful semantic model | exact source-law pushforward to target law | measurable pushforwards follow | source update square proved; target coverage and cross-game strategy isomorphism are separate | not included | target current history is the image of the source history | a.s. termination transfer needs an event theorem |
| `PathLawCoupling` | paired path carriers related almost surely | encoded in support relation | not included | joint law supplied explicitly | source, target, and joint are certified probability measures; both marginals are exact | relation-respecting observer requires a theorem | not implied | not implied | not implied | not implied |
| `StrictCompilerPreservation` | strict payoff-free history iso | inherited from strict iso | inherited from strict iso | not included | **not included** | not included | not included | not included | exact chosen-root correspondence | only what the structural iso transports |
| `WeakCompilerPreservation` | weak source/target state relation with nonempty target progress | macro action versus micro trace | not included | not included | **not included** | not included | not included | not included | related initial states only | progress is stored; no-divergence/law preservation is extra |
| payoff-free `FiniteEFGHypotheses.toFiniteHistoryGame` / `toFiniteObservedGame` | `historyEquiv` and `toOriginalIso` preserve occurrence-sensitive complete histories; merged endpoints remain distinct | strict dependent equivalence | private/public/info pullback presentation | `pullDiscreteChanceKernel_eq` | `mapBehavioralHistoryLaw` proves exact bounded complete-history PMF pushforward from certified behavioral execution laws | terminal/path objectives pull back without endpoint quotienting | pure/behavioral strategy equivalences and update squares are proved | `perfectRecall_iff`, `eventClockSignalPerfectRecall_iff`, `eventClockPublicPerfectRecall_iff` | `toOriginalIso_preservesRootPresentation`; `pullSubgameSystem_isLawful` | `toFiniteHistoryGame_hasLengthBound` |

## Declaration anchors

The matrix rows above are backed by the following Lean owners:

- `Observed/Controlled/Morphism/Core.lean`: payoff-free `Hom`, strict `Iso`,
  `InformationRefinement`, root-presentation correspondence, structural
  strategy transport, and Iso algebra.
- `Observed/Controlled/Morphism/Subgame.lean` and
  `Observed/Controlled/Morphism/Recall.lean`: lawful-subgame transport and
  recall equivalences respectively. `Observed/Controlled/Morphism.lean` is the
  declaration-free canonical facade for all three leaves.
- `Observed/Controlled/Compat/Morphism.lean`: the orthogonal
  `ObservedGame.PayoffCompatibleIso` and legacy payoff-aware adapters.
- `Observed/Controlled/Law/Discrete.lean`: discrete chance presentation, raw
  `BoundedHistoryLawFamily`, certified behavioral execution laws, bounded
  semantic realizations, and strict stochastic naturality.
- `Observed/Controlled/Law.lean`: the normalized, almost-surely lawful common
  per-root path-marginal carrier; honest general history-transform and
  terminal-history laws; measurable history/outcome/payoff interpretations; distinct
  arbitrary-integral and expected-utility theorems; execution coherence;
  same-game and cross-game realizations; identity/strict-Iso bridges; target
  deviation coverage; and strategy-space isomorphisms.
- `Observed/Controlled/Law/DiscretePath.lean` and
  `Observed/Controlled/Law/Analytic.lean`: the actual discrete behavioral and
  analytic-kernel adapters into that common carrier.
- `Observed/FiniteUnfolding.lean`: compiler-specific occurrence-unfolding
  certificates, including `boundedHistoryLawPreservation`, a concrete
  cross-representation exact behavioral history-law package.
- `Relations/Preservation.lean`: formal aliases for strict/weak relations,
  same/cross-game law realizations and probability couplings, plus compiler
  packages whose constructors prevent a weak serializer from being labelled
  a strict isomorphism.
- `Interface/Preservation.lean`: the recommended facade for those distinct
  strengths. `Interface.Relations.Discrete` intentionally does not import the
  measure-valued preservation module.

## Compiler coverage ledger

This is the per-compiler review queue. A `proved` cell names a theorem family
owned by the route. `via` means a generic theorem can be instantiated from the
listed compiler certificate. `premise` is deliberately not a preservation
claim. Missing cells are gaps only when a downstream client needs that axis.

| Frontend/route | Representation strength | Information / recall | Chance and execution law | Roots / lawful subgames | Deviations / equilibrium | Termination | Remaining boundary |
|---|---|---|---|---|---|---|---|
| `GameTreeOccurrenceObserved` | occurrence-sensitive history construction; endpoint forgetting is a separate information refinement | `toOccurrenceObservedGame_perfectInformation` and `toOccurrenceObservedGame_perfectRecall` proved | deterministic terminal outcome and payoff realization proved | canonical `occurrenceCompleteSubgameSystem` | backward-induction profile and `Kuhn_exists_occurrencePureSPE` proved; endpoint behavioral/pure reflection is directional | pure termination on every continuation proved | no chance or analytic execution claim |
| legacy `GameTreeObserved` | endpoint compiler and root game-form isomorphism; **not** a strict occurrence-history isomorphism | endpoint information may merge distinct occurrences | deterministic terminal continuation outcome proved | all-continuations presentation only; not a canonical lawful-root certificate | root Nash and legacy endpoint-policy continuation equivalence proved; explicitly not standard EFG SPE | finite tree execution proved terminating | compatibility route; do not grow parallel standard-SPE theory |
| `StochasticGameTreeObserved` | occurrence-sensitive complete-history observation | full-history information by construction; no separate generic recall package | local chance PMF, bounded endpoint law, and payoff-law equalities proved | root selection and lawful-subgame coverage remain external | `policyToBehavioralProfile_deviate` proved; no compiler-level Nash/SPE theorem | bounded fuel only at the public bridge | total continuation equilibrium and lawful-root coverage |
| `FiniteImperfectObserved` | structural compiler from compact finite states and declared information labels | action coherence is a compiler premise; generic recall is not claimed (`tinyObserved_perfectRecall` is only a regression instance) | optional normalized chance compiler; no global execution-law package | `initialRoot` is a presentation choice; other roots require external lawfulness | strategy carrier is information-indexed; equilibrium transfer not supplied | premise | add only model-specific certificates actually derivable from the compact source |
| `FiniteEFGHypotheses` finite unfolding | strict occurrence-history `toOriginalIso` | classic and event-clock private/public recall iff proved | chance-kernel equality and exact bounded complete-history PMF pushforward proved | root presentation, selected systems, and complete systems transport | update squares proved; concrete Iso equilibrium transfer is available via the corresponding pure/behavioral theorem | uniform history-length bound proved | no expressive change; this is a finite re-presentation |
| FOSG sequentialization | progressing weak serialization from one simultaneous macro-step to an ordered micro-trace | history-augmented target information and observation hiding are constructed; recall is not claimed generically | one-block laws, finite-horizon state/trace couplings, and payoff/utility-law equalities proved | explicit source macro roots and external target-root presentation; not all lawful target micro roots | behavioral deviation square and two-way finite-horizon macro-root Nash proved | finite macro horizon only | complete lawful-root coverage, total continuation execution, target local-deviation coverage, and standard SPE remain open |
| measurable presentation bridges | semantic embedding/presentation, not one strict EFG compiler | supplied measurable information presentation | exact supplied kernel/path-law transport | premise | only the strategy/deviation packages explicitly constructed by each bridge | finite-horizon or a.s.-termination premise | PMF strategies are not identified with arbitrary non-atomic kernels |

Every new compiler-facing theorem should update exactly one row. A new
`proved` claim must cite a Lean declaration; prose, a root predicate, or a
weak simulation alone cannot upgrade another axis.

## Equilibrium and recall contract

`ContinuationSemantics.isEvaluatorContinuationEquilibriumAt_iff_of_surjective`
is an abstract evaluator-relative game-form transfer. It is not a
standard-EFG-SPE theorem. Operational standard-SPE preservation remains on
concrete pure, behavioral, or path-law execution layers. A future common
theorem must use canonical root-local strategy restriction, local-deviation
extension, and complete-play/path-law execution; caller-defined execution and
legality types are not preservation evidence.

Signal/public recall preservation rows refer to event-clock traces, in which
every arena transition emits one signal. `SignalTraceBuilder` supports
external asynchronous traces with `Option Signal` and silent events. Only the
always-emitting builder is proved to recover the event-clock trace; no
equivalence with arbitrary silent-event recall is asserted.

## Review rule

A compiler or transfer theorem should cite the strongest row it actually
constructs. Stronger downstream consequences must be derived through a named
bridge—history/path law to outcome law, outcome law to payoff law, or payoff
law to utility—not asserted by prose. Root visibility, lawful subgames,
deviation coverage, recall, and termination are independent axes unless the
declaration explicitly includes them.

These checks provide machine-checked evidence for source elaboration, the
axiom surface, placeholder policy, module boundaries, and the listed formal
semantic properties. They are not a metamathematically complete certification
of every intended model meaning.
