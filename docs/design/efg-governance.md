# EFG Architecture Governance

This document and `scripts/check_efg_governance.py` are the authoritative
enforceable architecture and placement policy for EconCSLib's extensive-form
games. Mathematical declarations and proofs remain authoritative in Lean,
module lifecycle lives in
[`efg-module-status.md`](efg-module-status.md), public navigation lives in
[`efg-public-api.md`](efg-public-api.md), and freeze readiness lives in
[`efg-minimal-core-freeze.md`](efg-minimal-core-freeze.md). The complete
authority order is
[`efg-document-authority.md`](efg-document-authority.md).

## Verdict and canonical semantic line

The current architecture is logically sound.  Its canonical semantic line is:

```text
 Foundation / Math.Probability.FiniteLaw
               │
               ▼
 Arena + Reachability + typed History       representation-neutral GameForm
               │                              │
              ▼                              │
           CompletePlay                       │
               │                              │
               └──────────────┬───────────────┘
                              ▼
   ControlledGame / ControlledDecisionGame / ControlledObservedGame
                              │
                 ┌────────────┼──────────────┐
                 ▼            ▼              ▼
          Objective/Winning  structural   lawful path
                             relations    probability
                                            │
                                 ┌──────────┴──────────┐
                                 ▼                     ▼
                         discrete PMF adapter   analytic adapter
                                 └──────────┬──────────┘
                                            ▼
                         payoff/equilibrium compatibility
                              ▼
                          ┌────┴─────┐
                          ▼          ▼
                       Restart   Compilation
```

This is a logical ownership diagram, not a claim that every source file forms
one literal import chain.  In particular:

- `Arena`, reachability, typed histories, measure-free complete plays, and
  payoff-free observed control form the exact five-module StructuralCore.
- structural termination, finite/subgame/recall certificates, and bounded
  deterministic/PMF execution are the broader `Interface.Core` Foundation
  Facade.
- history-sensitive terminal and path outcomes are exposed by the opt-in
  `Interface.Objective` facade without probability or equilibrium.
- `ControlledDecisionGame` is the minimal payoff-free carrier of controlled
  dynamics and decision information. `ControlledObservedGame` adds optional
  private/public observations. `ObservedGame` and `ObservedChanceGame` are
  payoff-aware/discrete compatibility extensions, not dependencies of the
  payoff-free spine.
- finite PMF execution, infinite discrete path execution, and non-atomic
  analytic execution are distinct layers.
- Restart extends analytic equilibrium.  Discrete Compilation extends discrete
  equilibrium.  They are sibling public branches and neither imports the other.

Specialized representations remain inputs or algorithm languages:

```text
GameTree ───────────────────────────────┐
StochasticGameTree ────────────────────┤
FiniteImperfectGame ───────────────────┼─ compiler / proved realization
FOSG ──────────────────────────────────┤                │
ZeroSumChance.GameTree ─ specialized ──┘                ▼
                                            ObservedGame /
                                            ObservedChanceGame /
                                            GameForm
```

`GameTree` endpoint projection and occurrence projection are both useful, but
the endpoint map is not injective when equal subtree values recur.  It is an
information-forgetting relation, not an isomorphism.  `ZeroSumChance.GameTree`
retains independent value as an exact `ℚ` algorithm; the presence of
`ObservedChanceGame` is not a reason to remove it.

### Recorded physical-layout deviations

The source does not perfectly mirror the diagram:

1. `Simulation/` contains analytic execution, presentation assembly, outcomes,
   continuation, and restart implementation. Its Internal leaves are grouped
   below `Kernel/`, `Presentation/`, `Equilibrium/`, `Continuation/`, and
   `Restart/`; discrete execution and relations live separately under
   `Execution/Discrete` and `Relations/Discrete`.
2. `Strategy` is a valid state-indexed Arena policy, but is not equivalent to
   information-indexed `ObservedGame.PureStrategy`.
3. `Subgame.subgameAt` changes a state root; a presentation-designated
   continuation and a lawful `ObservedGame.SubgameSystem` make strictly
   different claims. The representation-neutral `Arena.Reachable` relation and
   initial-state specialization now live separately in canonical
   `Structural.Reachability`, so typed histories do not import `Subgame`.
4. The endpoint `GameTree` NE/SPE/strategic-form route remains available by
   explicit import but left the root closure on 2026-07-30; occurrence-sensitive
   observed strategies are canonical for standard EFG SPE.
5. Several implementation modules exceed 800 lines.  Their audit below shows
   that most large proof chains are highly coupled and are not made safer by a
   mechanical split.
6. `Observed.Controlled.Infrastructure` is a declaration-free canonical
   aggregate facade. Its declarations are physically owned by `Core`,
   `WellFormed`, `Subgame`, `Finite`, `Quasi`, and `Recall` leaves;
   winning-dependent quasistrategy predicates live in `Winning.Basic`.
   `Recall` has an exact six-module closure and reaches neither `Finite` nor
   `Execution.Length`.
7. `Observed.Controlled.Morphism` is likewise a declaration-free canonical
   facade. Structural transport is owned by `Controlled.Morphism.Core`,
   lawful-subgame transport by `.Subgame`, and recall transport by `.Recall`;
   their exact EFG/local closures are 9 / 9, 11 / 11, and 12 / 12.
8. The complete `Observed.Controlled` hierarchy has the fixed role taxonomy
   documented in [`efg-controlled-api.md`](efg-controlled-api.md): one carrier,
   five semantic owners, ten responsibility owners, two declaration-free
   facades, and three downstream payoff-aware adapters under `.Compat`.
   Canonical modules cannot reach an adapter, and a new flat sibling such as
   `Observed.ControlledFoo` is rejected.
9. FOSG sequentialization keeps its observed chance-game value independent of
   continuation-root selection. `observedChanceGameCore` is root-free,
   `rootPresentation` owns the source-root predicate, and the established
   root-parameterized `observedChanceGame` name is a definitionally equal
   compatibility wrapper.

These deviations are governed below. The `Observed.Controlled` hierarchy was
hard-migrated during the current EFG pre-stability phase; no forwarding stubs
remain at its former flat paths. No EFG facade currently carries an external
source-compatibility guarantee.

## Lifecycle classes

### Canonical

Canonical modules own reusable semantics. General Nash, SPE, continuation,
and representation-transfer theory should be stated here unless its statement
genuinely mentions a frontend-specific object. Canonical declarations may be
implemented in non-facade leaves, but consumers import the granular facade.

Canonical means recommended and machine-governed during pre-stability; it
does not mean externally source-compatible. An evidence-backed hard migration
is allowed now and requires, in the same change:

1. a mathematically equivalent, explicitly narrower, or honestly documented
   non-equivalent replacement when one exists;
2. migration notes and synchronized internal consumers;
3. a positive import regression for every promised replacement;
4. a negative boundary regression when dependency closure changes; and
5. updated lifecycle, governance, and audit records.

The repository-wide Canonical/Frontend API growth freeze overrides the normal
pre-stability permission to add endpoints. Existing declarations and paths may
still be corrected or hard-migrated under the rules above, but the checked
surface does not grow. New research remains in the knowledge blueprint or an
opt-in Experimental module and is not promoted while the freeze is active.

The recorded 2026-09-04 A19 architecture decision is one narrowly scoped
module-path exception. It adds the declaration-free Canonical aggregates
`EconCSLib.Math.Probability.Effective` and
`EconCSLib.Math.Probability.Effective.Analytic`, allowing executable clients
to avoid analytic imports while giving theorem clients one opt-in route. No
public declaration is added by either aggregate, and the 1,689-declaration
ceiling is unchanged. This exception does not authorize another endpoint.

No migration window, deprecation interval, or major-release-only removal rule
is currently promised. Those policies begin only if EFG API stability is
formally announced later.

### Frontend

A frontend may own:

- syntax, validation, structural recursion, and executable algorithms natural
  to that representation;
- representation-specific correctness theorems;
- a compiler, realization, refinement, or simulation into the canonical layer;
  and
- exact algorithmic results that would become less useful if forced through a
  more general carrier.

A frontend must not acquire a second general-purpose Nash/SPE/continuation
hierarchy merely because the theorem can be restated there.  New general
theory first targets observed EFGs or game forms and is transferred through the
proved boundary. A direct dependency on a Historical module is forbidden
unless the exact importer/imported pair is registered as a
semantic-preservation bridge with a written reason.

### Historical

Historical declarations are retained because they are mathematically valid
and may have downstream users, not because they are the preferred semantics.
They receive correctness fixes, documentation, and preservation regressions
only.  They do not receive parallel general theory.

Do not attach `@[deprecated replacement]` when the replacement changes the
strategy space, information partition, root scope, or deviation quantifier.
In particular, endpoint and occurrence `GameTree` policies are not
interchangeable, state re-rooting is not a lawful subgame certificate, and a
designated continuation is not a complete subgame system.

### Compatibility

A temporary compatibility module:

- must be explicitly listed in both the module-status register and governance
  temporary registry;
- contains only imports and a module docstring;
- names the granular or canonical replacement;
- must not define new implementation; and
- is removed after its real users are zero and the migration is documented.

There are currently zero temporary compatibility modules. The pre-release
broad Interface, implementation aggregate, former EFG-local probability, and
other redirect-only paths were hard-deleted after internal consumers
migrated. New code imports a granular facade or defining leaf.

### Internal and experimental

Internal modules implement a governed facade. Their proof helpers are
name-resolvable through Lean imports but are not individual pre-stability
contracts. They may be reorganized only when the change measurably lowers
dependency or navigation cost. A wrapper is justified only by an identified
downstream consumer. Direct Historical imports require the same exact,
reasoned pairwise exception as Frontend imports; directory-level and wildcard
exceptions are not permitted.

Experimental modules are opt-in and must say what evidence would promote them.
No in-scope module currently needs the Experimental classification; unfinished
mathematical targets belong in the knowledge blueprint rather than in
placeholder Lean declarations.

## Placement rules for maintenance and experimental work

When the API growth freeze is explicitly reopened, place a new declaration at
the lowest layer that can state it honestly:

| Declaration depends on | Home |
|---|---|
| players, profiles, order, or probability only | `Foundation/` or `Math/` |
| strategy/outcome maps without histories | `GameForm/` |
| raw payoff-free state-dependent dynamics | `ExtensiveGame/Structural/Basic` |
| finite transition reachability | `Structural/Reachability` |
| typed action occurrences and payoff-free unfolding | `Structural/History` |
| endpoint-state-payoff compatibility | `ExtensiveGame/Basic` and the matching `Execution` adapter |
| measure-free complete plays or structural termination | `Execution/CompletePlay` or `Execution/Length` |
| terminal-history or complete-path objectives | `Execution/Objective`, exposed by `Interface.Objective` |
| observations, information, chance, or lawful roots | `Observed/`; controlled execution/well-formedness/subgame/finite/quasi/recall infrastructure and structural/subgame/recall morphisms use the matching focused leaf |
| finite/infinite/analytic execution | the corresponding execution implementation, exposed by its facade |
| strict/refinement/coupling/weak representation relation | relation implementation, exposed by `Relations.Discrete` |
| general pure/behavioral/mixed Nash, SPE, recall, or realization | observed/game-form equilibrium layer |
| fresh-clock versus absolute-prefix compatibility | restart implementation, exposed only by `Interface.Restart` |
| syntax-specific recursion or exact solver | the frontend |
| preservation from a frontend | `Compiler/` or that frontend's serializer |

New modules are not added to `EconCSLib.lean` merely because they compile. A
root import requires broad canonical utility, a bounded dependency closure, an
explicit lifecycle decision, and root-boundary regression coverage. Analytic,
restart, compiler, internal, experimental, `Examples`, and `OpenProblem`
modules are opt-in by default.

While the growth freeze is active, this table remains an ownership map for
fixes and refactors, not permission to add Canonical/Frontend declarations.
Usability experiments belong in documentation and `Examples`; reusable
research prototypes remain Experimental until a later policy decision.

### When a new representation is allowed

A new representation is justified only if at least one of the following is
structural rather than cosmetic:

- it admits an algorithm unavailable on the canonical carrier;
- it records data the current carriers cannot express without loss;
- it materially improves executable finite models;
- it is an established external language whose faithful translation matters;
  or
- it isolates a stronger assumption package that yields a useful proof method.

The proposal must identify the information, action-occurrence, chance,
termination, and root semantics that differ from existing frontends.
Directory symmetry, shorter record literals, or a second spelling of an
existing carrier is insufficient.

### When a compiler is required

A frontend must provide a compiler, exact realization, refinement, or
simulation before adding theory that is intended to be representation
independent.  The boundary states exactly what is preserved:

- histories or only endpoints;
- action occurrences or only action values;
- information and public observations;
- chance-law pushforwards or couplings;
- payoff laws or expectations;
- unilateral deviations; and
- designated, selected lawful, or complete lawful roots.

Non-bijective endpoint/occurrence maps are never called isomorphisms.  A weak
serializer that inserts administrative states proves macro-boundary laws
instead of claiming one-step strict equivalence.

### When parallel theory is forbidden

Do not add a frontend-specific general Nash/SPE/continuation theorem when:

1. its statement can be made on `ObservedGame`, `ObservedChanceGame`, or
   `GameForm`;
2. the frontend already has a preservation boundary; and
3. the only remaining proof is transport.

An exception is permitted for an executable solver or structural induction
theorem whose algorithmic content is native to the frontend.  Its result must
still be related to canonical semantics before it is described as a general
EFG theorem.

## Legacy API decisions

| Path or family | Decision | Replacement or distinction |
|---|---|---|
| `BehaviorStrategy` | Deleted after consumer migration; no redirect stub | `ObservedGame.BehavioralStrategy`, normalized chance kernels, and `Finite`/`EqD` |
| `Play` | Deleted after consumer migration; no redirect stub | terminal-aware `Execution.StoppedExecution` / `Finite` |
| `ExtensiveGame.Probability.*` | Deleted after consumer migration; no redirect stubs | `Math.Probability.PMF.*` |
| broad Interface aggregates | Deleted during pre-stability | smallest granular facade |
| split implementation aggregates | Deleted after consumers imported defining leaves | corresponding subdirectory leaves; downstream users prefer facades |
| `Observed.Controlled.Infrastructure` | Canonical declaration-free aggregate facade | defining `Controlled.Infrastructure.*` leaf; winning predicates are in `Winning.Basic` |
| `Observed.Controlled.Morphism` | Canonical declaration-free aggregate facade | `Controlled.Morphism.Core`, `.Subgame`, or `.Recall` according to the declarations used |
| former flat `Observed.ControlledFoo` paths | Removed during pre-stability | corresponding module below `Observed.Controlled`; no forwarding stubs |
| `Observed.PathLawEquivalence` | Deleted in the 2026-08-03 pre-stability audit after a zero-consumer check | use the authoritative payoff-free `ControlledObservedGame.CompletePathLawSemantics` and its nested equivalence/realization declarations |
| endpoint `GameTree` NE/SPE/strategic form | Historical, retained, stopped from general expansion | occurrence compiler for canonical standard SPE; no false deprecation |
| `GameTree.toObservedGame` | Historical endpoint compiler, retained for old policy semantics | occurrence compiler when paths must be distinguished |
| state-based `Strategy` | Historical but semantically valid | observed pure strategy is information-indexed and not definitionally equivalent |
| `Subgame.subgameAt` / `reachableSubgameAt` | Historical state re-root/restriction tools | not synonymous with designated roots or lawful/complete subgame systems |
| `FiniteImperfectGame` | Supported frontend, not a theorem layer | compile via `ObservedCompiler` or `ObservedChanceCompiler` |
| exact deprecated declaration aliases | Hard-deleted after the 2026-08-03 zero-source-consumer audit | replacements remain recorded in `efg-api-migration.md`; new EFG deprecations require a future external-stability policy |
| `ZeroSumChance.GameTree` | Supported specialized frontend | exact rational algorithm has no equivalent replacement |
| `GameForm.LimitSPE` | Historical path with a correct, explicit convergence theorem | indexed continuation Nash on declared roots; it does not certify standard SPE |

Canonical implementation files were audited for obsolete imports. The
governance closeout replaced direct aggregate imports with defining leaves in
the continuation, behavioral-refinement, deferred-sampling,
Kuhn-conditioning, FOSG-sequentialization, and restart-certificate chains.
The four historical broad-aggregate boundary regressions were removed with the
aggregates. Historical imports from
Canonical, Frontend, or Internal modules are rejected unless an exact
importer/imported pair with a reason is present in the governance checker.
The current exceptions are the occurrence-to-endpoint compiler preservation
bridge and the endpoint-policy results used by `FiniteArenaExtraction` and
`Zermelo`.

## Semantic contract rules

Executable/analytic correspondence follows the dedicated
[`two-track semantic compatibility contract`](efg-semantic-compatibility.md).
Shared structural theory must not be duplicated across the tracks. Its fifteen
registered bridge modules are governed as a logical layer rather than a broad
aggregate:

- the executable owner must be in the bridge's import closure;
- the bridge must be in its documented facade's closure;
- executable owners must not import their semantic bridge;
- a registered bridge must contain an equality theorem and may not introduce
  a new `noncomputable` data declaration.

The analytic target remains a current general semantic definition. It is not
assigned Historical or Compatibility lifecycle status merely because an
effective subdomain has an executable counterpart. Exact equality, certified
approximation, and almost-everywhere correspondence remain distinct claims.

The same checker registers twenty algorithm-first owners. Those owners must be
reachable through their finite facade, contain no noncomputable data
declaration, and remain independent of `Simulation`, supplied infinite-path
semantics, finite-law measure interpretation, and direct Mathlib measure-theory
imports. This makes an effective algorithm the default representation rather
than an optimization hidden behind an analytic definition. It does not narrow
the general analytic carrier or theorem domain; algorithm-first is an
operational route for instances that possess an effective realization.

For A19, the checker additionally freezes the direct imports of both
probability aggregates. `EconCSLib.Math.Probability.Effective` imports exactly
`Enclosure`, `Core`, and `Uniform`, so it remains measure-free.
`EconCSLib.Math.Probability.Effective.Analytic` imports exactly that pure
aggregate plus `Semantics` and `UniformSemantics`. Measure, kernel, and integral
dependencies therefore cannot leak back into the executable facade through a
later convenience import.

- The minimal carrier line
  `Arena -> ControlledGame -> ControlledDecisionGame -> ControlledObservedGame`
  is governed by
  [`efg-minimal-core-freeze.md`](efg-minimal-core-freeze.md). Its compatibility
  freeze is deferred while the current API/generality review continues. A
  narrow guard keeps `InfoAction` aligned with the base action universe rather
  than the state universe. New payoff, probability, objective, recall,
  finiteness, root-selection, termination, or solution-concept data should
  still normally belong in an external certificate, adapter, relation,
  execution layer, or compiler. The exact five-module StructuralCore closure
  is a current import-boundary regression, not a compatibility freeze.
- Ambient `ControlledGame.NoChance` and reachable
  `NoChanceOnHistories` are distinct. Pure execution, total pure
  continuation/SPE, winning, and determinacy use the reachable certificate;
  only theorems that inspect arbitrary ambient states should require the
  global predicate.
- An arbitrary `ContinuationSemantics.evaluate` supports only
  evaluator-relative continuation equilibrium.
  No generic standard-EFG-SPE declaration may be added until its strategy
  restriction, deviation extension, and execution carrier are anchored to
  canonical EFG histories or path laws. Caller-defined execution types or
  legality predicates are insufficient. Concrete pure, behavioral, and
  analytic execution layers own their operational equilibrium claims.
- `BoundedHistoryLawFamily` is raw data.
  Execution claims use `CertifiedBehavioralExecutionLaw` or an equally strong
  certificate covering normalization, reachable legality, terminal
  absorption, and agreement with the specified executor.
  `CompletePathLawSemantics` is a per-root lawful marginal family; common
  causal-process, restart, conditioning, and coherence claims remain separate.
- Arbitrary history transforms use `HistoryTransformLawEquivalentAt`.
  Terminal-history terminology requires the terminal-history subtype or an
  equivalent termination proof.
- Signal/public recall is event-clock recall unless an external
  `SignalTraceBuilder` is supplied. Silent-event builders are not identified
  with always-emitting event-clock traces without an explicit hypothesis and
  theorem.
- Optional well-formed bundles remain layered. They may combine represented
  information, mover coherence, and reachable no-chance where repeatedly
  needed, but must not accumulate unrelated finite, payoff, probability,
  recall, or termination assumptions.

## Root aggregate lifecycle

The checker recomputes the root closure from the current source graph. It
currently contains 54 EFG modules and 173 local `EconCSLib` modules. It exposes
measure-free complete plays, structural termination, reusable finite-EFG
certificates, finite/PMF execution, finite `GameTree` syntax and
backward-induction values, but no infinite path law,
historical endpoint-policy equilibrium, Arena extraction, Zermelo theorem,
analytic execution, Restart, FOSG, compiler, or Historical
module.

The governed direct-import closure budgets are recalculated from the current
source graph. As in `efg-public-api.md` and the governance checker, the entry
module itself is excluded:

| Entry | EFG modules / all local modules |
|---|---:|
| `EconCSLib` | 54 / 173 |
| `Interface.StructuralCore` | 5 / 5 |
| `Interface.Core` | 17 / 23 |
| `Interface.Objective` | 33 / 45 |
| `Interface.Winning` | 36 / 48 |
| `Interface.Winning.Stochastic` | 67 / 79 |
| `Interface.Execution.Finite` | 50 / 62 |
| `Interface.Execution.Infinite` | 55 / 67 |
| `Interface.Execution.Analytic` | 82 / 96 |
| `Interface.Relations.Discrete` | 55 / 67 |
| `Interface.Preservation` | 22 / 34 |
| `Interface.Equilibrium.Discrete` | 85 / 103 |
| `Interface.Equilibrium.Analytic` | 125 / 148 |
| `Interface.Restart` | 134 / 157 |
| `Interface.Compilation.Discrete` | 106 / 126 |

| Path | Class | Root decision | Explicit import for opt-in use |
|---|---|---|---|
| `Interface.Execution.Finite` | canonical pre-stability finite/PMF execution | retained as the root EFG facade | same path |
| `Interface.Objective` | canonical pre-stability measure-free objective semantics | opt-in; terminal/path objectives are not required by every root client | same path |
| `GameTree` | canonical specialized frontend | retained | same path |
| `BackwardInduction` | canonical specialized frontend algorithm | retained | same path |
| `ZeroSumGameTreeWithChance` | canonical specialized exact solver | retained | same path |
| `Interface.Execution.Discrete` | deleted pre-release aggregate | removed from source | `Interface.Execution.Finite` or `Interface.Execution.Infinite` according to need |
| `GameTreeSPE` | historical endpoint semantics | removed from root | `EconCSLib.GameTheory.ExtensiveGame.GameTreeSPE` |
| `GameTreeNE` | historical endpoint semantics | removed from root | `EconCSLib.GameTheory.ExtensiveGame.GameTreeNE` |
| `GameTreeStrategicForm` | historical endpoint semantics | removed from root | explicit module import |
| `FiniteArenaExtraction` | canonical but niche frontend bridge | removed from root | explicit module import |
| `Zermelo` | canonical specialized theorem over historical endpoint policies | removed from root | explicit module import |

The migration includes explicit internal imports for existing examples and
positive/negative `RootImportBoundary` regressions. Historical declarations
remain available and receive no false `deprecated` replacement.

## Simulation responsibility matrix

All 40 modules currently under `Simulation/` have one primary responsibility
below.
“Partial” means the name is historically broader or narrower than the current
role; it is not evidence that the declarations are mathematically mixed.

| Module below `Simulation` | Category | Unique primary responsibility | Name fit | Dependency direction | Physical decision |
|---|---|---|---|---|---|
| `Kernel/DiscreteBridge` | analytic execution | exact full-path coherence of discrete and analytic executors | Yes | discrete + analytic execution | Grouped |
| `Kernel/Arena` | analytic execution | non-atomic one-step transition carrier | Yes | Mathlib kernels → analytic execution | Grouped |
| `Kernel/Execution` | analytic execution | legal terminal-aware action and state-step kernels | Yes | arena → policy execution | Grouped |
| `Kernel/Endpoint` | analytic execution | finite endpoint iteration and discrete recovery | Yes | one-step execution → endpoints | Grouped |
| `Kernel/StatePath` | analytic execution | stationary infinite state paths | Yes | endpoint/step → Ionescu–Tulcea path | Grouped |
| `Kernel/HistoryPath` | analytic execution | state-prefix-dependent infinite execution | Yes | path core → history policies | Grouped |
| `Kernel/EventPath` | analytic execution | joint state/action event paths and state projection | Yes | history path → event path | Grouped |
| `Kernel/FiniteExecution` | semantic compatibility | exact state/event one-step and arbitrary finite-prefix correspondence under local measurable realization | Yes | finite history execution + event kernels → analytic execution | Grouped |
| `Kernel/EffectivePathLaw` | semantic compatibility | coherent effective state/event laws and direct tail-law finite marginals | Yes | effective finite queries + continuation paths → analytic execution | Grouped |
| `Kernel/CertifiedPathApproximation` | semantic compatibility | exact prefix-center integration and uniform-certificate interval/search correctness | Yes | executable approximation scheme + effective path semantics → analytic utility guarantee | Grouped |
| `Kernel/FiniteRealizedInformation` | semantic compatibility | exact finite abstract-action realization as the analytic realized kernel | Yes | finite realization compiler + analytic realization → kernel correspondence | Grouped |
| `Kernel/FiniteCompleteEventPath` | semantic compatibility | bounded terminal-absorbing event/state path finite marginals | Yes | finite complete replay + analytic partial trajectories → marginal correspondence | Grouped |
| `Kernel/ObservedEvent` | observed analytic presentation | fixed-information event policies and pullback | Yes | event execution → information presentation | Grouped |
| `Kernel/RealizedInformation` | observed analytic presentation | abstract actions with history-dependent realization | Yes | observed event → realization | Grouped |
| `Presentation/Chance/KernelBridge` | observed analytic presentation | complete-history PMF observed profile to analytic kernel | Yes | observed finite → analytic | Grouped |
| `Presentation/Chance/Realized` | observed analytic presentation | explicit realization certificate | Yes | realization → observed presentation | Grouped |
| `Presentation/Chance/Countable` | effective countable presentation | executable information/action selectors; analytic laws supplied separately | Yes | explicit decisions/encodings → partial operations | Grouped |
| `Presentation/Chance/MeasurableHistory` | observed analytic presentation | explicit measurable history carrier | Yes | observed structure → analytic model | Grouped |
| `Presentation/Chance/Measurable` | observed analytic presentation | uncountable reachable presentation certificate | Yes | measurable history → presentation | Grouped |
| `Presentation/Chance/FiniteExecution` | semantic compatibility | direct observed-chance finite action/event/state execution correspondence | Yes | executable chance adapter + measurable presentation → finite marginals | Grouped |
| `Presentation/Kernel/Core` | observed analytic presentation | non-atomic player/chance kernel presentation | Yes | realized information → kernel profile | Grouped |
| `Presentation/Chance/ProfileAssembly` | profile assembly | exact PMF-to-kernel assembly seam | Yes | old presentation → assembly | Grouped |
| `Presentation/Kernel/ProfileAssembly` | profile assembly | measurable player kernels and deviations | Yes | presentation → profile/deviation | Grouped |
| `Presentation/Kernel/EffectiveBehavioralProfile` | semantic compatibility | effective high-level profile realization and finite event/state marginals | Yes | effective presentation + analytic profile assembly → compiled-policy correspondence | Grouped |
| `Equilibrium/FinitePayoff` | semantic compatibility | exact rational history/prefix expectations as finite Dirac, supplied-coordinate, and partial-trajectory integrals; exact unfinished mass and truncation radius | Yes | finite payoff + truncation + finite execution + supplied paths → integral semantics | Grouped |
| `Equilibrium/EffectivePathUtility` | semantic compatibility | effective simple-observable expectations as the original analytic path-utility integral | Yes | effective law/observable + analytic path utility → representation certificate | Grouped |
| `Equilibrium/Outcome` | outcome/equilibrium | path utility, Nash, termination, and payoff limits | Yes | assembly → economic outcome | Grouped |
| `Continuation/Path` | continuation/conditioning | raw absolute-prefix continuation path | Yes | event path → continuation path | Grouped |
| `Continuation/Conditioning` | continuation/conditioning | raw positive-atom and a.e. conditional bridge | Yes | continuation → conditioning | Grouped |
| `Continuation/FiniteConditioning` | semantic compatibility | exact finite posterior continuation as partial-trajectory and absolute-path finite marginals | Yes | finite conditioning + finite execution + continuation path → analytic correspondence | Grouped |
| `Continuation/Observed` | continuation/conditioning | observed absolute/fresh continuation and equilibrium predicates | Partial: also owns equilibrium adapters | outcome + path → continuation equilibrium | Grouped |
| `Continuation/ObservedConditioning` | continuation/conditioning | observed lift of conditional compatibility | Yes | raw conditioning → observed outcome | Grouped |
| `Restart/Core` | restart | root marker normalization and finite splice | Yes | continuation → restart core | Grouped |
| `Restart/Trajectory` | restart | spliced full and finite trajectory laws | Yes | restart core → trajectory | Grouped |
| `Restart/Certificates` | restart | raw step/path/action certificates | Yes | trajectory → certificates | Grouped |
| `Restart/FiniteExecution` | semantic compatibility | exact fresh, absolute, and spliced finite-law correspondence at every horizon | Yes | finite execution + restart certificates → restart semantics | Grouped |
| `Restart/Observed` | restart | observed profile to state-law compatibility | Yes | certificates → semantic target | Grouped |
| `Restart/Assembly` | restart | baseline and all-deviation compatibility | Yes | observed certificate → deviations | Grouped |
| `Restart/Equilibrium` | restart | canonical compatibility-to-equilibrium route | Yes | assembly → equilibrium | Grouped |
| `Restart/Factorization` | restart | statistic/rebase sufficient constructors | Yes | raw certificates → constructors | Grouped |

### Implemented physical-layout changes

Four Internal modules with unambiguous ownership were moved without
compatibility wrappers because their old implementation paths were never
promised public API:

| Old path below `Simulation` | New implementation path | Reason |
|---|---|---|
| `KernelArena` | `Execution/Discrete/KernelArena` | owns the finite PMF transition carrier |
| `KernelTrajectory` | `Execution/Discrete/KernelTrajectory` | owns finite PMF execution and trace laws |
| `Morphism` | `Relations/Discrete/Morphism` | owns deterministic Arena relations |
| `KernelWeakSimulation` | `Relations/Discrete/KernelWeakSimulation` | owns probabilistic weak/stuttering relations |

The 40 Internal analytic and semantic-compatibility modules are grouped below
`Kernel/`, `Presentation/`, `Equilibrium/`, `Continuation/`, and `Restart/`.
The finite/analytic bridge is a new Internal leaf; the preceding regrouping
was a path-only cleanup whose declaration names and public facades did not
change. Repeated semantic prefixes live in directory names instead of every
filename. The former
`ObservedMeasurableKernelRestartCompatibility` aggregate was deleted; clients
use `Interface.Restart`.

## Large-file audit

The audit covers every EFG `.lean` source with at least 800 physical lines.
Stable bands replace volatile exact line and declaration counts. The governance
checker verifies both complete membership and the recorded band; crossing a
band or the 800-line threshold therefore requires an explicit review without
turning routine small edits into documentation churn.

| Module | Line band | Main responsibility | Cohesion / split trigger | Decision |
|---|---:|---|---|---|
| `EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Morphism.Core` | `1200+` | payoff-free `Hom`, information refinement, strict `Iso`, and Iso algebra | Three carrier-transport families share the same dependent casts; split only when a real consumer avoids a measured closure and the module-path migration is reviewed | Queue measured `Hom` / refinement / `Iso` split; do not grow paths during the API freeze |
| `EconCSLib.GameTheory.ExtensiveGame.Observed.FiniteUnfolding` | `1200+` | finite occurrence unfolding and structural/stochastic preservation | One compiler-preservation chain; split when a second independent consumer needs only construction or only preservation | Keep |
| `EconCSLib.GameTheory.ExtensiveGame.Compiler.GameTreeOccurrenceObserved` | `1200+` | occurrence compiler, endpoint refinement bridge, and finite SPE | One public compiler route; revisit at the next independent compiler theorem | Keep |
| `EconCSLib.GameTheory.ExtensiveGame.Simulation.Restart.Certificates` | `1000-1199` | implications among restart step, prefix, and full-path certificates | One splice/index induction graph | Keep |
| `EconCSLib.GameTheory.ExtensiveGame.Simulation.Kernel.EventPath` | `1000-1199` | analytic event paths, policies, and state projection | One Ionescu--Tulcea construction and projection chain | Keep |
| `EconCSLib.GameTheory.ExtensiveGame.Simulation.Continuation.Observed` | `1000-1199` | absolute/fresh continuation and bounded/terminal equilibrium | Shared clock and prefix identities; revisit when another independent utility regime appears | Keep |
| `EconCSLib.GameTheory.ExtensiveGame.Simulation.Equilibrium.Outcome` | `1000-1199` | path utility, Nash, termination, and convergence | Shared measurability/integrability lemmas; split only for an independent outcome family | Queue on new outcome family |
| `EconCSLib.GameTheory.ExtensiveGame.Simulation.Presentation.Kernel.ProfileAssembly` | `1000-1199` | measurable player/chance profile and deviation assembly | Cross-cutting measurable tagged-fiber instances | Keep |
| `EconCSLib.GameTheory.ExtensiveGame.Simulation.Kernel.FiniteExecution` | `800-999` | exact finite-law interpretation of state/event history execution at one and arbitrarily many finite steps | State and event proofs share prefix reindexing, terminal absorption, and one induction route; split only if a measured consumer can avoid one half and the facade closure decreases | Keep |
| `EconCSLib.GameTheory.ExtensiveGame.Simulation.Restart.Observed` | `800-999` | observed restart compatibility plus effective continuation/fresh-restart finite-marginal bridges | The new bridges share the same high-level profile and restart semantic owners; split if a narrower facade can expose them without the compatibility theorem matrix | Keep |
| `EconCSLib.GameTheory.ExtensiveGame.Compiler.GameTreeObserved` | `800-999` | endpoint observed compiler and direct profile outcome evaluation | Structural recursion, outcome correctness, and the termination-plan chain share dependent history evidence; split only if a measured consumer avoids one half | Keep |
| `EconCSLib.GameTheory.ExtensiveGame.FOSG.FOSGContinuation` | `800-999` | finite FOSG and serialized-continuation payoff laws, bridges, and Nash transfer | Source/target root relations and explicit macro-policy data couple the law, coupling, and equilibrium proofs; split only on measured closure reduction | Keep |
| `EconCSLib.GameTheory.ExtensiveGame.Observed.Morphism.Structural` | `800-999` | payoff-aware strict observed-game isomorphism and structural transport | Dependent history/action transport is shared; split only on measured adapter demand | Queue on measured import demand |
| `EconCSLib.GameTheory.ExtensiveGame.Observed.Kuhn` | `800-999` | finite hypotheses, behavioral-to-mixed construction, and realization | One proof progression with shared conditioning tables | Keep |
| `EconCSLib.GameTheory.ExtensiveGame.Observed.KuhnConditioning.Execution` | `800-999` | partial posterior disintegration and bounded mixed-to-behavioral execution laws | Zero-mass handling and positive-atom induction form one proof chain; split only if a consumer can avoid either the conditioning or execution half | Keep |
| `EconCSLib.GameTheory.ExtensiveGame.Observed.BehaviorMorphism` | `800-999` | behavioral strategy, law, and equilibrium transport | Dependent action casts connect all stages | Queue on measured import demand |
| `EconCSLib.GameTheory.ExtensiveGame.Observed.SPE` | `800-999` | termination-certified continuation semantics and standard pure SPE | Root, termination, and Iso transfer theorems share one transport chain | Keep |
| `EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Infrastructure.Recall` | `800-999` | classic, signal, public recall, and factorization certificates | Trace builders and recall hierarchy share dependent list transport | Keep |
| `EconCSLib.GameTheory.ExtensiveGame.Winning.Determinacy` | `800-999` | finite and well-founded logical determinacy | One well-founded recursion route; descriptive-set determinacy belongs in a separate future owner | Keep |
| `EconCSLib.GameTheory.ExtensiveGame.Observed.Game` | `800-999` | payoff-aware observed-game compatibility carrier and pure execution | Central adapter owner; split only when a leaf can avoid the carrier construction closure | Keep |
| `EconCSLib.GameTheory.ExtensiveGame.Simulation.Restart.Assembly` | `800-999` | lift raw restart certificates across all deviations | Deliberate theorem matrix over one certificate family | Keep |
| `EconCSLib.GameTheory.ExtensiveGame.Observed.Continuation` | `800-999` | pure and behavioral continuation compatibility adapters | Two parallel halves; split only when a client measurably avoids one half | Queue on measured import demand |

The current worktree contains the high-value, dependency-ordered splits for
controlled morphisms, continuation game forms, observed
morphisms/refinements, deferred sampling, Kuhn conditioning, FOSG
sequentialization, and Restart. The controlled-morphism split was driven by
three independently useful dependency closures, not line count alone. No
additional low-risk/high-benefit split was identified; the remaining
mechanical line-count splits would either cut a single induction/transport
chain or add wrappers without reducing facade closure.

The 2026-08-03 distribution pass moved reusable-module regression data to four
opt-in example modules and removed zero-consumer exact declaration aliases.
Neither change justifies splitting a cohesive implementation module: example
ownership and API compatibility are enforced independently by source scans
and negative facade regressions.

## Maintenance queue and stop conditions

1. Revisit `Controlled.Morphism.Core` only with a measured closure reduction
   and an explicit module-path migration decision; line count does not reopen
   the Canonical/Frontend API-growth freeze.
2. Revisit `Observed.Continuation` only if a real client can avoid a material
   behavioral or pure dependency by importing one half.
3. Revisit `BehaviorMorphism` only after its dependent-cast helpers can be
   packaged without duplicating proof state.
4. Revisit analytic outcome/continuation files when a second independent
   outcome or continuation family makes the current cohesion false.
5. Revisit the large compiler files during a planned compiler API release,
   not during unrelated theorem work.
6. Retain Restart `Certificates` and `Assembly` while their implication graphs
   remain single proof chains; line count alone is not a split trigger.
7. Consider further physical `Simulation/` moves only when ownership is as
   unambiguous as the discrete execution/relation moves or an import-closure
   measurement demonstrates a reduction. Navigation aesthetics alone do not
   pass the gate.
8. Keep historical root removals covered by explicit-import examples and
   negative root guards.

This queue is intentionally part of the governance document rather than a new
collection of one-off audit files.

## Declaration lifecycle triage

CI generates a conservative theorem/lemma usage report with:

```bash
python3 scripts/report_efg_declaration_usage.py \
  --check --output /tmp/efg-declaration-usage.md
```

The report is not a dead-code oracle. It classifies zero-source-indegree
declarations into source-documented or repository-backed endpoints,
unclassified Canonical/Frontend endpoints, Internal/private helpers, and
lifecycle-specific review. A declaration is removed or privatized only after
manual confirmation that it has no mathematical endpoint role, downstream
compatibility role, documentation role, example/test role, or external
consumer.

The generated zero-source-indegree queue is split deterministically into:
repository-backed public endpoints, source-doc endpoints,
`[simp]`/normalization API, positive facade-contract declarations,
compiler-preservation endpoints, proof helpers, historical-only declarations,
and a residual unclassified-public review bucket. Negative `#guard_msgs`
checks are excluded from positive facade evidence. The last label still
requires mathematical and downstream review; it is not a dead-code verdict.

The current residual ceiling is **0**, recorded in the report script. It is
not a claim that all zero-indegree endpoints should be deleted. Before the API
growth freeze, endpoint evidence could justify a new Canonical/Frontend
endpoint; during the freeze, the separate surface baseline rejects the
addition even when it is documented.

## Enforceable invariants

The source-graph portion of this policy is checked in CI with:

```bash
python3 scripts/check_efg_governance.py
```

The Canonical/Frontend API-growth decision is checked independently with:

```bash
python3 scripts/check_efg_api_growth.py
```

The check makes closure changes deliberate: a facade or root dependency change
must update its boundary regression and the audited count in this policy,
rather than remaining an invisible transitive import. Review and CI maintain:

- zero-byte and comment/namespace-only Lean files are rejected;
- every import-only Lean module is explicitly registered as a canonical
  facade/aggregate or temporary compatibility path;
- the current inventory is 23 canonical import-only modules and zero
  temporary compatibility modules;
- deleted module paths cannot be recreated or imported;
- no minimal carrier declaration is currently fingerprint-frozen;
- the 97 registered Canonical/Frontend modules currently own 1,670 explicit
  public source declarations and remain below the 1,689-declaration ceiling;
  the current count is 19 below that ceiling. The 2026-09-04 A19 decision adds
  exactly two zero-declaration aggregate paths—measure-free `Effective` and
  opt-in `Effective.Analytic`—to the module-path baseline without changing the
  declaration ceiling or reopening declaration growth;
- a focused source check requires `ControlledDecisionGame.base :
  ControlledGame.{uN, uA, uS} N`, `InfoAction ... : Type uA`, and the matching
  universe order on the `ControlledObservedGame` extension, preventing the
  base action/state universe swap from recurring;
- `Interface.StructuralCore` has exactly the five structural EFG dependencies
  and `Interface.Core` cannot regain Objective/Winning;
- every payoff-free `Controlled.Infrastructure.*` leaf obeys the existing
  reverse-dependency prohibition;
- `Controlled.Infrastructure.Recall` has its exact six-module closure and
  cannot regain `Finite` or `Execution.Length`;
- `Controlled.Morphism.{Core,Subgame,Recall}` retain their exact 9 / 9,
  11 / 11, and 12 / 12 closures without cross-layer leakage;
- `Observed.Controlled.Infrastructure` and `Observed.Controlled.Morphism`
  remain declaration-free canonical facades with exact direct leaf imports,
  while internal consumers import defining leaves;
- the complete `Observed.Controlled` hierarchy is fixed by a registered role
  map, and flat `Observed.ControlledFoo` siblings are forbidden;
- canonical controlled modules cannot reach the three `.Compat` payoff-aware
  adapters, whose exact imports and namespaces are fixed;
- the governed EFG/GameForm/direct probability-support source graph is acyclic;
- the semantic-regime routes keep finite PMF, infinite discrete,
  analytic-kernel, and FOSG compilation ownership distinct while requiring
  the two full-path producers to point toward the common lawful path carrier;
- every EFG source at or above 800 physical lines appears exactly once in the
  machine-checked large-file audit with the correct stable line band;
- Canonical, Frontend, and Internal modules do not directly import Historical
  modules except for exact, reasoned importer/imported allowlist pairs;
- `Structural.History` cannot import `Subgame`, and `StochasticGameTree` cannot
  import `GameTreeSPE`;
- `Core`, `Finite`, `Infinite`, `Analytic`, relations, equilibrium, Restart,
  and Compilation keep their documented negative sentinels;
- root does not gain Historical paths, infinite path,
  analytic, restart, FOSG, or compiler modules transitively;
- Restart and Compilation remain sibling branches;
- `Math/Probability/FiniteLaw`, `Math/Probability/FiniteMarkovChain`,
  `Math/Probability/RationalIntervalUnion`, and the legacy-internal
  `Math/Probability/PMF` modules import no game theory;
- `Examples` and `OpenProblem` do not enter governed library aggregates;
- reusable EFG/GameForm/direct probability-support modules do not declare
  under `namespace Examples`,
  and example-only fair-coin data does not return to `StochasticGameTree`;
- any future temporary compatibility module must appear in both explicit
  registries and name a replacement;
- no `@[deprecated]` EFG declaration is retained during pre-stability;
  completed replacement maps live in
  [`efg-api-migration.md`](efg-api-migration.md);
- the unexplained zero-source-indegree Canonical/Frontend endpoint queue does
  not grow beyond its recorded baseline;
- no ordinary `sorry` or `admit` appears below `EconCSLib/`; and
- no compatibility, historical, or internal status is inferred solely from a
  filename: the source responsibility is checked.

CI separately runs:

```bash
python3 scripts/build_efg_modules.py --fresh
```

The lifecycle register is the script's only build-module list. The script
rejects register/source drift, removes only registered artifacts plus the
governance checker's exact removed-path artifacts in fresh mode, asks Lake to
build every registered EFG, GameForm, and direct probability-support module in one
invocation, and verifies one nonempty `.olean` per registered source. This
covers canonical, frontend, historical, and internal modules without
importing them into `EconCSLib.lean`, while preventing removed paths from
surviving through stale project artifacts.

These checks provide machine-checked evidence for source elaboration, the
axiom surface, placeholder policy, module boundaries, and the listed formal
semantic properties. They are not a metamathematically complete certification
of every intended model meaning.
