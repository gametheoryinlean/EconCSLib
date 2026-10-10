# Extensive-Game Architecture Exploration

**Status:** implemented and Lean-verified architecture, 2026-07-20

This note starts the next extensive-form game (EFG) design iteration.  It does
not declare the current API final.  The method is theorem-driven: keep several
presentations available, state concrete preservation and equilibrium targets,
and use small Lean proofs to determine which interfaces are viable.

The central conclusion is that EconCSLib should not choose one of the existing
`GameTree`, `ExtensiveGame`, or `FiniteImperfectGame` structures as the single
EFG representation.  Instead, it should use a layered architecture:

```text
compact / proof-oriented presentations

  Arena        GameTree        FOSG        other finite syntax
    |              |             |
    +------ compile / unfold / relate -----+
                         |
                         v
              history-indexed observed EFG
                         |
                         v
            strategy/outcome semantic form
                         |
                         v
          Nash, realization, and value results
```

`Arena` remains the general transition-system foundation.  Histories, turns,
observations, information states, chance laws, strategies, and terminal
outcomes belong in layers above it.  `GameTree` remains a useful finite
perfect-information proof language.  Representation-independent results should
be transferred through explicit morphisms rather than reproved against every
syntax.

The first transfer layer is now implemented:

- [`Morphism.lean`](../../EconCSLib/GameTheory/ExtensiveGame/Relations/Discrete/Morphism.lean)
  defines strict Arena morphisms/isomorphisms and relational
  simulations/bisimulations;
- [`GameForm/Basic.lean`](../../EconCSLib/GameTheory/GameForm/Basic.lean)
  defines deterministic strategy/outcome forms, composable morphisms,
  deviation-sensitive Nash reflection, and game-form isomorphisms;
- [`GameForm/Continuation/Core.lean`](../../EconCSLib/GameTheory/GameForm/Continuation/Core.lean)
  defines representation-neutral families of continuation game forms with one
  shared complete strategy space, declared roots, composable semantic
  morphisms/isomorphisms, and generic Nash-on-declared-roots reflection/two-way transfer;
- [`GameForm/Law.lean`](../../EconCSLib/GameTheory/GameForm/Law.lean)
  makes normalized outcome laws primitive, defines exact composable
  `RealizesVia`, law-preserving morphisms/isomorphisms, and reuses the existing
  deviation-sensitive Nash-transfer layer through `toGameForm`;
- [`GameTreeObserved.lean`](../../EconCSLib/GameTheory/ExtensiveGame/Compiler/GameTreeObserved.lean)
  packages the `GameTree`/observed-game correspondence as a `GameForm.Iso`.
- [`GameTreeOccurrenceObserved.lean`](../../EconCSLib/GameTheory/ExtensiveGame/Compiler/GameTreeOccurrenceObserved.lean)
  provides a second, occurrence-sensitive `GameTree` compiler, proves perfect
  information and perfect recall, and relates it to the endpoint compiler by
  explicit information forgetting and strategy lifting.
- [`FiniteImperfectObserved.lean`](../../EconCSLib/GameTheory/ExtensiveGame/Compiler/FiniteImperfectObserved.lean)
  completes compact finite imperfect-game labels into genuine player-indexed
  decision information, transports declared abstract actions through explicit
  concrete equivalences, and compiles the result to `ObservedGame` with explicit
  admitted-root data.
- [`Morphism/Structural.lean`](../../EconCSLib/GameTheory/ExtensiveGame/Observed/Morphism/Structural.lean)
  defines strict structural observed-EFG isomorphisms and proves exact
  mapping and composition; operational and continuation transfer are split
  into neighboring `Morphism/Operational.lean` and
  `Morphism/Continuation.lean` leaves.
- [`PerfectRecall.lean`](../../EconCSLib/GameTheory/ExtensiveGame/Observed/PerfectRecall.lean)
  defines personal information/action histories, singleton information, and
  perfect recall; adds compiler-facing recall factorization certificates
  equivalent to that predicate; and proves strict-isomorphism transfer in both
  directions.
- [`SPE.lean`](../../EconCSLib/GameTheory/ExtensiveGame/Observed/SPE.lean)
  turns existential pure termination into a choice-independent total outcome
  and proves standard pure-SPE transfer relative to an explicit lawful
  `SubgameSystem`.
- [`Refinement/Core.lean`](../../EconCSLib/GameTheory/ExtensiveGame/Observed/Refinement/Core.lean)
  defines composable information refinements, exact strategy lifting and
  execution, directional Nash-on-designated-continuations reflection, and two-way transfer under an
  explicit strategy-surjectivity condition.
- [`Chance.lean`](../../EconCSLib/GameTheory/ExtensiveGame/Observed/Chance.lean)
  adds normalized history-indexed chance kernels and strict chance-law
  naturality.
- [`Behavior.lean`](../../EconCSLib/GameTheory/ExtensiveGame/Observed/Behavior.lean)
  defines information-indexed behavioral profiles and the genuine
  chance-consistent history policies they induce.
- [`BehaviorMorphism.lean`](../../EconCSLib/GameTheory/ExtensiveGame/Observed/BehaviorMorphism.lean)
  transports those profiles through strict observed chance-EFG
  isomorphisms, proves exact bounded history and payoff-law naturality, and
  transfers behavioral Nash on presentation-designated continuations in both directions.
- [`BehaviorRefinement/Execution.lean`](../../EconCSLib/GameTheory/ExtensiveGame/Observed/BehaviorRefinement/Execution.lean)
  extends information refinements with exact chance-kernel naturality, lifts
  behavioral profiles, preserves complete bounded history and payoff `PMF`s,
  reflects behavioral Nash on presentation-designated continuations from fine to coarse information, and gives
  two-way transfer under explicit behavioral-strategy surjectivity.
- [`Realization.lean`](../../EconCSLib/GameTheory/ExtensiveGame/Observed/Realization.lean)
  exposes bounded behavioral payoff semantics as a `LawGameForm`. Strict
  observed chance-EFG isomorphisms and chance-aware information refinements
  become law isomorphisms/morphisms whose preservation equations are uniform
  `RealizesVia` witnesses.
- [`Mixed.lean`](../../EconCSLib/GameTheory/ExtensiveGame/Observed/Mixed.lean)
  defines classical mixed strategies as laws on complete pure contingent
  plans, independently samples the finite player family once before play,
  proves the Dirac/pure-as-behavioral regression, and transports complete
  mixed payoff laws, Nash equilibrium, and bounded mixed Nash on presentation-designated continuations exactly through
  strict observed chance-EFG isomorphisms.
- [`Kuhn.lean`](../../EconCSLib/GameTheory/ExtensiveGame/Observed/Kuhn.lean)
  treats Kuhn equivalence as exact realization rather than strategy
  isomorphism. It defines root-scoped and continuation-wide certificates,
  compiles them to law/continuation morphisms with semantic deviation
  completeness, derives Nash and conditional designated-continuation Nash transfer, and constructs the
  finite-information behavioral-to-mixed plan law with exact abstract and
  concrete action marginals. `FiniteInformationHypotheses` gives that
  construction exactly the assumptions it consumes. The additive
  `FiniteNoAbsentMindednessHypotheses` layer supplies the strictly stronger
  no-repeated-key property needed by execution-law comparison; perfect recall
  is separately proved to imply no-absent-mindedness and remains available
  through compatibility wrappers.
  The root/continuation distinction prevents the false claim that perfect
  recall alone makes an arbitrary ex-ante mixed profile behaviorally
  equivalent at every off-path subgame simultaneously.
- [`FiniteProduct.lean`](../../EconCSLib/Math/Probability/PMF/FiniteProduct.lean),
  [`Equiv.lean`](../../EconCSLib/Math/Probability/PMF/Equiv.lean), and
  [`Coupling.lean`](../../EconCSLib/Math/Probability/PMF/Coupling.lean)
  host the representation-neutral finite dependent-product, equivalence
  pushforward, and relational-coupling APIs. Probability-only clients therefore
  do not import stochastic transition or EFG structures.
- [`ConditionalSampling.lean`](../../EconCSLib/Math/Probability/PMF/ConditionalSampling.lean)
  and
  [`ConditionalProduct.lean`](../../EconCSLib/Math/Probability/PMF/ConditionalProduct.lean)
  prove total discrete fiber conditioning, exact disintegration, and
  coordinate conditioning for finite independent dependent products.
- [`KuhnConditioning/Realization.lean`](../../EconCSLib/GameTheory/ExtensiveGame/Observed/KuhnConditioning/Realization.lean)
  constructs the root-scoped mixed-to-behavioral map by conditioning on
  continuation-relative personal decisions. It proves exact bounded
  history/payoff-law realization, semantic unilateral-deviation coverage,
  two-way root Nash transfer, and the full bounded designated-continuation Nash equivalence for a
  behavioral profile and its independently sampled complete-plan profile.
  The SPE proof uses rootwise semantic deviation completeness and does not
  assert a false root-independent behavioralization of arbitrary mixed plans.
- [`DeferredSampling.lean`](../../EconCSLib/Math/Probability/PMF/DeferredSampling.lean)
  defines a representation-neutral fresh-query tree with terminal, chance,
  and one-use query nodes. Finite dependent-product point masses, arbitrary
  coordinate splitting, PMF bind commutativity, and structural freshness give
  exact equality between full-table presampling and adaptive on-demand
  sampling.
- [`DeferredSampling/Realization.lean`](../../EconCSLib/GameTheory/ExtensiveGame/Observed/DeferredSampling/Realization.lean)
  compiles bounded observed chance-EFG execution to the fresh-query tree.
  No-absent-mindedness propagates a future-closed set of available
  player/information keys. Under finite information, the resulting theorem
  identifies behavioral execution with independently sampled pure plans at
  the levels of complete history laws and optional payoff laws, from every
  continuation root. It packages this direction as a continuation morphism
  and gives one-way designated-continuation Nash reflection without perfect recall. The two-way Kuhn
  results retain perfect recall and isolate semantic deviation completeness
  as the exact additional premise.
- [`Continuation.lean`](../../EconCSLib/GameTheory/ExtensiveGame/Observed/Continuation.lean)
  compiles bounded pure and behavioral observed-EFG continuation semantics to
  the generic continuation-family layer. Strict isomorphisms become semantic
  family isomorphisms; information refinements become family morphisms and
  graph-root simulations, so their designated-continuation Nash theorems are instances of one
  representation-neutral proof and compose with relational weak-serialization
  simulations.
- [`MorphismHierarchy.lean`](../../EconCSLib/GameTheory/ExtensiveGame/Observed/MorphismHierarchy.lean)
  makes the structural hierarchy explicit. Every strict observed-EFG
  isomorphism induces a pure and chance-aware information refinement; its pure
  and behavioral strategy maps agree with strict transport and are
  automatically surjective. Strict designated-continuation Nash transfer is re-derived through the
  refinement and continuation-family layers.
- [`KernelArena.lean`](../../EconCSLib/GameTheory/ExtensiveGame/Execution/Discrete/KernelArena.lean)
  defines stochastic transition systems and their functional/relational
  morphisms, while
  [`KernelTrajectory.lean`](../../EconCSLib/GameTheory/ExtensiveGame/Execution/Discrete/KernelTrajectory.lean)
  provide exact marginal-preserving coupling composition, terminal-aware
  randomized Markov policy matching, stopped finite-horizon state/trace-law
  transfer, and related-observable law equality.
- [`KernelWeakSimulation.lean`](../../EconCSLib/GameTheory/ExtensiveGame/Relations/Discrete/KernelWeakSimulation.lean)
  packages positive finite serialized executions as macro actions and
  proves that probabilistic weak refinement induces both a kernel simulation
  at macro boundaries and a progressing support-path simulation.
- [`FOSG.lean`](../../EconCSLib/GameTheory/ExtensiveGame/FOSG/FOSG.lean)
  defines FOSG macro dynamics, history-augmented observations, and the
  chance-consistent weak-serialization boundary.
- [`Sequentialization/Equilibrium.lean`](../../EconCSLib/GameTheory/ExtensiveGame/FOSG/Sequentialization/Equilibrium.lean)
  implements that boundary for `Fin (n + 1)` players and proves exact initial
  and one-macro-step distributional coupling, a macro-boundary kernel
  simulation, compilation of arbitrary history-level randomized joint-action
  policies and information-indexed behavioral profiles, stopped finite-horizon
  trace coupling, initialized optional-terminal-payoff/utility-law equality,
  and a genuine
  target observed-EFG behavioral-profile compiler commuting with unilateral
  deviation.
- [`FOSGBehavioralSerialization.lean`](../../EconCSLib/GameTheory/ExtensiveGame/FOSG/FOSGBehavioralSerialization.lean)
  isolates the reusable finite-player strategic obligations for any weak
  serializer: playerwise behavioral-strategy equivalences, genuine target
  finite-horizon optional terminal-payoff laws, exact law equality at related
  macro roots and initialization, and source-root coverage. It constructs the relational
  continuation simulation and initialized game-form isomorphism generically.
- [`FOSGContinuation.lean`](../../EconCSLib/GameTheory/ExtensiveGame/FOSG/FOSGContinuation.lean)
  instantiates that generic bridge with the genuine micro-execution laws of
  the concrete compiler. Its declared-root and full finite-horizon behavioral
  Nash-on-declared-macro-continuations theorems are direct instances of the
  generic transfer theorem.

## Why the current models are not interchangeable

### Arena is a transition system, not an EFG history tree

`Arena` has exactly the right raw data for a state machine: state-dependent
actions and a transition function.  It supports infinite state spaces and
cycles.  It deliberately does not say how a state was reached.

That distinction is essential.  Two action histories can reach the same world
state while giving players different memories or public observations.  Treating
the endpoint state as the EFG node silently merges those histories.  It also
makes perfect recall, augmented information states, and public partitions
impossible to state faithfully.

The former execution API had a second operational issue. A terminal state has
an empty action type, but `Arena.play` took a total chooser
`(s : State) → Action s`, which cannot exist for an Arena with a terminal
state. That declaration has been removed.
[`StoppedExecution.lean`](../../EconCSLib/GameTheory/ExtensiveGame/Execution/StoppedExecution.lean)
supplies the terminal-aware `HistoryPolicy` and stopped-execution semantics
used by the observed-game layer.

The new [`History.lean`](../../EconCSLib/GameTheory/ExtensiveGame/Execution/History.lean)
starts separating these concepts:

```lean
Arena.History A start s
Arena.HistoryFrom A start
Arena.unfoldFrom A start
ExtensiveGame.unfold G
```

The endpoint remains available for transition, mover, and payoff data, but two
different histories are different states of the unfolding even if their
endpoints are equal.

### GameTree is a specialized proof language

The current inductive `GameTree` is effective for structurally finite,
perfect-information, no-chance backward induction.  Its Kuhn/SPE and Zermelo
developments should be retained while a replacement proves that it can recover
those results.

It is not a suitable general EFG core:

- a `Node` stores child tree values, not action identities or child
  occurrences;
- two actions leading to equal continuations cannot be distinguished reliably;
- strategies are global functions over every `GameTree N U`, not contingent
  plans bound to one game;
- the global `IsGlobalEndpointSubgamePerfect` quantifies over every tree of the same types,
  while the more standard root-scoped API is defined separately;
- chance and imperfect information require parallel tree types.

These are not objections to using `GameTree` for induction.  They are reasons
to compile it into a game-bound semantic layer before reusing general solution
concepts.

There are now two such compilers, with deliberately different information
structures. `GameTree.toObservedGame` observes the endpoint subtree and uses
`NodeInfo`, retaining exact compatibility with the historical
`GameTree.PlayerStrategy`. `GameTree.toOccurrenceObservedGame` observes the
complete typed history and uses the player-controlled occurrence itself as the
information state. The latter has singleton information and hence perfect
recall.

These two observed games share the same base dynamics, concrete actions,
movers, terminal payoffs, and presentation-designated roots, but they are not generally
strictly isomorphic as observed EFGs. Repeated equal subtree values can give
several occurrence information states but only one endpoint information state,
so the forgetting map is not injective. This is a genuine change of
information partitions and strategy spaces, not a notational difference:
the occurrence player may condition on the path, while the endpoint strategy
must choose the same action at identified nodes. Accordingly the implemented
bridge is an `ObservedGame.InformationRefinement`: endpoint strategies lift to
occurrence strategies with identical play. Fine designated-continuation Nash reflects to the
endpoint game. Transfer from endpoint to occurrence requires
`StrategySurjective`, which generally fails precisely because the occurrence
game has additional path-contingent deviations.

The occurrence compiler now also supplies
`occurrenceBackwardInductionProfile_isPureStandardSubgamePerfect` and
`Kuhn_exists_occurrencePureSPE`. These are root-bound standard-SPE theorems
over the complete all-history `occurrenceCompleteSubgameSystem`; their
deviation quantifier ranges over complete history-contingent occurrence
strategies. The separate `occurrenceSubgameSystem` theorem is accurately named
subgame perfection *on* that selected system.
`OccurrenceNonIso` gives the strict boundary example: one occurrence strategy
chooses different children at two equal-subtree occurrences, while every
lifted endpoint strategy is proved to choose the same child at both.

### FiniteImperfectGame duplicates rather than extends Arena

`FiniteImperfectGame` repeats states, actions, transitions, movers, and payoffs
in a separate compact structure. Each information label now declares one
abstract `InfoAction` and an explicit equivalence to every represented
concrete legal-action type. Its `PureStrategy` is indexed by player information
sets only, and `actionAt_same_info` proves equality after transporting concrete
actions back to the shared abstract type.

New imperfect-information theorem work should target the history-indexed layer.
`FiniteImperfectGame` remains a compact finite-state presentation for examples,
without a built-in acyclicity or termination claim, and
`FiniteImperfectObserved.lean` now compiles its transition data and completed
decision information into `ObservedGame`. Nodes carrying the same `some k`
label share one player-indexed information state; an unlabeled player node
receives a singleton information state. `SameActionsOnInfo` is now a derived
coherence theorem; compilation uses the explicit `actionEquiv` directly and
makes no noncanonical representative choice.

Chance-aware clients can additionally supply an
`ObservedChanceCompiler`. Its state-indexed `chanceLaw` is used exactly at
every complete history ending in that compact state, and
`toObservedChanceGame` preserves the existing observed presentation
definitionally. The chance law lives in the compiler certificate rather than
the legacy record, avoiding a source-breaking record-field change.

The source and compiled strategy spaces are both information-indexed. The
compiler completes unlabeled player decisions as singleton information states,
so it does not claim a literal type isomorphism between the two presentations.
Since the old presentation stores neither nonacting-player observations nor
public observations, those components are conservatively trivial, and
presentation-designated continuation roots are explicit compiler-certificate data.

### Chance was fragmented; the common law is now explicit

The Arena model marks nonterminal `mover = none` states as chance states but has
no chance law. `StochasticGameTree` now uses normalized finite `PMF` laws and
occurrence-sensitive policies, while `ZeroSumChance.GameTree` retains its
separate rational syntax and zero-sum evaluator.

`StochasticGameTreeObserved.lean` now supplies the occurrence-sensitive
compiler to `ObservedChanceGame`. It preserves player action laws and chance
kernels exactly, proves bounded endpoint and vector-payoff `PMF` equality
after forgetting complete target histories, and commutes with source pure
unilateral deviations. This is an exact realization statement, not a strict
isomorphism: endpoint projection forgets occurrence identity.

`ObservedChanceGame` is now the common general layer: it attaches a `PMF` to
the legal dependent action type at each nonterminal chance history.
Normalization is enforced by the type. Its strict isomorphism additionally
requires that pushing a source law through the action equivalence gives the
target law exactly. The specialized rational `ZeroSumChance.GameTree`
evaluator remains separate because its structural strategy space identifies
repeated child-pair contexts while the occurrence target admits more
deviations; a future bridge must therefore be phrased as a directional
information refinement or exact realization, not an assumed strategy
isomorphism.

## Selected direction

### 1. Keep Arena minimal

The raw foundation remains:

```lean
structure Arena where
  State  : Type*
  Action : State → Type*
  next   : (s : State) → Action s → State
```

Finiteness, acyclicity, termination, turn-taking, and observation assumptions
stay out of `Arena`.  They are predicates or data in the consuming layer.

### 2. Make histories explicit

The dependent history type records action occurrences:

```lean
inductive Arena.History (A : Arena) (start : A.State) : A.State → Type _
  | nil
  | snoc (h : A.History start s) (a : A.Action s)
```

This supports two distinct uses:

- `A.History start s` expresses paths to a fixed state and makes unique-history
  conditions meaningful;
- `A.HistoryFrom start := Σ s, A.History start s` supplies the node type of the
  unrolled game tree.

The old `TreeShapedFrom` condition quantified over proofs of a proposition,
`Arena.Reachable`.  Proof irrelevance made that condition true for every Arena.
It now quantifies over `Arena.History`, so it genuinely asserts at most one
action history to each state.

### 3. Add a game-bound decision layer with optional observations

[`Game.lean`](../../EconCSLib/GameTheory/ExtensiveGame/Observed/Game.lean)
implements the first wrapper over an Arena game and its histories rather than
copying transition data. The current carrier deliberately separates:

- `ControlledDecisionGame`, which owns decision information and actions
  without requiring any observation carrier;
- `Observation i`, defined for every player at every history;
- `PublicObservation`, also defined at every history;
- `InfoState i`, indexing player decision information only;
- `infoAt`, defined when the base mover is `some i` and the endpoint carries
  constructive `IsDecision` evidence;
- `InfoAction i I`, with an equivalence to the underlying Arena action at each
  represented decision history.

This separation matters.  If all-history observations were themselves the
domain of pure strategies, terminal observations with empty Arena actions
would make the pure-strategy type uninhabited.  The prototype still leaves
terminal outcome semantics to later layers; for no-chance games it uses the
base mover and terminal payoff fields, while `ObservedChanceGame` supplies the
separate chance-law layer.

The action equivalence is load-bearing. A witness-backed subtype removes raw
information values that do not occur at a real decision, so the strategy types
are:

```lean
PureStrategy G i :=
  (I : G.RepresentedInfo i) → G.InfoAction i I.1
BehavioralStrategy G i :=
  (I : G.RepresentedInfo i) → PMF (G.InfoAction i I.1)
```

Thus two histories in the same information state are forced to use the same
abstract action or distribution.  Proof obligations then show that the
abstract action is legal at each represented decision history. Unused raw
`InfoState` values do not enlarge or empty the strategy space.

The following should be predicates, not fields stored merely for convenience:

- finite players, histories, information states, or actions;
- bounded horizon or well-founded continuation;
- perfect information;
- perfect recall;
- no chance;
- timeability;
- no thick public states;
- caller-declared continuation-root admissibility.

### 4. Treat augmented EFG as the observation-complete form

Classical acting-player information sets forget what non-acting players observe.
The augmented layer instead gives every player an observation at every history
and gives every history a public observation.  Each player's observation must
refine the public observation.  Decision information states additionally map
back to the acting player's all-history observation.

This is the right target for a FOSG bridge.  A FOSG world state remains a
compact implementation state; its unrolling records realized joint actions,
next states, private observations, and public observations.  The resulting
player views and public views define the augmented EFG partitions.

Simultaneous FOSG steps need not be forced into the turn-taking Arena core.
A bounded bridge may serialize one joint step into player decisions followed
by a chance transition, provided it proves that the serialization preserves
the trajectory and outcome laws.

The implemented FOSG interface therefore uses two related stochastic objects:

- `historyKernelArena`, whose state is a complete realized FOSG history and
  whose action is a simultaneous joint action;
- `WeakSerialization`, which implements one such macro action by positive-fuel
  execution in an observed chance EFG.

The latter requires a coupling with exact source and target marginals, support
inside the macro-state relation, target chance-kernel consistency, observation
and public-state preservation, terminal payoff equality, and exact
correspondence of caller-declared macro roots.  Those declarations are not by
themselves standard-subgame certificates.  It is not called an isomorphism
because serialization may add
several administrative decision and chance histories per FOSG macro step.
This is a structural obstruction, not a weakening chosen for convenience:
a strict history-Arena isomorphism requires a bijection of history nodes and
matches one source step with exactly one target step, whereas this serializer
replaces one simultaneous source step by `n + 2` target steps.  Exactness is
therefore stated at macro boundaries through PMF couplings and
weak/stuttering simulation; no probability or payoff approximation is
introduced.

The concrete `Fin (n + 1)` compiler makes this distinction executable.  It
collects individual actions in index order while keeping previous choices out
of every private and public observation, then uses the original FOSG
transition `PMF` at a chance node.  A `FOSG.DecisionModel` ensures legal action
types depend on player information rather than exposing hidden world state.
The compiler proves that one macro step is exactly `n + 2` target steps and
that the target endpoint law is the source transition law pushed through the
serialization endpoint map.

### 5. Add semantic transfer targets, but do not confuse them with EFG syntax

Elazar's `GameTheory` library uses a useful two-level semantic target:

```lean
structure GameForm (N : Type) where
  Strategy      : N → Type
  Outcome       : Type
  outcomeKernel : Profile → PMF Outcome
```

A utility-bearing game adds an outcome utility function.  Concrete NFG, EFG,
FOSG, MAID, and other languages compile into this target.  Morphisms preserve
outcome or utility distributions; isomorphisms additionally give per-player
strategy equivalences.

EconCSLib should test a small compatible interface rather than port the entire
framework immediately.  It gives the correct home for representation-neutral
Nash and outcome-law theorems, but it deliberately forgets history and subgame
structure. `ContinuationGameForm` retains one additional semantic dimension:
it indexes the same global strategy space and outcome evaluator by declared
continuation roots. It therefore forgets how subgames are represented
internally while retaining exactly enough structure for generic
Nash-on-declared-roots transfer.
Consequently:

- an outcome-distribution morphism transfers evaluation facts;
- an isomorphism, or a morphism with deviation lifting/surjectivity, can
  transfer Nash equilibrium;
- Nash-on-roots transfer additionally requires correspondence of the declared
  root predicates;
- perfect recall and augmented public-information facts must be proved before
  compilation to the semantic form forgets them.

Calling every forward transition map a game simulation would obscure these
requirements.  The API should distinguish operational maps between Arenas,
observation-preserving maps between EFGs, and strategic maps between compiled
game forms.

## Representation comparison

| Candidate | Strength | Blocking issue | Role |
|---|---|---|---|
| Existing `GameTree` | Structural induction and current Kuhn proof | No general chance, observations, history occurrences, or game-bound strategy | Finite perfect-information proof language |
| Occurrence-sensitive `GameTree` compiler | Complete-history observations, singleton decision information, perfect recall, and exact lifting of endpoint strategies | Finer strategy space is not isomorphic to the endpoint compiler when equal subtrees repeat | Perfect-information reference EFG and information-refinement test case |
| Existing Arena state model | Infinite/cyclic and compact dynamics | Endpoint states can merge histories; no chance law | Raw transition foundation |
| Measurable kernel arena and observed presentation | Dependent legal actions, explicit measurable state/action bundles, normalized Mathlib Markov transitions, terminal-aware action kernels, joint event/state Ionescu--Tulcea paths, fixed and time-varying measurable information, abstract-action realization, non-atomic player/chance profiles, terminal-payoff limits, absolute/fresh continuation, designated-root Nash, subgame-perfection-on, and complete standard-SPE semantics | Continuous time, holding-time/non-explosion theory, and automatic measurability for arbitrary uncountable model data remain outside the certified interface | General discrete-event analytic EFG execution and equilibrium layer |
| Existing `FiniteImperfectGame` plus observed compiler | Small finite-state examples, explicit coherent information actions, and verified decision-information completion into the canonical EFG layer | Duplicated dynamics remain; acyclicity and termination are not structural; unlabeled player nodes are completed as singleton information only during compilation | Compact input presentation only |
| `StochasticGameTree` plus occurrence compiler | Structurally finite player/chance syntax, normalized finite PMFs, path-sensitive pure policies, exact bounded endpoint/payoff laws in `ObservedChanceGame` | The legacy scalar evaluator has an explicit fuel-zero convention; no source behavioral Nash/SPE language exists | Compact finite stochastic input presentation |
| History-indexed observed EFG | Faithful histories, information, public states, subgames, optional normalized chance kernels, strict bounded behavioral equilibrium transfer, representation-invariant perfect recall, constructive finite perfect-recall mixed/behavioral realization, and a generic discrete event-time infinite path/terminal-payoff convergence layer | Model-specific infinite-horizon equilibrium applications, continuous time, and further compiler-specific recall proofs | Canonical EFG theorem layer |
| History-augmented FOSG | Simultaneous joint actions, normalized world transitions, private/public views, a verified finite-player sequential compiler, genuine target behavioral-profile realization, exact finite-horizon trace/payoff laws from every macro root, and behavioral Nash/Nash on caller-declared macro continuations transfer | Instantiation of the generic infinite path layer, infinite-horizon equilibrium transfer, and general perfect-recall transfer through serialization | Compact stochastic presentation |
| Strategy/outcome game form | Strong theorem transfer across languages | Forgets subgames and information structure | Canonical strategic semantic layer |
| Law-valued game form | Complete normalized outcome laws, composable realization maps, and deviation-sensitive Nash transfer | Forgets internal histories, observations, and subgames | Canonical stochastic realization layer |
| Continuation game-form family | Shared global profile, declared roots, root-dependent evaluation, generic Nash-on-declared-roots transfer | Forgets observations, recall, and internal history structure | Canonical subgame semantic layer |

The choice is therefore a pair of interoperating canonical layers, not a single
all-purpose structure: history-indexed EFG for sequential structure and a
strategy/outcome form for representation-neutral strategic results.

## Morphism and preservation plan

| Map | Must preserve | Results available |
|---|---|---|
| `Arena.Hom` | transitions along mapped states/actions | typed history maps; stopped execution when terminality and policies are preserved |
| `Arena.Simulation` | each related source step has a related target step | existence of matching finite histories; target terminality reflects to the source |
| `Arena.Bisimulation` | transitions in both directions | matching histories and terminal equivalence |
| `Arena.WeakSimulation` | each source step has a finite target history; terminality agrees at related macro states | matching finite histories with stuttering; `Progressing` excludes zero-step matches |
| `ObservedGame.Iso` | strict history/action equivalence, turns, observations, public states, information actions with a local concrete-action coherence square, terminal outcomes (ignoring arbitrary nonterminal payoff fillers), and presentation-designated roots | composable strict equivalences; pure and behavioral strategy/profile equivalences; exact stopped pure continuations; perfect recall and termination; designated-continuation Nash transfer; lawful `SubgameSystem` and `CompleteSubgameSystem` transport; subgame-perfection-on and complete standard pure SPE in both directions |
| `ObservedChanceGame.Iso` | all `ObservedGame.Iso` structure plus exact PMF pushforward at chance histories | composable strict chance equivalences; exact successor-history and behavioral-policy naturality; complete bounded continuation/payoff laws; behavioral Nash on presentation-designated continuations in both directions |
| `ObservedGame.InformationRefinement` | strict complete-history dynamics and terminal payoffs; forget fine observations, public states, and information; lift coarse indexed actions exactly; preserve presentation-designated roots | composable refinements; exact bounded and total execution; fine-to-coarse Nash-on-designated-continuations reflection; two-way transfer exactly when `StrategySurjective` is supplied |
| `ObservedChanceGame.InformationRefinement` | all structural information-refinement data plus exact chance-kernel PMF pushforward | composable refinements; exact behavioral policy, complete bounded history, and payoff-law transfer; fine-to-coarse behavioral Nash on presentation-designated continuations reflection; two-way transfer exactly under `BehavioralStrategySurjective` |
| `ContinuationGameForm.Hom` | one global strategy map, declared-root map, outcome map, and evaluator square at every root | generic target-to-source Nash-on-declared-roots reflection; forward/two-way transfer under strategy and root surjectivity; composable independently of EFG syntax |
| `ContinuationGameForm.Simulation` | one global strategy/outcome map and a relation on roots with exact evaluator and declared-root compatibility at every related pair | generic Nash-on-declared-roots reflection under source-root coverage; forward/two-way transfer under target-root coverage and strategy surjectivity; relational composition for weak/stuttering bridges; every root-reflecting `Hom` embeds as a graph simulation |
| `ContinuationGameForm.Iso` | equivalences of roots, per-player strategies, and outcomes, plus exact root/evaluator compatibility | generic two-way Nash-on-declared-roots transfer for root-dependent utilities |
| `LawGameForm.RealizesVia` | source outcome law pushed through an outcome map equals the target law | reflexive and composable exact realization, independent of concrete game syntax |
| `LawGameForm.Hom` | playerwise strategy map, outcome map, and exact law pushforward | composable realization; Nash reflection and two-way transfer under strategy surjectivity |
| `LawGameForm.Iso` | playerwise strategy and outcome equivalences with exact law pushforward | strict realization and two-way law-based Nash transfer |
| `PMF.RelCoupling` | both marginals exactly and relation support | probability-mass-preserving stochastic refinement |
| `MeasurableKernelArena.Hom` | measurable state and dependent action-bundle maps; exact measure pushforward of every transition law | composable strict analytic transition morphisms; discrete strict kernel morphisms embed exactly |
| `KernelArena.Simulation.PolicyMatch` | terminal agreement, exact coupling of nonterminal action laws, and coupling of every supported successor-kernel pair | exact stopped finite-horizon endpoint and complete-trace couplings; equality of related observable laws |
| `KernelArena.ProbabilisticWeakSimulation` | source successor law coupled to a positive-fuel target endpoint law; exact terminal agreement | progressing weak simulation of every positive-probability support path |
| `FOSG.WeakSerialization` | chance-consistent probabilistic weak simulation, private/public observations, terminal payoffs, and designated macro roots | reusable operational proof boundary for FOSG-to-observed-EFG compilers |
| `FOSG.WeakSerialization.BehavioralBridge` | playerwise strategy equivalences, genuine target payoff laws, exact source/target laws at related roots and initialization, source-root coverage | generic relational continuation simulation, initialized game-form isomorphism, and two-way finite-horizon behavioral Nash on caller-declared macro continuations transfer |
| game-form morphism | mapped outcome or utility distribution | evaluation and expected-utility equalities |
| game-form isomorphism | strategy equivalences plus outcome/utility law | Nash in both directions |

A one-way strategy map does not by itself preserve Nash equilibrium: the target
may have deviations that are absent from the source.  Every equilibrium
transport theorem must expose the required deviation-lifting hypothesis rather
than hide it under the word “simulation”.

## Theorem-driven acceptance tests

The design is accepted only when small theorem packages exercise the intended
abstractions.

### Gate A: histories and stopped play

1. In a diamond Arena, the left and right histories remain distinct even when
   their endpoint states are equal.
2. Every state of `ExtensiveGame.unfold G` is reachable from its empty history.
3. A one-step game with a terminal successor admits a profile-induced stopped
   play and returns the terminal outcome; it does not require an action at the
   terminal state.
4. A cyclic Arena has arbitrarily long finite histories without pretending to
   have a finite inductive game tree.

### Gate B: action and information identity

5. Two distinct actions leading to the same continuation remain distinct
   strategy choices.
6. A pure or behavioral strategy is constant on one information state by its
   type, not by a post-hoc equality proposition.
7. Player information equality implies the same abstract action type and the
   same public state.

### Gate C: finite perfect-information recovery

8. `GameTree.toEFG` has a game-bound strategy correspondence.
9. The correspondence preserves terminal outcome, unilateral deviation, Nash,
   and root-scoped SPE.
10. Finite well-founded perfect-information no-chance EFGs have a pure SPE
    (backward-induction Kuhn), and SPE implies Nash.
11. A finite tree-shaped no-chance Arena extraction has a round-trip
    equivalence, not only an unrelated `SPE → NE` corollary.

### Gate D: chance and FOSG

12. Every chance history has a normalized probability law and evaluation
    preserves total mass.
13. FOSG histories induce player views and public views; equality of a player
    view implies equality of the public view.
14. A bounded FOSG-to-augmented-EFG compiler preserves trajectory
    distributions, terminal outcomes, and expected utilities.
15. Perfect recall gives mixed-to-behavioral realization equivalence (the
    behavioral Kuhn theorem).

### Current prototype status

Completed and Lean-checked:

- Gate A.1–A.3: the diamond history regression, reachability in the history
  unfolding, and terminal-aware stopped execution;
- Gate B.6–B.7 for pure strategies: information-indexed choice and public
  observation equality from decision-information equality;
- Gate C.8 and the terminal-outcome portion of C.9:
  `GameTree.playerStrategyEquiv`,
  `stoppedPayoff_strategy_eq_outcome`, and
  `stoppedPayoff_playerProfile_eq_outcome`.
- The pure-Nash portion of Gate C.9:
  `GameTree.gameFormIso_isNash_iff` and
  `GameTree.observedGameForm_isNash_iff_isNashAt`.
- Operational transfer infrastructure:
  `Arena.Hom.map_stoppedHistory`, graph simulations for strict morphisms,
  bisimulations induced by strict isomorphisms, and the history-unfolding
  projection.
- Strict structural observed-EFG transfer:
  `ObservedGame.Iso.map_stoppedHistoryFrom`,
  `map_stoppedPayoffFrom`, `continuationGameFormIso`, and
  `isPureNashOnDesignatedContinuationsAtFuel_iff`. The isomorphism preserves
  private observations, public states, information/action identity, and
  presentation-designated roots.
- Termination-certified subgame-perfect transfer:
  `ObservedGame.PureTerminating`, terminal-run uniqueness,
  `ObservedGame.Iso.map_terminalPayoffFrom`,
  `mapSubgameSystem`, `mapCompleteSubgameSystem`,
  `map_pureTerminatingOn`, `isPureSubgamePerfectOn_iff`, and
  `isPureStandardSubgamePerfect_iff`.
- Full Gate C.9 recovery:
  compiled histories and `GameTree.Subtree` correspond, every compiled
  `GameTree` is pure terminating, and
  `GameTree.observed_isPureNashOnDesignatedContinuations_iff_isGlobalEndpointSubgamePerfectOn`
  identifies the endpoint compiler's designated-continuation predicate with
  the root-scoped structural endpoint-policy predicate. This is not the
  occurrence compiler's standard SPE theorem.
- Weak/stuttering operational infrastructure:
  `Arena.WeakSimulation`, `WeakSimulation.Progressing`,
  `WeakSimulation.exists_history`, and `WeakBisimulation`.
- Gate D.12:
  `ObservedChanceGame.chanceKernel` and
  `chanceSuccessorKernel_tsum` enforce normalized history chance laws, while
  `ObservedChanceGame.Iso.map_chanceSuccessorKernel` proves strict
  distributional naturality.
- Strict behavioral observed-EFG transfer:
  `ObservedGame.Iso.behavioralProfileEquiv`,
  `ObservedChanceGame.Iso.map_behavioralHistoryPolicy`,
  `map_behavioralHistoryPMFFrom`,
  `map_behavioralStoppedPayoffLawFrom`,
  `behavioralContinuationGameFormIso`,
  `behavioralContinuationIsNash_iff`, and
  `isBehavioralNashOnDesignatedContinuationsAtFuel_iff`.  These preserve the complete PMF,
  not only its support or expectation, at every corresponding continuation
  and presentation-designated root.
- Perfect-recall structural layer:
  `ObservedGame.ownDecisionHistory`,
  `HasSingletonInformation`, `HasPerfectRecall`, `PerfectRecall`,
  `RecallCertificate`, `RecallCertificate.perfectRecall`,
  `recallCertificate_nonempty_iff_perfectRecall`,
  `PerfectInformation.perfectRecall`,
  `ObservedGame.Iso.map_ownDecisionHistory`, and
  `ObservedGame.Iso.perfectRecall_iff` and
  `recallCertificate_nonempty_iff`. Recall records both prior information
  states and the player's own abstract actions. The certificate form says
  this sequence factors through current information and is preserved in both
  directions without finiteness or termination assumptions.
- Occurrence-sensitive `GameTree` reference compiler:
  `GameTree.toOccurrenceObservedGame`,
  `toOccurrenceObservedGame_perfectInformation`,
  `toOccurrenceObservedGame_perfectRecall`,
  `forgetOccurrenceInfo_infoAt`,
  `forgetOccurrenceInfoActionEquiv_at`,
  `not_injective_forgetOccurrenceInfo_of_merged_histories`, and
  `endpointInformationRefinement`,
  `toOccurrenceObservedGame_pureTerminating`,
  `stoppedPayoffFrom_liftEndpointPureProfile`, and
  `endpoint_isPureNashOnDesignatedContinuations_of_occurrence_lift`. It makes history
  occurrences observable, proves singleton information, and realizes every
  endpoint pure profile with exactly the same bounded and total play while
  retaining the strictly larger path-contingent strategy space.
- Compact finite-imperfect compiler:
  `FiniteImperfectGame.DecisionInfo`,
  `decisionInfoAt_eq_of_same_info`, `ObservedCompiler`,
  `ObservedCompiler.toObservedGame`, and
  `tinyObserved_infoAt_left_right`,
  `tinyObservedRecallCertificate`, and
  `tinyObserved_perfectRecall`. Labeled player nodes share a genuine decision
  information state, unlabeled player nodes remain singletons, legal actions
  are transported through explicit `actionEquiv`, and presentation-designated continuation roots
  are supplied explicitly. The hidden left/right histories demonstrate
  non-singleton information with perfect recall. No representative-dependent
  action relabeling is introduced.
- Generic information-refinement transfer:
  `InformationRefinement.refl`, `trans`, `map_stoppedHistoryFrom`,
  `map_stoppedPayoffFrom`, `map_terminalPayoffFrom`,
  `continuationIsNash_of_map`,
  `isPureNashOnDesignatedContinuationsAtFuel_of_map`, and
  `isPureNashOnDesignatedContinuations_of_map`. The default theorem direction reflects
  equilibrium from the finer deviation space. The
  `_iff_of_strategySurjective` variants state the exact extra condition needed
  for two-way Nash-on-declared-roots transfer.
- Behavioral/chance-aware information-refinement transfer:
  `ObservedChanceGame.InformationRefinement.refl`, `trans`,
  `map_behavioralHistoryPolicy`, `map_behavioralHistoryPMFFrom`,
  `map_behavioralStoppedPayoffLawFrom`,
  `behavioralContinuationIsNash_of_map`, and
  `isBehavioralNashOnDesignatedContinuationsAtFuel_of_map`. Chance kernels and complete
  finite-horizon `PMF`s are preserved exactly. The
  `_iff_of_strategySurjective` variants require explicit surjectivity of the
  behavioral strategy lift. `GameTree.endpointBehavioralInformationRefinement`
  instantiates this interface for the endpoint and occurrence compilers; its
  chance condition is vacuous, and its SPE theorem remains directional because
  occurrence-dependent deviations generally do not descend.
- Representation-neutral continuation-family transfer:
  `ContinuationGameForm.Hom.refl`, `trans`,
  `ContinuationGameForm.IsNashOnRoots.comap`, `ContinuationGameForm.IsNashOnRoots.map_of_surjective`,
  `Hom.isNashOnRoots_iff_of_surjective`, and
  `Iso.isNashOnRoots_iff`. `ObservedGame.pureContinuationFamily` and
  `ObservedChanceGame.behavioralContinuationFamily` recover the existing
  bounded continuation game forms at each root. Strict observed EFG
  isomorphisms and pure/behavioral information refinements compile to family
  isomorphisms or morphisms. Private route regressions derive the existing
  designated-continuation Nash transfer directions from the generic layer.
  `ContinuationGameForm.Hom.toSimulation` embeds any declared-root-reflecting
  functional map as a graph relation.
  `pureContinuationFamilySimulation` and
  `behavioralContinuationFamilySimulation` instantiate this conversion for
  information refinements; private simulation-route regressions recover
  equilibrium reflection through the same relational API used by weak
  serializers.
- Representation-neutral law and realization semantics:
  `LawGameForm`, `RealizesVia.refl`, `RealizesVia.trans`,
  `LawGameForm.Hom.refl`, `trans`, `mapProfile_realizesVia`,
  `LawGameForm.Iso`, and the law-valued Nash transfer theorems.
  `ObservedChanceGame.behavioralLawGameForm` definitionally recovers the
  existing bounded behavioral continuation `GameForm`.
  `ObservedChanceGame.Iso.behavioralLawGameFormIso` and
  `InformationRefinement.behavioralLawGameFormHom` expose strict
  isomorphism and information-refinement payoff-law preservation through the
  same representation-neutral realization relation.
- Gate D.15, constructive at every bounded continuation:
  `PMF.bind_conditionOnFiber_map_pair` and
  `PMF.fintypePi_conditionOnFiber_apply` provide exact discrete
  conditionalization; `mixedToBehavioral_stoppedHistoryLawFrom` and
  `mixedToBehavioral_stoppedPayoffLawFrom` realize arbitrary mixed plans from
  a selected root under `FiniteKuhnHypotheses`;
  `finiteKuhn_isNash_iff` transfers root Nash equilibrium; and
  `behavioralToMixedContinuationHom_outcomeDeviationCompleteAt` discharges
  every rootwise mixed deviation, yielding
  `isBehavioralNashOnDesignatedContinuationsAtFuel_iff_mixed`. The result is exact equality
  of complete bounded laws, not merely equality of expectations.
- Structural morphism hierarchy:
  `ObservedGame.Iso.toInformationRefinement` and
  `ObservedChanceGame.Iso.toInformationRefinement` embed strict structural
  isomorphisms into the refinement layer. Their pure and behavioral strategy
  maps equal the original strict maps and are surjective.
  Private hierarchy regressions verify that strict
  designated-continuation Nash transfer factors through refinement and
  generic continuation semantics.
- Relational continuation-family and FOSG Nash on caller-declared macro continuations transfer:
  `ContinuationGameForm.Simulation.refl`, `trans`,
  `ContinuationGameForm.IsNashOnRoots.comapSimulation`,
  `ContinuationGameForm.IsNashOnRoots.mapSimulation_of_surjective`, and
  `Simulation.isNashOnRoots_iff_of_total` avoid choosing a target root in a
  weak simulation.
  `FOSG.WeakSerialization.BehavioralBridge.continuationSimulation`,
  `initialGameFormIso`, and `macroNashOnDeclaredContinuations_iff` package this reasoning once for
  every finite-player serializer. The concrete
  `FOSG.Sequentialization.behavioralWeakSerializationBridge` discharges the
  interface with `serializedBehavioralMicroPayoffLawFrom_eq`, initialized
  micro payoff-law equality, and macro-root coverage;
  `behavioralMacroNashOnDeclaredContinuations_iff` is obtained from the generic theorem.
- Gate D.13:
  `FOSG.privateObservations_map_publicOf` and
  `publicObservations_eq_of_privateObservations_eq`.
- The reusable distributional core of Gate D.14:
  `PMF.RelCoupling.bind`, `PMF.RelCoupling.map_eq`,
  `KernelArena.Simulation.PolicyMatch.stateLawCoupling`,
  `traceLawCoupling`, `traceObservableLaw_eq`,
  `KernelArena.ProbabilisticWeakSimulation`,
  `toKernelSimulation`, `toSupportWeakSimulation`, and
  `toSupportWeakSimulation_progressing`; `FOSG.WeakSerialization` adds exact
  target chance consistency, observation/public-state maps, terminal payoff
  equality, and designated-root correspondence.
- A concrete bounded part of Gate D.14:
  `FOSG.Sequentialization.observedChanceGame`,
  `exists_macroExecutionLaw`, `probabilisticWeakSimulation`,
  `macroKernelSimulation`, `serializedMacroPolicy`,
  `serializedMacroPolicy_match`, `serializedMacroTraceLawCoupling`,
  `serializedBehavioralMacroPolicy`,
  `serializedBehavioralTraceLawCoupling`,
  `initialBoundaryCoupling`, `initializedStateLawCoupling`,
  `initializedPayoffLaw_eq`, `initializedUtilityLaw_eq`,
  `initializedBehavioralUtilityLaw_eq`, and
  `weakSerialization`.  For `Fin (n + 1)` players, each simultaneous joint
  action has exactly the original transition law after `n + 2` serialized
  steps; arbitrary terminal-aware history-level joint-action policies compile
  automatically and have exactly coupled stopped finite traces and equal
  initialized optional terminal-payoff and derived-utility laws. Independently randomized
  information-indexed behavioral profiles induce these source and target
  macro policies automatically. The compiler also constructs the genuine
  target observed-EFG behavioral profile, proves its local player/chance laws,
  and proves exact unilateral-deviation commutation. Its prefix-accumulating
  dependent product theorem identifies genuine micro execution with the
  canonical macro-controller mixture, first for one block and then for every
  stopped finite macro horizon. The resulting payoff-distribution
  `GameForm.Iso` gives two-way finite-horizon behavioral Nash transfer.

Still open:

- the cyclic-history regression;
- broader model-specific applications of the generic infinite-horizon
  terminal-expected-utility and measurable-kernel equilibrium layers;
- true continuous-time event kernels, non-explosion, and path regularity;
- richer imperfect-information observation/public-state compilers and further
  compiler-specific perfect-recall proofs;
- analytic-to-finite/FOSG lawful-subgame-system transfer theorems.

Joint state/action event histories, observed information-indexed analytic
policies, non-atomic player/chance laws, constructive player deviations,
path-utility designated-root Nash, subgame-perfection-on, complete standard SPE, and the
pointwise/distributional fresh-restart compatibility hierarchy are
implemented. Same-state and
same-successor/different-action regressions now guard the recorded-action
semantics.

The occurrence-sensitive `GameTree` compiler is authoritative for canonical
root-bound subgame-perfect equilibrium. The older recursive `GameTree` theorem
stack remains the structural endpoint-policy proof language. Pure Nash
transfers through `GameForm.Iso`; the observed-game layer and its stopped
evaluator provide the game-bound semantics.

## Migration rules

- Do not remove or rename the existing `GameTree` Kuhn/SPE results during the
  experiment.
- Do not add more equilibrium theorems to `FiniteImperfectGame`; add a compiler
  target first.
- Do not present the current state-indexed `BehaviorStrategy` as a general
  imperfect-information behavior strategy.  It is a Markov/state strategy.
- Do not add another independent chance tree before the common chance-law
  interface is tested.
- New solution concepts must be game-bound and root-scoped unless a genuinely
  representation-independent global definition is intended.
- New bridge theorems must state exactly what they preserve: transition,
  observation, outcome distribution, deviations, or subgames.

## Implementation sequence

1. **Completed:** typed histories, history unfolding, and terminal-aware stopped
   execution induced by a history policy.
2. **Completed:** diamond and terminal-play regression examples.
3. **Completed:** observed-EFG wrapper with all-history observations,
   decision-information states, and information-indexed actions.
4. **Completed:** no-chance `GameTree` compilation with player-strategy
   equivalence and stopped terminal-outcome correspondence.
5. **Completed:** the finite perfect-recall behavioral/mixed Kuhn realization
   is proved directly on the observed-EFG interface, and
   `Kuhn_exists_occurrencePureSPE` transports backward induction to a concrete
   root-bound occurrence-sensitive finite EFG.
6. **Completed:** deterministic `GameForm`, strategy/outcome isomorphism,
   deviation commutation, and utility-compatible pure-Nash transfer.
7. **Completed:** strict observed-EFG structural isomorphism preserving
   observations, public states, action identities, terminal payoffs, and
   presentation-designated continuation roots; exact bounded pure Nash transfer on presentation-designated continuations.
8. **Completed:** existential pure-termination certificates, total terminal
   outcomes independent of witness fuel, pure-SPE transfer on an explicit lawful
   `SubgameSystem`, complete standard-SPE transfer through
   `CompleteSubgameSystem`, and the separately named structural endpoint
   correspondence.
9. **Completed interface:** FOSG compact macro language, realized-history
   augmentation, normalized kernel transitions, and a chance-consistent
   coupling-based serialization boundary.  Its support theorem produces a
   progressing `Arena.WeakSimulation`; it does not claim a one-step strict
   isomorphism when administrative decision or chance states are inserted.
10. **Completed first compiler:** `Fin (n + 1)` simultaneous decisions compile
    to hidden sequential choices plus the original chance kernel, with exact
    initial and one-macro endpoint laws and a complete
    `FOSG.WeakSerialization`.
11. **Completed generic iteration:** relation-supported PMF couplings compose
    through bind; terminal-aware coupling-compatible randomized policies have
    exact stopped finite-horizon endpoint and complete-trace couplings; related
    observables have equal pushforward laws.
12. **Completed concrete policy iteration:** the FOSG compiler recovers the
    unique source state at a serialized macro boundary, compiles arbitrary
    history-level randomized joint-action policies to canonical positive
    executions, proves `PolicyMatch`, and derives initialized endpoint,
    trajectory, optional-terminal-payoff-law, and derived-utility-law transfer.
13. **Completed behavioral profile compilation:** `DecisionModel` behavioral
    profiles independently sample information-indexed abstract actions,
    transport them through the legal-action equivalences, and induce the
    source and serialized macro policies used by the trajectory and utility
    theorems. The same profile is realized as a genuine target observed-EFG
    behavioral profile with exact local player/chance laws, and compilation
    commutes with unilateral deviation.
14. **Completed behavioral micro/macro realization and equilibrium transfer:**
    the prefix sampler proves equality of genuine target micro execution and
    the verified macro controller for one block and every stopped finite
    horizon, including initialization. Source and target optional
    terminal-payoff PMFs therefore define isomorphic finite-horizon behavioral
    game forms, so
    behavioral Nash transfers in both directions.
15. **Completed generic strict behavioral transfer:** strict
    `ObservedChanceGame.Iso` maps information-indexed behavioral profiles by
    exact PMF pushforward, commutes with genuine stochastic history policies,
    preserves complete bounded continuation and optional-terminal-payoff laws,
    and transfers behavioral Nash on presentation-designated continuations in both
    directions at corresponding presentation-designated roots.
16. **Completed structural perfect recall:** personal decision histories
    record every player's earlier information states and own abstract actions;
    singleton information implies perfect recall, and strict observed-EFG
    isomorphisms preserve and reflect recall.
17. **Completed first compiler-specific recall proof:** the
    occurrence-sensitive `GameTree` compiler has singleton information and
    therefore perfect recall. It forgets to the endpoint/`NodeInfo` compiler,
    and endpoint pure profiles lift with exact bounded operational semantics;
    no strict isomorphism is asserted across the changed information
    partition.
18. **Completed reusable information refinement:** strict history dynamics
    combine with forgetful observation/public/information maps and dependent
    action lifting. Refinements have identity and composition, exact bounded
    and termination-certified execution, default fine-to-coarse Nash
    reflection on presentation-designated continuations, and two-way transfer
    under explicit `StrategySurjective`.
    The endpoint-to-occurrence `GameTree` compiler is the first concrete
    instance.
19. **Completed behavioral information refinement:** normalized local player
    laws and chance kernels commute exactly with information refinement;
    complete bounded history/payoff laws and behavioral Nash on presentation-designated continuations reflect from
    fine to coarse, with two-way transfer under
    `BehavioralStrategySurjective`.
20. **Completed representation-neutral continuation semantics:** one shared
    complete strategy space is evaluated at every declared root;
    root/strategy/outcome morphisms compose and provide generic
    Nash-on-declared-roots reflection, while strategy and root surjectivity
    give forward and two-way transfer. Bounded pure and behavioral observed-EFG
    isomorphisms and refinements instantiate this layer.
21. **Completed relational weak-serialization rootwise-Nash semantics:**
    continuation simulations relate roots without selecting representatives,
    compose relationally, and transfer Nash-on-declared-roots under explicit
    root coverage and strategy lifting. `WeakSerialization.BehavioralBridge`
    turns exact behavioral laws at related roots and initialization into this
    transfer generically. The finite-player FOSG serializer instantiates the
    bridge, has exact payoff-law equality from every related macro root, and
    preserves initialized plus caller-declared macro-root finite-horizon Nash
    in both directions.
22. **Completed morphism-hierarchy closure:** strict observed-EFG
    isomorphisms embed as automatically strategy-surjective information
    refinements. Root-reflecting continuation morphisms embed as graph
    simulations, so strict maps, information refinements, and relational weak
    serializers share one composable semantic simulation layer.
23. **Completed compact finite-imperfect compiler:** raw labels are completed
    into player-indexed shared or singleton decision information; explicitly
    declared abstract action types transport exactly to concrete actions; compiler certificates
    supply presentation-designated continuation roots; and the tiny hidden-choice example verifies
    that equal labels force one abstract choice. The compiler makes no
    arbitrary representative-state action choice.
24. **Completed compiler-facing recall certificates:** remembered personal
    decisions factor through current information states. Certificate existence
    is equivalent to `PerfectRecall`, transfers through strict observed-EFG
    isomorphisms, and is instantiated by the finite-imperfect tiny compiler,
    whose non-singleton hidden information state has perfect recall.
25. **Completed law-valued realization semantics:** `LawGameForm` makes
    normalized outcome laws primitive; `RealizesVia`, law morphisms, and law
    isomorphisms compose; their deterministic view reuses generic Nash
    transfer. Bounded observed chance-EFG behavioral semantics instantiate the
    layer, with strict isomorphisms and information refinements producing
    uniform realization witnesses.
26. **Completed finite behavioral/mixed Kuhn realization:** mixed contingent
    plans have exact bounded laws; discrete conditionalization plus perfect
    recall constructs root-scoped behavioral realizations, proves semantic
    deviation coverage, and yields two-way bounded Nash equivalence on
    presentation-designated continuations.
27. **Completed generic discrete event-time infinite semantics:** construct the
    terminal-absorbing path probability measure, identify every bounded PMF
    marginal, and prove stopping-time, payoff, expectation, unfinished-mass,
    weak-law, and uniform-deviation limit Nash-on-declared-roots theorems.
    The generic limit layer makes no standard-SPE claim. Broader
    model-specific applications and true continuous time remain open.
28. **Completed analytic one-step transition boundary:** add a genuine
    Markov-kernel arena on measurable dependent state/action bundles, embed
    the discrete PMF arena and strict morphisms exactly, and prove by a
    non-atomic unit-interval reverse regression that the extension is not
    cosmetic.
29. **Completed terminal-aware analytic one-step execution:** add killed legal
    action kernels, prove the terminal-absorbing state-step kernel is Markov,
    recover the discrete policy step exactly without a carrier-countability
    assumption, and preserve the non-atomic reverse regression after
    execution.
30. **Completed finite analytic endpoint iteration:** prove finite endpoint
    kernels are Markov, establish successor and additive
    Chapman--Kolmogorov laws, recover every discrete stopped state PMF
    exactly, test a concrete active/terminal arena, and preserve the
    non-atomic reverse regression at every positive horizon.
31. **Completed analytic discrete-event state-path semantics:** apply
    Ionescu--Tulcea to the stopped measurable step kernel, prove probability
    normalization and exact endpoint-coordinate marginals, recover every
    embedded discrete stopped state law, prove terminal starts are constant
    almost surely under measurable singletons, and rule out PMF
    representation of the continuous path law by coordinate pushforward.
32. **Completed finite-state-history-dependent analytic policies:** permit
    time-indexed measurable legal-action kernels on complete finite state
    prefixes, prove normalized Ionescu--Tulcea execution and the correct
    prefix-dependent coordinate recursion, embed stationary `ActionPolicy`
    with exact step and whole-path equality, and guard strict interface gain
    with same-latest-state reachable prefixes.
33. **Completed joint state/action event histories:** record the selected
    dependent action in each noninitial event, admit complete event-prefix
    policies, recover the state path exactly, and separate policies that
    cannot be represented from state histories alone.
34. **Completed observed measurable-kernel presentations:** add
    time-indexed event information, abstract-action realization, explicit
    measurable history presentations, non-atomic player/chance kernels, and
    constructive jointly measurable player-profile/deviation assembly.
35. **Completed analytic outcomes and equilibrium:** add measurable and
    bounded path utility, finite and almost-sure terminal-payoff bridges,
    canonical absolute-prefix continuation, positive-atom conditioning, and
    constructive designated-root Nash, subgame-perfection-on, and complete standard SPE with strict
    off-path regressions.
36. **Completed qualified fresh-restart comparison:** normalize only the
    retained root action marker, characterize equality through finite
    marginals, derive path/equilibrium transfer from distributional and
    rooted one-step certificates, and expose reusable action-kernel
    factorization plus genuinely time-varying information rebasing.
37. Further work should target the still-open items above without weakening
    the separation between absolute-prefix continuation, fresh-clock restart,
    and regular conditioning. True continuous time remains a separate future
    layer.

## Sources and related implementations

- Vojtěch Kovařík, Martin Schmid, Neil Burch, Michael Bowling, and Viliam Lisý,
  “Rethinking Formal Models of Partially Observable Multiagent Decision
  Making,” especially the FOSG unrolling and augmented-EFG correspondence:
  <https://arxiv.org/abs/1906.11110>.
- Elazar Gershuni, `elazarg/GameTheory`, especially
  `GameTheory/Core/{GameForm,KernelGame,GameMorphism,GameSimulation,GameIsomorphism}.lean`,
  `GameTheory/Languages/EFG/Augmented.lean`, and
  `GameTheory/Languages/Bridges/FOSG/AugmentedEFG.lean`, audited at commit
  `bf8c735a84a9356108ccd16bc4f09ffc632cc1a9`:
  <https://github.com/elazarg/GameTheory/tree/bf8c735a84a9356108ccd16bc4f09ffc632cc1a9>.
- Maschler, Solan, and Zamir, *Game Theory*, Chapters 3 and 7, for finite
  extensive games, subgames, behavioral strategies, and perfect recall.
