# EFG Module Status

This is the source-based lifecycle register for the extensive-form-game
implementation.  It covers every Lean module below
`EconCSLib/GameTheory/ExtensiveGame/`, every module in the representation-neutral
`GameForm` family, and the directly supporting executable `FiniteLaw`,
effective coded-event probability, exact finite Markov-chain, rational
interval-event, and legacy-internal `PMF`
probability families.
The governance checker compares this register with the current complete source
tree. It contains 214 modules, including 40 modules below
`ExtensiveGame/Simulation/`; both totals are machine-checked.

The status describes the role of the module that owns a declaration, not every
declaration made name-resolvable by transitive imports:

- **Canonical** owns the preferred reusable semantics or is a governed
  pre-stability facade. Canonical means recommended and machine-checked; it
  does not currently promise external source compatibility.
- **Frontend** is a supported input or algorithm representation that should
  compile or relate to the canonical layer before acquiring general theory.
- **Historical** is mathematically valid but has different or superseded
  semantics. It is retained and build-checked, but is closed to parallel
  general theory.
- **Compatibility** is reserved for an explicitly temporary import wrapper.
  There are currently no such modules: the pre-release compatibility paths
  were removed after their internal consumers were migrated.
- **Experimental** is opt-in theory whose public contract is not settled.
- **Internal** is proof or compiler implementation reached through a facade;
  its path and helpers are not individually frozen.

The Canonical/Frontend API growth freeze is global and overrides every
row-level `May grow` entry below. Those cells describe the declaration's
responsibility boundary if the policy is reopened; they are not current
permission to add public declarations. Internal implementation and
Experimental prototypes may continue to evolve without promotion into the
frozen surface.
The 2026-09-04 A19 decision adds only the declaration-free Canonical
`Effective` and `Effective.Analytic` aggregate paths; their seven implementation
and semantic leaves remain Internal, and the public declaration ceiling is
unchanged.

| Status | Modules |
|---|---:|
| Canonical | 83 |
| Frontend | 13 |
| Historical | 7 |
| Compatibility | 0 |
| Experimental | 0 |
| Internal | 111 |
| **Total** | **214** |

Recommended-import abbreviations used below are:

| Abbreviation | Full import |
|---|---|
| `GF` | `EconCSLib.GameTheory.GameForm` |
| `FiniteLaw` | `EconCSLib.Math.Probability.FiniteLaw` |
| `Structural` | `EconCSLib.GameTheory.ExtensiveGame.Interface.StructuralCore` |
| `Core` | `EconCSLib.GameTheory.ExtensiveGame.Interface.Core` |
| `Finite` | `EconCSLib.GameTheory.ExtensiveGame.Interface.Execution.Finite` |
| `Infinite` | `EconCSLib.GameTheory.ExtensiveGame.Interface.Execution.Infinite` |
| `Analytic` | `EconCSLib.GameTheory.ExtensiveGame.Interface.Execution.Analytic` |
| `Relations` | `EconCSLib.GameTheory.ExtensiveGame.Interface.Relations.Discrete` |
| `Preserve` | `EconCSLib.GameTheory.ExtensiveGame.Interface.Preservation` |
| `EqD` | `EconCSLib.GameTheory.ExtensiveGame.Interface.Equilibrium.Discrete` |
| `EqA` | `EconCSLib.GameTheory.ExtensiveGame.Interface.Equilibrium.Analytic` |
| `Restart` | `EconCSLib.GameTheory.ExtensiveGame.Interface.Restart` |
| `Compile` | `EconCSLib.GameTheory.ExtensiveGame.Interface.Compilation.Discrete` |

Removal-policy codes keep the register readable during pre-stability:

- `C`: a canonical path may hard-migrate when mathematical and dependency
  evidence justifies it; update internal consumers, facade regressions,
  lifecycle rows, audits, and migration notes in the same change.
- `F`: a frontend may hard-migrate under the same synchronization rule, while
  preserving or honestly restating its representation-specific semantics.
- `H`: a historical path may be removed after a real-consumer audit and an
  honest migration note; never invent a false semantic replacement.
- `W`: a temporary compatibility wrapper is removed after internal consumers
  are zero and the replacement has been documented.
- `I`: internal paths may be reorganized behind their governed facade; add a
  wrapper only for an identified downstream consumer, not a hypothetical one.

If EFG source compatibility is announced later, this table must adopt an explicit
deprecation, migration-window, and major-release policy at that time. None is
currently promised.

## Arena, execution, frontends, and compilers

| Module | Status | Responsibility | Recommended import | Replacement | May grow | Action | Removal policy |
|---|---|---|---|---|---|---|---|
| `EconCSLib.GameTheory.ExtensiveGame.Structural.Basic` | Canonical | Minimal payoff-free `Arena` and `ControlledGame` carriers | `Structural` | — | Yes, structural carriers only | Keep | C |
| `EconCSLib.GameTheory.ExtensiveGame.Structural.Reachability` | Canonical | Finite Arena reachability and controlled-game initial reachability | `Structural` | — | Yes, reachability only | Keep | C |
| `EconCSLib.GameTheory.ExtensiveGame.Structural.History` | Canonical | Typed finite histories and payoff-free Arena/controlled-game unfolding | `Structural` | — | Yes, history only | Keep | C |
| `EconCSLib.GameTheory.ExtensiveGame.Basic` | Internal | State-payoff `ExtensiveGame` compatibility carrier over `Structural.Basic` | explicit payoff-aware module | `Structural.Basic` for payoff-free code | Adapter declarations only | Keep | I |
| `EconCSLib.GameTheory.ExtensiveGame.Execution.Reachability` | Internal | `ExtensiveGame.IsReachable` payoff-aware adapter over structural reachability | explicit payoff-aware module | `Structural.Reachability` for payoff-free code | Adapter declarations only | Keep | I |
| `EconCSLib.GameTheory.ExtensiveGame.Execution.History` | Internal | `ExtensiveGame.unfold` payoff-aware adapter over structural histories | explicit payoff-aware module | `Structural.History` for payoff-free code | Adapter declarations only | Keep | I |
| `EconCSLib.GameTheory.ExtensiveGame.Execution.CompletePlay` | Canonical | Measure-free history-rooted legal complete plays and terminal absorption | `Core` | — | Yes, structural play only | Keep | C |
| `EconCSLib.GameTheory.ExtensiveGame.Execution.Length` | Canonical | Uniform length and `Acc`-based structural well-foundedness certificates | `Core` | — | Yes, structural termination only | Keep | C |
| `EconCSLib.GameTheory.ExtensiveGame.Execution.Objective` | Canonical | History-sensitive terminal and complete-path outcomes | `Interface.Objective` | — | Yes, objective only | Keep | C |
| `EconCSLib.GameTheory.ExtensiveGame.Winning.Basic` | Canonical | Complete-play winning conditions, prefix decisions, and robust pure winning strategies | `Interface.Objective` | — | Yes, winning-objective semantics only | Keep | C |
| `EconCSLib.GameTheory.ExtensiveGame.Winning.Topology` | Canonical | Complete-play agreement cylinders, prefix topology, and measurable prefix objectives | `Interface.Objective` | — | Yes, topological objective boundary only | Keep | C |
| `EconCSLib.GameTheory.ExtensiveGame.Execution.StoppedExecution` | Canonical | Terminal-aware deterministic bounded execution | `Core` | — | Yes, execution only | Keep | C |
| `EconCSLib.GameTheory.ExtensiveGame.Execution.StochasticExecution` | Canonical | Terminal-aware bounded PMF execution | `Finite` | — | Yes, PMF execution | Keep | C |
| `EconCSLib.GameTheory.ExtensiveGame.Execution.FinitePayoff` | Internal | Exact rational finite-horizon expectations and stopped payoffs on complete histories and state/event prefixes | `Finite` | facade | Yes, finite payoff only | Keep | I |
| `EconCSLib.GameTheory.ExtensiveGame.Execution.FiniteCompletePath` | Internal | On-demand terminal-absorbing complete paths from bounded exact history laws and explicit positive-support termination certificates | `Finite` | facade | Yes, bounded complete-path construction only | Keep | I |
| `EconCSLib.GameTheory.ExtensiveGame.Execution.Truncation` | Internal | Exact stopped-payoff centers, unfinished-mass radii, budgeted search, and proof-guarded least-horizon search | `Finite` | facade | Yes, finite truncation computation only | Keep | I |
| `EconCSLib.GameTheory.ExtensiveGame.Relations.Discrete.StochasticNaturality` | Canonical | Exact PMF history-execution naturality under strict arena isomorphisms | `Relations.Discrete` | — | Yes, relation-side execution naturality only | Keep | C |
| `EconCSLib.GameTheory.ExtensiveGame.Execution.InfiniteTrajectory` | Canonical | Executable `FiniteLaw` path marginals, exact bounded observables, partial terminal search, and projections of supplied infinite/terminal laws | `Infinite` | — | Yes, discrete paths | Keep | C |
| `EconCSLib.GameTheory.ExtensiveGame.Observed.InfiniteExecution` | Canonical | Observed behavioral indexing and finite-marginal certificates for supplied infinite execution | `Infinite` | — | Yes, adapter only | Keep | C |
| `EconCSLib.GameTheory.ExtensiveGame.GameTree` | Frontend | Finite no-chance inductive tree syntax | explicit module or `EconCSLib` | compile with `GameTreeOccurrenceObserved` for canonical EFG semantics | Yes, structural algorithms | Keep | F |
| `EconCSLib.GameTheory.ExtensiveGame.BackwardInduction` | Frontend | Computable structural backward-induction values | explicit module or `EconCSLib` | occurrence compiler for game-bound standard SPE | Yes, tree algorithms | Keep | F |
| `EconCSLib.GameTheory.ExtensiveGame.StochasticGameTree` | Frontend | Finite stochastic occurrence-sensitive tree syntax | `Compile` | `StochasticGameTree.toObservedChanceGame` | Yes, tree-local algorithms | Keep | F |
| `EconCSLib.GameTheory.ExtensiveGame.ImperfectInformation` | Frontend | Compact finite-state information-labeled syntax | `Compile` | `FiniteImperfectGame.ObservedCompiler` | Yes, input structure only | Keep | F |
| `EconCSLib.GameTheory.ExtensiveGame.FiniteArenaExtraction` | Frontend | Assumption-explicit Arena-to-tree extraction relation | explicit module | canonical Arena/observed layer when extraction is unnecessary | Yes, extraction only | Keep | F |
| `EconCSLib.GameTheory.ExtensiveGame.Zermelo` | Frontend | Chance-free finite two-player zero-sum tree theorem | explicit module or `EconCSLib` | canonical EFG only for representation-neutral extensions | Yes, specialized algorithm theory | Keep | F |
| `EconCSLib.GameTheory.ExtensiveGame.ZeroSumGameTreeWithChance` | Frontend | Exact rational binary chance-tree value and saddle algorithms | explicit module or `EconCSLib` | no equivalent replacement; compiler required before general EFG transfer | Yes, exact rational algorithms | Keep | F |
| `EconCSLib.GameTheory.ExtensiveGame.Compiler.FiniteImperfectObserved` | Frontend | Compact imperfect-information to observed/chance EFG compilation | `Compile` | target is `ObservedGame`/`ObservedChanceGame` | Yes, preservation only | Keep | F |
| `EconCSLib.GameTheory.ExtensiveGame.Compiler.StochasticGameTreeObserved` | Frontend | Stochastic-tree to occurrence-sensitive observed-chance compilation | `Compile` | target is `ObservedChanceGame` | Yes, preservation only | Keep | F |
| `EconCSLib.GameTheory.ExtensiveGame.Compiler.GameTreeOccurrenceObserved` | Frontend | Canonical root-bound occurrence-sensitive tree compiler and pure standard SPE | `Compile` | target is `ObservedGame` | Yes, compiler preservation | Keep | F |
| `EconCSLib.GameTheory.ExtensiveGame.Compiler.GameTreeObserved` | Historical | Endpoint-observed compiler preserving old endpoint policies | `Compile` | `GameTreeOccurrenceObserved` for occurrence-sensitive semantics | Bugfix/preservation only | Keep | H |
| `EconCSLib.GameTheory.ExtensiveGame.GameTreeSPE` | Historical | Global structural endpoint-policy optimality | explicit module | occurrence compiler for standard EFG SPE; not definitionally equivalent | Bugfix only | Keep | H |
| `EconCSLib.GameTheory.ExtensiveGame.GameTreeNE` | Historical | Root Nash and endpoint-policy restriction theorems | explicit module | canonical observed continuation Nash for new general theory | Bugfix only | Keep | H |
| `EconCSLib.GameTheory.ExtensiveGame.GameTreeStrategicForm` | Historical | Endpoint-plan strategic-form extraction | explicit module | occurrence observed-game pure profiles for occurrence plans | Bugfix only | Keep | H |
| `EconCSLib.GameTheory.ExtensiveGame.Strategy` | Historical | State-indexed Arena strategies without observed information | explicit module | `ObservedGame.PureStrategy`; semantics differ | Bugfix only | Documentation only | H |
| `EconCSLib.GameTheory.ExtensiveGame.Subgame` | Historical | State re-rooting and reachable-state restriction | explicit module | `ObservedGame.SubgameSystem` for lawful subgames; semantics differ | Bugfix only | Documentation only | H |

## FOSG frontend

| Module | Status | Responsibility | Recommended import | Replacement | May grow | Action | Removal policy |
|---|---|---|---|---|---|---|---|
| `EconCSLib.GameTheory.ExtensiveGame.FOSG.FOSG` | Frontend | Compact simultaneous stochastic game and weak-serialization contract | `Compile` | compile/serialize to observed chance EFG | Yes, frontend only | Keep | F |
| `EconCSLib.GameTheory.ExtensiveGame.FOSG.FOSGBehavioralSerialization` | Frontend | Reusable strategic bridge for weak serializers | `Compile` | canonical continuation simulation is its target | Yes, preservation only | Keep | F |
| `EconCSLib.GameTheory.ExtensiveGame.FOSG.FOSGContinuation` | Frontend | Macro-root continuation and Nash transfer | `Compile` | canonical declared-root continuation semantics | Yes, FOSG transfer only | Keep | F |
| `EconCSLib.GameTheory.ExtensiveGame.FOSG.Sequentialization.Core` | Internal | Serialized micro-state/game construction | `Compile` | facade | Yes, implementation | Keep | I |
| `EconCSLib.GameTheory.ExtensiveGame.FOSG.Sequentialization.Policy` | Internal | Source and target policy compilation | `Compile` | facade | Yes, implementation | Keep | I |
| `EconCSLib.GameTheory.ExtensiveGame.FOSG.Sequentialization.MacroLaw` | Internal | Exact one-macro-step law | `Compile` | facade | Yes, implementation | Keep | I |
| `EconCSLib.GameTheory.ExtensiveGame.FOSG.Sequentialization.Trajectory` | Internal | Iterated micro/macro trace law | `Compile` | facade | Yes, implementation | Keep | I |
| `EconCSLib.GameTheory.ExtensiveGame.FOSG.Sequentialization.Witness` | Internal | Weak-serialization certificate assembly | `Compile` | facade | Yes, implementation | Keep | I |
| `EconCSLib.GameTheory.ExtensiveGame.FOSG.Sequentialization.Equilibrium` | Internal | Finite-horizon Nash transfer from the witness | `Compile` | facade | Yes, implementation | Keep | I |

## Canonical observed EFG

The complete `Observed.Controlled` hierarchy is governed by the role taxonomy
in [`efg-controlled-api.md`](efg-controlled-api.md). `Controlled.Infrastructure`
and `Controlled.Morphism` are canonical declaration-free aggregate facades;
payoff-aware projection code is isolated under `Controlled.Compat` rather than
forming alternative canonical owners.

| Module | Status | Responsibility | Recommended import | Replacement | May grow | Action | Removal policy |
|---|---|---|---|---|---|---|---|
| `EconCSLib.GameTheory.ExtensiveGame.Observed.Game` | Canonical | State-payoff observed-game information, two-way payoff attachment/erasure, bijective player/payoff reindexing, external root presentations, and compatibility names for controlled lawful systems | `Finite` | `Controlled`/`Controlled.Infrastructure.Subgame` for payoff-free clients | Yes, payoff-aware structure and adapters | Keep | C |
| `EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled` | Canonical | Observation-free decision core, optional private/public observation extension, represented strategy coordinates, bijective player relabeling, pure-profile reindexing, and external root presentations | `Core` | — | Yes, objective-free information only | Keep | C |
| `EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Infrastructure` | Canonical | Declaration-free aggregate facade for controlled execution, well-formedness, subgame, finite, quasistrategy, recall, and winning infrastructure | narrowest defining `Controlled.Infrastructure.*` leaf | responsibility leaves | No declarations | Aggregate facade | C |
| `EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Infrastructure.Core` | Canonical | Reachable no-chance mover helpers, pure-profile history execution, and player-strategy play compatibility | `Core` | — | Yes, execution helpers only | Keep | C |
| `EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Infrastructure.WellFormed` | Canonical | Optional full raw-information representation and mover-normalization predicates plus reachable-execution compatibility bundles | `Core` | — | Yes, general well-formedness only; no finite/payoff/probability/recall/termination fields | Keep | C |
| `EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Infrastructure.Subgame` | Canonical | Occurrence-sensitive continuations, lawful/complete subgame systems, and bijective player-relabel transport | `Core` | — | Yes, subgame structure only | Keep | C |
| `EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Infrastructure.Finite` | Canonical | Uniform history-length, finite reachable-action/represented-information, and finite-EFG certificate package | `Core` | — | Yes, finite certificates only | Keep | C |
| `EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Infrastructure.Quasi` | Canonical | Objective-free quasistrategy permissions, refinement, and play compatibility | `Core` | — | Yes, quasistrategy structure only | Keep | C |
| `EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Infrastructure.Recall` | Canonical | Personal decisions, own-decision histories, classic recall, event-clock signal/public recall, optional silent-event trace builders, no-absent-mindedness, and recall certificates | `Core` | — | Yes, recall only | Keep | C |
| `EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Compat.Infrastructure` | Internal | `ObservedGame` projection and legacy recall/quasistrategy compatibility lemmas | downstream compatibility modules | payoff-free declarations in `Controlled.Infrastructure` | Adapter declarations only | Keep | I |
| `EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Morphism` | Canonical | Declaration-free aggregate facade for payoff-free structural, lawful-subgame, recall, and objective-semantics morphism leaves | `Relations` or the narrowest `Controlled.Morphism.*` leaf | responsibility leaves | No declarations | Aggregate facade | C |
| `EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Morphism.Core` | Canonical | Payoff-free Hom, information refinement, strict Iso, carrier/history/action/strategy maps, root-presentation comparison, inverse, and Iso algebra | `Relations` | — | Yes, structural morphisms only | Keep | C |
| `EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Morphism.Subgame` | Canonical | Strict-Iso preservation of occurrence-sensitive continuation, lawful roots, and selected/complete subgame systems | `Relations` | — | Yes, subgame transport only | Keep | C |
| `EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Morphism.Recall` | Canonical | Strict-Iso preservation of personal decisions, own-decision histories, event-clock signal histories, and classic/event-clock private/public recall | `Relations` | — | Yes, recall transport only | Keep | C |
| `EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Morphism.Objective` | Canonical | Pure execution and terminal-objective transport under strict Iso and directional information refinement, each with an explicit objective-compatibility square | `EqD` | — | Yes, operational objective transport only | Keep | C |
| `EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Compat.Morphism` | Internal | Payoff-aware strict-isomorphism commuting square and legacy-Iso projection | `Relations` | `ControlledObservedGame.Iso` plus an external payoff square | Adapter declarations only | Keep | I |
| `EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Law.Discrete` | Canonical | Payoff-free discrete chance kernels, raw `BoundedHistoryLawFamily`, and normalized/legal/absorbing/executor-consistent `CertifiedBehavioralExecutionLaw` | `Finite` | — | Yes, finite discrete laws only | Keep | C |
| `EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Compat.DiscreteLaw` | Internal | Forget-payoff adapter from `ObservedChanceGame` to discrete controlled chance | `Finite` | `DiscreteControlledObservedChanceGame` | Adapter declarations only | Keep | I |
| `EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Law` | Canonical | Per-root lawful complete-path marginals, measurable interpretations, honest history-transform/terminal-history laws, execution-coherence certificates, realizations, and strict-Iso bridges | `Preserve`; add `Analytic` for analytic execution | — | Yes, representation-independent law semantics only; no implicit common causal process | Keep | C |
| `EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Law.DiscretePath` | Canonical | Supplied discrete behavioral complete-path laws with exact executable `FiniteLaw` marginal and legality certificates | `Infinite` | — | Yes, discrete constructor only | Keep | C |
| `EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Law.Analytic` | Canonical | Measurable-kernel adapter to the common lawful complete-path probability carrier | `Analytic` | — | Yes, analytic adapter only | Keep | C |
| `EconCSLib.GameTheory.ExtensiveGame.Observed.WellFormed` | Canonical | Full information representation, decision coherence, and structural finite-EFG certificates | `Core` | — | Yes, hypothesis packages only | Keep | C |
| `EconCSLib.GameTheory.ExtensiveGame.Observed.FiniteUnfolding` | Canonical | Finite occurrence-sensitive reachable-history extraction with strict structural, root/subgame, recall, chance, strategy/update, and bounded-history-law preservation | `Finite` | — | Yes, extraction/preservation only | Keep | C |
| `EconCSLib.GameTheory.ExtensiveGame.Observed.SignalRecall` | Internal | Payoff-aware `ObservedGame` projections of event-clock signal/public recall and recall certificates | downstream payoff-aware modules | `Controlled.Infrastructure.Recall` | Adapter declarations only | Keep | I |
| `EconCSLib.GameTheory.ExtensiveGame.Observed.SemanticMode` | Canonical | Lightweight strategy/chance semantic classification tags | `Relations` | — | Yes, classification only | Keep | C |
| `EconCSLib.GameTheory.ExtensiveGame.Observed.Quasi` | Internal | Legacy `ObservedGame` quasistrategy names projected from the payoff-free implementation | downstream legacy modules | `Controlled.Infrastructure` | Adapter declarations only | Keep | I |
| `EconCSLib.GameTheory.ExtensiveGame.Observed.Chance` | Canonical | Normalized chance kernels and chance isomorphisms | `Finite` | — | Yes, chance semantics | Keep | C |
| `EconCSLib.GameTheory.ExtensiveGame.Observed.Behavior` | Canonical | Information-indexed behavioral profiles and history policies | `Finite` | — | Yes, finite execution | Keep | C |
| `EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Semantics` | Canonical | Concrete pure terminal/path-objective continuation and SPE plus payoff-free evaluator-relative continuation transfer | explicit module or `EqD` | — | Yes; operational names only for canonical pure execution, arbitrary evaluators remain explicitly relative | Keep | C |
| `EconCSLib.GameTheory.ExtensiveGame.Observed.Semantics` | Canonical | State-payoff `ObservedGame` adapter for controlled evaluator-relative continuation semantics | `EqD` | `Controlled.Semantics` for payoff-free clients | Adapter declarations only | Keep | C |
| `EconCSLib.GameTheory.ExtensiveGame.Observed.SPE` | Canonical | Total pure execution, lawful-root and standard SPE | `EqD` | — | Yes, canonical equilibrium | Keep | C |
| `EconCSLib.GameTheory.ExtensiveGame.Observed.PerfectRecall` | Internal | Legacy `ObservedGame` classic-recall names and strict-Iso adapters projected from payoff-free theory | downstream legacy modules | `Controlled.Infrastructure`/`Controlled.Morphism` | Adapter declarations only | Keep | I |
| `EconCSLib.GameTheory.ExtensiveGame.Observed.Mixed` | Canonical | Mixed complete plans and bounded mixed execution | `EqD` | — | Yes, mixed semantics | Keep | C |
| `EconCSLib.GameTheory.ExtensiveGame.Observed.General` | Canonical | Finite rational laws over behavioral plans | `EqD` | — | Yes, carrier and lawful realization only | Keep | C |
| `EconCSLib.GameTheory.ExtensiveGame.Observed.LawEquivalence` | Canonical | Bounded complete-history-law realizations and terminal/payoff pushforwards | `EqD` | — | Yes, discrete semantic relations | Keep | C |
| `EconCSLib.GameTheory.ExtensiveGame.Winning.Determinacy` | Canonical | Logical determinacy predicates, imperfect-information boundary, finite determinacy, and well-founded perfect-information two-player zero-sum determinacy with explicit finite action and terminal-winner data | `Interface.Winning` | — | Yes, assumption-explicit determinacy only | Keep | C |
| `EconCSLib.GameTheory.ExtensiveGame.Winning.BasicCompat` | Internal | Legacy payoff-aware winning-strategy compatibility layer | `Interface.Winning` | payoff-free declarations in `Winning.Basic` | Adapter declarations only | Keep | I |
| `EconCSLib.GameTheory.ExtensiveGame.Winning.DeterminacyCompat` | Internal | Legacy `ObservedGame` determinacy packages and well-formedness bridges | `Interface.Winning` | payoff-free declarations in `Winning.Determinacy` | Adapter declarations only | Keep | I |
| `EconCSLib.GameTheory.ExtensiveGame.Winning.Chance` | Canonical | Almost-sure winning under discrete infinite history laws | `Interface.Winning.Stochastic` | — | Yes, stochastic winning only | Keep | C |
| `EconCSLib.GameTheory.ExtensiveGame.Observed.Realization` | Canonical | Law-valued behavioral realization adapters | `EqD` | — | Yes, realization only | Keep | C |
| `EconCSLib.GameTheory.ExtensiveGame.Observed.Continuation` | Canonical | Pure/behavioral compilation to continuation forms | `EqD` | — | Yes, adapter only | Keep | C |
| `EconCSLib.GameTheory.ExtensiveGame.Observed.Kuhn` | Canonical | Finite hypotheses and behavioral-to-mixed realization | `EqD` | — | Yes, finite Kuhn only | Keep | C |
| `EconCSLib.GameTheory.ExtensiveGame.Observed.StrategyBridge` | Canonical | Uniform public navigation across strategy modes | `EqD` | — | Yes, navigation only | Keep | C |
| `EconCSLib.GameTheory.ExtensiveGame.Observed.BehaviorMorphism` | Canonical | Strict behavioral transport and Nash equivalence | `EqD` | — | Yes, strict transfer | Keep | C |
| `EconCSLib.GameTheory.ExtensiveGame.Observed.MorphismHierarchy` | Canonical | Relation hierarchy and agreement regressions | `EqD` | — | Yes, hierarchy only | Keep | C |
| `EconCSLib.GameTheory.ExtensiveGame.Observed.Morphism.Structural` | Canonical | Strict observed-EFG isomorphism structure | `Relations` | — | Yes, structural relation | Keep | C |
| `EconCSLib.GameTheory.ExtensiveGame.Observed.Morphism.Inverse` | Internal | Inverse structural transport proofs | `Relations` | facade | Yes, proof helpers | Keep | I |
| `EconCSLib.GameTheory.ExtensiveGame.Observed.Morphism.Operational` | Canonical | Exact finite execution transport | `Relations` | — | Yes, transfer only | Keep | C |
| `EconCSLib.GameTheory.ExtensiveGame.Observed.Morphism.Continuation` | Canonical | Total continuation and lawful-system transport | `EqD` | — | Yes, transfer only | Keep | C |
| `EconCSLib.GameTheory.ExtensiveGame.Observed.Refinement.Structural` | Canonical | Information-refinement structure and maps | `Relations` | — | Yes, structural relation | Keep | C |
| `EconCSLib.GameTheory.ExtensiveGame.Observed.Refinement.Core` | Canonical | Pure bounded execution and directional Nash transfer | `EqD` | — | Yes, transfer only | Keep | C |
| `EconCSLib.GameTheory.ExtensiveGame.Observed.Refinement.Termination` | Canonical | Termination-certified refinement transfer | `EqD` | — | Yes, transfer only | Keep | C |
| `EconCSLib.GameTheory.ExtensiveGame.Observed.BehaviorRefinement.Structural` | Canonical | Chance-aware refinement and strategy lifting | `Relations` | — | Yes, structural relation | Keep | C |
| `EconCSLib.GameTheory.ExtensiveGame.Observed.BehaviorRefinement.Execution` | Canonical | Behavioral execution and directional Nash transfer | `EqD` | — | Yes, transfer only | Keep | C |
| `EconCSLib.GameTheory.ExtensiveGame.Relations.Preservation` | Canonical | Formal preservation-matrix certificate aliases, coupling interfaces, and compiler-specific strict/weak packages | `Preserve` | — | Yes, relation vocabulary and packages only | Keep | C |
| `EconCSLib.GameTheory.ExtensiveGame.Observed.DeferredSampling.Core` | Internal | Fresh information keys and finite table laws | `EqD` | facade | Yes, proof implementation | Keep | I |
| `EconCSLib.GameTheory.ExtensiveGame.Observed.DeferredSampling.Execution` | Internal | Fresh-query execution equivalence | `EqD` | facade | Yes, proof implementation | Keep | I |
| `EconCSLib.GameTheory.ExtensiveGame.Observed.DeferredSampling.Realization` | Internal | Deferred behavioral/mixed continuation transfer | `EqD` | facade | Yes, proof implementation | Keep | I |
| `EconCSLib.GameTheory.ExtensiveGame.Observed.KuhnConditioning.Posterior` | Internal | Posterior conditioning of complete plans | `EqD` | facade | Yes, proof implementation | Keep | I |
| `EconCSLib.GameTheory.ExtensiveGame.Observed.KuhnConditioning.Core` | Internal | Posterior products and recall identities | `EqD` | facade | Yes, proof implementation | Keep | I |
| `EconCSLib.GameTheory.ExtensiveGame.Observed.KuhnConditioning.Execution` | Internal | Sequential posterior execution equality | `EqD` | facade | Yes, proof implementation | Keep | I |
| `EconCSLib.GameTheory.ExtensiveGame.Observed.KuhnConditioning.Realization` | Internal | Root-scoped mixed-to-behavioral law transfer | `EqD` | facade | Yes, proof implementation | Keep | I |
| `EconCSLib.GameTheory.ExtensiveGame.Observed.FinitePureNash` | Internal | Executable finite-horizon Nash checking over the original root-bound pure strategy and unilateral-deviation spaces | `EqD` | facade | Yes, bounded pure Nash checking only | Keep | I |
| `EconCSLib.GameTheory.ExtensiveGame.Observed.FiniteMeasureStrategy` | Internal | Executable finite joint pure-profile laws and exact marginal, outcome, and complete-path pushforwards | `EqD` | facade | Yes, finite profile laws only | Keep | I |

## Public interfaces

| Module | Status | Responsibility | Recommended import | Replacement | May grow | Action | Removal policy |
|---|---|---|---|---|---|---|---|
| `EconCSLib.GameTheory.ExtensiveGame.Interface.StructuralCore` | Canonical | Exact five-module structural facade for Arena, reachability, typed histories, complete plays, and payoff-free observed control | `Structural` | — | Yes, structural closure only | Keep | C |
| `EconCSLib.GameTheory.ExtensiveGame.Interface.Core` | Canonical | Governed pre-stability Foundation Facade for typed histories, finite/subgame/recall certificates, and bounded deterministic/PMF execution | `Core` | — | Yes, foundation families only | Keep | C |
| `EconCSLib.GameTheory.ExtensiveGame.Interface.Objective` | Canonical | Governed pre-stability measure-free outcome, winning-condition, and quasistrategy facade | `Interface.Objective` | — | Yes, no probability/equilibrium | Keep | C |
| `EconCSLib.GameTheory.ExtensiveGame.Interface.Winning` | Canonical | Governed pre-stability logical winning-strategy and determinacy facade | `Interface.Winning` | — | Yes, no stochastic/analytic winning | Keep | C |
| `EconCSLib.GameTheory.ExtensiveGame.Interface.Winning.Stochastic` | Canonical | Governed pre-stability discrete infinite almost-sure-winning facade | `Interface.Winning.Stochastic` | — | Yes, no non-atomic analytic arena | Keep | C |
| `EconCSLib.GameTheory.ExtensiveGame.Interface.Execution.Finite` | Canonical | Governed pre-stability measure-free deterministic/PMF execution facade | `Finite` | — | Yes, finite execution only | Keep | C |
| `EconCSLib.GameTheory.ExtensiveGame.Interface.Execution.Infinite` | Canonical | Governed pre-stability measure-valued discrete-path facade | `Infinite` | — | Yes, infinite discrete only | Keep | C |
| `EconCSLib.GameTheory.ExtensiveGame.Interface.Execution.Analytic` | Canonical | Governed pre-stability non-atomic measurable-kernel execution facade | `Analytic` | — | Yes, execution/presentation only | Keep | C |
| `EconCSLib.GameTheory.ExtensiveGame.Interface.Relations.Discrete` | Canonical | Governed pre-stability structural/PMF relation facade | `Relations` | — | Yes, relation only | Keep | C |
| `EconCSLib.GameTheory.ExtensiveGame.Interface.Preservation` | Canonical | Governed pre-stability facade for strict/refinement/weak relation strengths, bounded/path-law realizations, couplings, and compiler preservation packages | `Preserve` | — | Yes, preservation contracts only | Keep | C |
| `EconCSLib.GameTheory.ExtensiveGame.Interface.Equilibrium.Discrete` | Canonical | Governed pre-stability pure/behavioral/mixed/general finite equilibrium facade | `EqD` | — | Yes, discrete equilibrium only | Keep | C |
| `EconCSLib.GameTheory.ExtensiveGame.Interface.Equilibrium.Analytic` | Canonical | Governed pre-stability measurable outcome and continuation-equilibrium facade | `EqA` | — | Yes, no restart/compiler | Keep | C |
| `EconCSLib.GameTheory.ExtensiveGame.Interface.Restart` | Canonical | Governed pre-stability fresh-restart compatibility facade | `Restart` | — | Yes, canonical routes only | Keep | C |
| `EconCSLib.GameTheory.ExtensiveGame.Interface.Compilation.Discrete` | Canonical | Governed pre-stability finite compiler and FOSG serialization facade | `Compile` | — | Yes, compilers only | Keep | C |

## Simulation implementation

The logical responsibility and physical-move decision for every module in
this section are recorded in the Simulation matrix in
[`efg-governance.md`](efg-governance.md).  None is a separately promised
public import path.

| Module | Status | Responsibility | Recommended import | Replacement | May grow | Action | Removal policy |
|---|---|---|---|---|---|---|---|
| `EconCSLib.GameTheory.ExtensiveGame.Simulation.Kernel.DiscreteBridge` | Internal | Exact discrete-path/analytic-path coherence | `Analytic` | facade | Yes, bridge only | Keep | I |
| `EconCSLib.GameTheory.ExtensiveGame.Simulation.Kernel.Arena` | Internal | Non-atomic analytic arena and discrete embedding | `Analytic` | facade | Yes, analytic core | Keep | I |
| `EconCSLib.GameTheory.ExtensiveGame.Simulation.Kernel.Execution` | Internal | Legal terminal-aware analytic one-step policy | `Analytic` | facade | Yes, execution only | Keep | I |
| `EconCSLib.GameTheory.ExtensiveGame.Simulation.Kernel.Endpoint` | Internal | Supplied analytic endpoint kernels with exact iteration certificates | `Analytic` | facade | Yes, execution only | Keep | I |
| `EconCSLib.GameTheory.ExtensiveGame.Simulation.Kernel.StatePath` | Internal | Supplied infinite state law and exact prefix/coordinate marginals | `Analytic` | facade | Yes, execution only | Keep | I |
| `EconCSLib.GameTheory.ExtensiveGame.Simulation.Kernel.HistoryPath` | Internal | Prefix-dependent state-history policy execution | `Analytic` | facade | Yes, execution only | Keep | I |
| `EconCSLib.GameTheory.ExtensiveGame.Simulation.Kernel.EventPath` | Internal | Joint state/action event-path execution | `Analytic` | facade | Yes, execution only | Keep | I |
| `EconCSLib.GameTheory.ExtensiveGame.Simulation.Kernel.FiniteExecution` | Internal | Semantic compatibility for executable one-step, arbitrary finite-prefix, and state/event coordinate laws under local analytic realization | `Analytic` | facade | Yes, semantic compatibility only | Keep | I |
| `EconCSLib.GameTheory.ExtensiveGame.Simulation.Kernel.EffectivePathLaw` | Internal | Analytic finite-marginal semantics for coherent executable state/event path-law queries, including direct tail-event and tail-state prefix bridges | `Analytic` | facade | Yes, semantic compatibility only | Keep | I |
| `EconCSLib.GameTheory.ExtensiveGame.Simulation.Kernel.CertifiedPathApproximation` | Internal | State-path semantic certificates identifying exact prefix centers and deriving true interval/search error bounds from pointwise uniform approximation | `Analytic` | facade | Yes, semantic compatibility only | Keep | I |
| `EconCSLib.GameTheory.ExtensiveGame.Simulation.Kernel.FiniteRealizedInformation` | Internal | Exact analytic correspondence for finite abstract-action selection and prefix-dependent finite realization | `Analytic` | facade | Yes, semantic compatibility only | Keep | I |
| `EconCSLib.GameTheory.ExtensiveGame.Simulation.Kernel.FiniteCompleteEventPath` | Internal | Analytic prefix and coordinate semantics for bounded terminal-absorbing complete event-path laws | `Analytic` | facade | Yes, semantic compatibility only | Keep | I |
| `EconCSLib.GameTheory.ExtensiveGame.Simulation.Kernel.ObservedEvent` | Internal | Fixed information-indexed event policies | `Analytic` | facade | Yes, presentation only | Keep | I |
| `EconCSLib.GameTheory.ExtensiveGame.Simulation.Kernel.RealizedInformation` | Internal | Abstract action realization for observed event policies | `Analytic` | facade | Yes, presentation only | Keep | I |
| `EconCSLib.GameTheory.ExtensiveGame.Simulation.Continuation.Path` | Internal | Absolute-prefix analytic continuation paths | `EqA` | facade | Yes, continuation only | Keep | I |
| `EconCSLib.GameTheory.ExtensiveGame.Simulation.Continuation.Conditioning` | Internal | Constructive continuation-kernel finite marginals and raw positive-prefix conditional-law bridge | `EqA` | facade | Yes, conditioning only | Keep | I |
| `EconCSLib.GameTheory.ExtensiveGame.Simulation.Continuation.FiniteConditioning` | Internal | Semantic compatibility for exact finite-posterior continuation, analytic partial trajectories, and absolute-path marginals | `EqA` | facade | Yes, semantic compatibility only | Keep | I |
| `EconCSLib.GameTheory.ExtensiveGame.Simulation.Presentation.Chance.KernelBridge` | Internal | Complete-history observed PMF-to-kernel bridge | `Analytic` | facade | Yes, bridge only | Keep | I |
| `EconCSLib.GameTheory.ExtensiveGame.Simulation.Presentation.Chance.Realized` | Internal | Explicit observed-chance realization certificate | `Analytic` | facade | Yes, presentation only | Keep | I |
| `EconCSLib.GameTheory.ExtensiveGame.Simulation.Presentation.Chance.Countable` | Internal | Effective countable information/action selectors; supplied analytic boundary | `Analytic` | facade | Yes, presentation only | Keep | I |
| `EconCSLib.GameTheory.ExtensiveGame.Simulation.Presentation.Chance.MeasurableHistory` | Internal | Explicit measurable complete-history model | `Analytic` | facade | Yes, presentation only | Keep | I |
| `EconCSLib.GameTheory.ExtensiveGame.Simulation.Presentation.Chance.Measurable` | Internal | Explicit uncountable observed-chance presentation | `Analytic` | facade | Yes, presentation only | Keep | I |
| `EconCSLib.GameTheory.ExtensiveGame.Simulation.Presentation.Chance.FiniteExecution` | Internal | Semantic compatibility for direct observed-chance action laws, bounded event prefixes, and complete finite state-prefix marginals | `Analytic` | facade | Yes, finite/analytic bridge only | Keep | I |
| `EconCSLib.GameTheory.ExtensiveGame.Simulation.Presentation.Chance.ProfileAssembly` | Internal | Compatibility seam from PMF profiles to measurable assembly | `Analytic` | facade | Yes, adapter only | Keep | I |
| `EconCSLib.GameTheory.ExtensiveGame.Simulation.Presentation.Kernel.Core` | Internal | Non-atomic observed kernel-valued strategy presentation | `Analytic` | facade | Yes, presentation only | Keep | I |
| `EconCSLib.GameTheory.ExtensiveGame.Simulation.Presentation.Kernel.ProfileAssembly` | Internal | Measurable player profiles with executable role decisions and deviations | `Analytic` | facade | Yes, assembly only | Keep | I |
| `EconCSLib.GameTheory.ExtensiveGame.Simulation.Presentation.Kernel.EffectiveBehavioralProfile` | Internal | Weighted-Dirac realization of effective kernel profiles, compiled-policy equality, and exact finite event/state-prefix analytic marginals | `Analytic` | facade | Yes, semantic compatibility only | Keep | I |
| `EconCSLib.GameTheory.ExtensiveGame.Simulation.Equilibrium.FinitePayoff` | Internal | Semantic compatibility for exact rational Arena history and KernelArena state/event prefix payoffs, unfinished mass, and truncation bounds | `EqA` | facade | Yes, semantic compatibility only | Keep | I |
| `EconCSLib.GameTheory.ExtensiveGame.Simulation.Equilibrium.EffectivePathUtility` | Internal | Effective simple-observable expectation certificates for the existing analytic path-utility integral | `EqA` | facade | Yes, effective/analytic representation certificates only | Keep | I |
| `EconCSLib.GameTheory.ExtensiveGame.Simulation.Equilibrium.Outcome` | Internal | Path utilities, Nash, termination, and payoff convergence | `EqA` | facade | Yes, outcome/equilibrium | Keep | I |
| `EconCSLib.GameTheory.ExtensiveGame.Simulation.Continuation.Observed` | Internal | Absolute/fresh continuation outcomes and equilibrium | `EqA` | facade | Yes, continuation/equilibrium | Keep | I |
| `EconCSLib.GameTheory.ExtensiveGame.Simulation.Continuation.ObservedConditioning` | Internal | Supplied positive-prefix conditional laws and expectations | `EqA` | facade | Yes, conditioning only | Keep | I |
| `EconCSLib.GameTheory.ExtensiveGame.Simulation.Restart.Core` | Internal | Root-event normalization and finite splicing | `Restart` | facade | Yes, restart proof | Keep | I |
| `EconCSLib.GameTheory.ExtensiveGame.Simulation.Restart.Trajectory` | Internal | Spliced trajectory and finite-prefix laws | `Restart` | facade | Yes, restart proof | Keep | I |
| `EconCSLib.GameTheory.ExtensiveGame.Simulation.Restart.Certificates` | Internal | Raw step/action/path restart certificates | `Restart` | facade | Yes, restart proof | Keep | I |
| `EconCSLib.GameTheory.ExtensiveGame.Simulation.Restart.FiniteExecution` | Internal | Semantic compatibility for fresh-clock, absolute-clock, and spliced executable restart prefixes at every horizon | `Restart` | facade | Yes, semantic compatibility only | Keep | I |
| `EconCSLib.GameTheory.ExtensiveGame.Simulation.Restart.Observed` | Internal | Observed-profile restart compatibility and effective-profile finite marginals for continuation event/state, fresh-restart state, and normalized continuation event laws | `Restart` | facade | Yes, restart proof | Keep | I |
| `EconCSLib.GameTheory.ExtensiveGame.Simulation.Restart.Assembly` | Internal | Baseline-and-deviation compatibility assembly | `Restart` | facade | Yes, restart proof | Keep | I |
| `EconCSLib.GameTheory.ExtensiveGame.Simulation.Restart.Equilibrium` | Internal | Canonical restart/continuation equilibrium transfer | `Restart` | facade | Yes, canonical route only | Keep | I |
| `EconCSLib.GameTheory.ExtensiveGame.Simulation.Restart.Factorization` | Internal | Statistic and information-rebase certificate constructors | `Restart` | facade | Yes, constructors only | Keep | I |

## Discrete execution and relation implementations

These internal modules were moved out of the historical `Simulation/`
directory on 2026-07-30. Their namespaces and public facade declarations did
not change; only non-promised implementation import paths changed.

| Module | Status | Responsibility | Recommended import | Replacement | May grow | Action | Removal policy |
|---|---|---|---|---|---|---|---|
| `EconCSLib.GameTheory.ExtensiveGame.Execution.Discrete.KernelArena` | Internal | Discrete stochastic arena and policy kernel | `Finite`/`Relations` | facade | Yes, discrete kernel only | Keep | I |
| `EconCSLib.GameTheory.ExtensiveGame.Execution.Discrete.KernelTrajectory` | Internal | Discrete policy execution, traces, and coupling transfer | `Finite`/`Relations` | facade | Yes, PMF execution/relations | Keep | I |
| `EconCSLib.GameTheory.ExtensiveGame.Execution.Discrete.HistoryKernel` | Internal | Executable state/event history policies, terminal-aware action results, and absolute-clock finite-prefix laws | `Finite` | facade | Yes, finite execution only | Keep | I |
| `EconCSLib.GameTheory.ExtensiveGame.Execution.Discrete.FiniteObservation` | Internal | Exact coordinate, tail, arbitrary-horizon, fresh-clock restart, and absolute prefix-splicing laws for state/event histories | `Finite` | facade | Yes, finite observation and restart computation only | Keep | I |
| `EconCSLib.GameTheory.ExtensiveGame.Execution.Discrete.EffectivePathLaw` | Internal | Coherent all-horizon state/event prefix-law queries, exact coordinate laws, and Boolean cylinder masses | `Finite` | facade | Yes, effective finite-marginal path queries only | Keep | I |
| `EconCSLib.GameTheory.ExtensiveGame.Execution.Discrete.EffectivePathUtility` | Internal | Exact rational prefix expectations and horizon-invariance for cylinder observables on coherent state/event path-law queries | `Finite` | facade | Yes, exact effective prefix utilities only | Keep | I |
| `EconCSLib.GameTheory.ExtensiveGame.Execution.Discrete.CertifiedPathApproximation` | Internal | Exact rational centers, declared approximation radii, scheme intervals, and least-horizon searches over coherent state/event prefix laws | `Finite` | facade | Yes, effective prefix approximation schemes only | Keep | I |
| `EconCSLib.GameTheory.ExtensiveGame.Execution.Discrete.DiscountedPathUtility` | Internal | Exact first-H discounted state/event rewards, geometric tail radii, vanishing proofs, and least positive-tolerance horizons | `Finite` | facade | Yes, effective discounted path utilities only | Keep | I |
| `EconCSLib.GameTheory.ExtensiveGame.Execution.Discrete.FiniteCompleteEventPath` | Internal | Finite laws of on-demand terminal-absorbing complete event and state paths from bounded execution and positive-support termination certificates | `Finite` | facade | Yes, bounded complete path construction only | Keep | I |
| `EconCSLib.GameTheory.ExtensiveGame.Execution.Discrete.RealizedInformation` | Internal | Executable finite abstract-action selection, prefix-dependent realization, and compilation to event-history policies | `Finite` | facade | Yes, finite realization compilation only | Keep | I |
| `EconCSLib.GameTheory.ExtensiveGame.Execution.Discrete.EffectiveKernelBehavioralProfile` | Internal | Effective kernel presentation and behavioral profile assembly with finite abstract/realization laws, fixed chance laws, terminal decisions, and coherent prefix execution | `Finite` | facade | Yes, effective kernel-profile execution only | Keep | I |
| `EconCSLib.GameTheory.ExtensiveGame.Execution.Discrete.ConditionalContinuation` | Internal | Exact positive-fiber conditioning and continuation on complete Arena histories and state/event prefixes, with explicit zero-mass failure | `Finite` | facade | Yes, finite conditional continuation only | Keep | I |
| `EconCSLib.GameTheory.ExtensiveGame.Execution.Discrete.ContinuationTruncation` | Internal | Exact continuation stopped centers, unfinished masses, error radii, and horizon searches from absolute state/event prefixes | `Finite` | facade | Yes, finite continuation truncation only | Keep | I |
| `EconCSLib.GameTheory.ExtensiveGame.Execution.Discrete.ObservedChance` | Internal | Direct finite event-history execution from original observed behavioral and chance laws with explicit terminal decisions | `Finite` | facade | Yes, finite observed-chance execution only | Keep | I |
| `EconCSLib.GameTheory.ExtensiveGame.Relations.Discrete.KernelWeakSimulation` | Internal | Positive-fuel weak/stuttering kernel simulation | `Relations` | facade | Yes, relation only | Keep | I |
| `EconCSLib.GameTheory.ExtensiveGame.Relations.Discrete.Morphism` | Internal | Arena homomorphism, simulation, bisimulation, and weak simulation | `Relations` | facade | Yes, structural relation | Keep | I |

## Executable probability and legacy PMF internals

| Module | Status | Responsibility | Recommended import | Replacement | May grow | Action | Removal policy |
|---|---|---|---|---|---|---|---|
| `EconCSLib.Math.Probability.Effective` | Canonical | Governed measure-free aggregate for effective coded-event probability queries | `Effective` | — | Yes, aggregate imports only | Keep | C |
| `EconCSLib.Math.Probability.Effective.Analytic` | Canonical | Opt-in aggregate for measure, kernel, and integral correctness of effective probability queries | `Effective.Analytic` | — | Yes, aggregate imports only | Keep | C |
| `EconCSLib.Math.Probability.Effective.Enclosure` | Internal | Exact rational enclosures and arbitrary-positive-tolerance query oracles | `Effective` | facade | Yes, executable approximation arithmetic only | Keep | I |
| `EconCSLib.Math.Probability.Effective.Core` | Internal | Coded events, finite rational simple observables, effective laws, pushforwards, bind, and kernel composition | `Effective` | facade | Yes, executable effective-probability operations only | Keep | I |
| `EconCSLib.Math.Probability.Effective.Semantics` | Internal | Proof-only representation relations for effective event, observable, law, map, and kernel operations | `Effective.Analytic` | facade | Yes, analytic interpretation only | Keep | I |
| `EconCSLib.Math.Probability.Effective.Uniform` | Internal | Exact non-atomic unit-interval backend for finite rational interval-union event codes | `Effective` | facade | Yes, concrete executable backend only | Keep | I |
| `EconCSLib.Math.Probability.Effective.UniformSemantics` | Internal | Volume and constant-kernel correctness for the unit-interval effective backend | `Effective.Analytic` | facade | Yes, analytic interpretation only | Keep | I |
| `EconCSLib.Math.Probability.FiniteLaw` | Canonical | Governed aggregate for executable exact finite laws | `FiniteLaw` | — | Yes, aggregate imports only | Keep | C |
| `EconCSLib.Math.Probability.FiniteLaw.Core` | Internal | Sparse rational laws, composition, mass, and expectation | `FiniteLaw` | facade | Yes, executable probability only | Keep | I |
| `EconCSLib.Math.Probability.FiniteLaw.Measure` | Internal | Analytic measure and integral theorems for exact finite laws, with no measure-producing data definition | focused module | — | Yes, analytic interpretation only | Keep | I |
| `EconCSLib.Math.Probability.FiniteLaw.Product` | Internal | Ordered finite dependent products | `FiniteLaw` | facade | Yes, executable probability only | Keep | I |
| `EconCSLib.Math.Probability.FiniteLaw.Conditioning` | Internal | Partial exact conditioning on Boolean events | `FiniteLaw` | facade | Yes, executable probability only | Keep | I |
| `EconCSLib.Math.Probability.PMF.Equiv` | Internal | Legacy PMF pushforward equivalences | focused module | `FiniteLaw` migration | No, migration only | Migrate/delete | I |
| `EconCSLib.Math.Probability.PMF.FiniteProduct` | Internal | Legacy dependent independent products | focused module | `FiniteLaw.Product` | No, migration only | Migrate/delete | I |
| `EconCSLib.Math.Probability.FiniteLaw.Coupling` | Internal | Constructive relation-supported exact finite-law couplings | `FiniteLaw` | facade | Yes, executable probability only | Keep | I |
| `EconCSLib.Math.Probability.PMF.ToMeasure` | Internal | PMF/Giry bridge for analytic consumers | focused module | analytic boundary | No, migration only | Migrate/delete | I |
| `EconCSLib.Math.Probability.PMF.ConditionalSampling` | Internal | Legacy discrete fiber conditioning | focused module | `FiniteLaw.Conditioning` | No, migration only | Migrate/delete | I |
| `EconCSLib.Math.Probability.PMF.ConditionalProduct` | Internal | Legacy conditional finite products | focused module | finite-law conditioning | No, migration only | Migrate/delete | I |
| `EconCSLib.Math.Probability.FiniteLaw.DeferredSampling` | Internal | Constructive fresh-query deferred-sampling theorem | `FiniteLaw` | facade | Yes, executable probability only | Keep | I |
| `EconCSLib.Math.Probability.FiniteMarkovChain` | Internal | Exact finite absorbing-chain execution, full-domain absorption checking, and rational Bellman solving with explicit failure | focused module | — | Yes, exact finite-chain algorithms only | Keep | I |
| `EconCSLib.Math.Probability.FiniteMarkovChain.Semantics` | Internal | Analytic correctness of the exact chain checker and solver via the original first-hit law, reward integral, and duration integral | focused module | — | Yes, finite-chain analytic interpretation only | Keep | I |
| `EconCSLib.Math.Probability.FiniteMarkovChain.Reachability` | Internal | Exact rational reach, terminal, nontermination, zero-on-nonhit reward, and late-hit computations without a global absorption premise | focused module | — | Yes, exact finite-chain reachability algorithms only | Keep | I |
| `EconCSLib.Math.Probability.FiniteMarkovChain.ReachabilitySemantics` | Internal | Bellman, normalization, finite outcome-law, and finite-horizon remainder correctness for the general reachability solver | focused module | — | Yes, finite-chain correctness only | Keep | I |
| `EconCSLib.Math.Probability.FiniteMarkovChain.Discounted` | Internal | Exact rational preterminal transient-reward Bellman solving, finite unrolling, uniqueness, and geometric remainder bounds without an absorption premise | focused module | — | Yes, exact finite-chain discounted algorithms only | Keep | I |
| `EconCSLib.Math.Probability.FiniteMarkovChain.Automaton` | Internal | Exact product with finite deterministic terminal-time monitors, accepted-terminal probability, and explicit nontermination mass | focused module | — | Yes, finite terminal-time monitor algorithms only | Keep | I |
| `EconCSLib.Math.Probability.FiniteMarkovChain.Parity` | Internal | Automatic positive-support reachability, SCC/bottom classification, and exact accepting/rejecting terminal probabilities in the two-terminal min-parity reduction | focused module | — | Yes, finite-chain reduction algorithms only; original-path ω-event semantics remains separate | Keep | I |
| `EconCSLib.Math.Probability.RationalIntervalUnion` | Internal | Pure exact inclusion-exclusion evaluator for finite rational interval-union descriptions | focused module | — | Yes, executable rational event language only | Keep | I |
| `EconCSLib.Math.Probability.RationalIntervalUnion.Volume` | Internal | Set and unit-interval volume semantics of the rational event evaluator, including probability bounds | focused module | — | Yes, interval-event analytic interpretation only | Keep | I |

## Representation-neutral game forms

| Module | Status | Responsibility | Recommended import | Replacement | May grow | Action | Removal policy |
|---|---|---|---|---|---|---|---|
| `EconCSLib.GameTheory.GameForm` | Canonical | Governed aggregate for representation-neutral semantics | `GF` | — | Yes, aggregate imports only | Keep | C |
| `EconCSLib.GameTheory.GameForm.Basic` | Canonical | Deterministic game forms, morphisms, and Nash transfer | `GF` | — | Yes, representation-neutral | Keep | C |
| `EconCSLib.GameTheory.GameForm.Law` | Canonical | Law-valued game forms and exact realization | `GF` | — | Yes, representation-neutral | Keep | C |
| `EconCSLib.GameTheory.GameForm.Continuation.Core` | Canonical | Continuation forms and functional transfer | `GF` | — | Yes, representation-neutral | Keep | C |
| `EconCSLib.GameTheory.GameForm.Continuation.Simulation` | Canonical | Relational-root continuation simulation | `GF` | — | Yes, representation-neutral | Keep | C |
| `EconCSLib.GameTheory.GameForm.Continuation.Iso` | Canonical | Invertible continuation semantics | `GF` | — | Yes, representation-neutral | Keep | C |
| `EconCSLib.GameTheory.GameForm.IndexedContinuation` | Canonical | Arbitrary-index continuation adapter | `GF` | — | Yes, representation-neutral | Keep | C |
| `EconCSLib.GameTheory.GameForm.LimitSPE` | Historical | Uniform-limit Nash on caller-declared roots under a legacy path name | `GF` | `IndexedContinuationGameForm` plus the explicit convergence theorem; not standard SPE by itself | Bugfix only | Documentation only | H |

## Register invariants

1. A compatibility row contains imports and documentation only.
2. A historical row may receive correctness fixes and migration documentation,
   but no new parallel general Nash/SPE/continuation theory.
3. An internal row may move only when the move reduces a measured dependency
   or navigation cost; an old path remains a wrapper when removal would break a
   known client.
4. No registered direct probability-support module imports EFG or game-theory
   modules.
5. Examples and open-problem modules are not part of this register and must not
   enter the library root aggregate.
