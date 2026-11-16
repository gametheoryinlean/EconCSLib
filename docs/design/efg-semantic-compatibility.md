# Two-track EFG representation and semantic compatibility

This note is the architecture contract between executable EFG algorithms and
the library's general analytic semantics. Lean declarations remain
authoritative for individual definitions and equalities. The governance
checker enforces the dependency direction and the registered bridge modules.

The analytic declarations in this contract are not called legacy. They retain
a wider mathematical domain: arbitrary measurable kernels, non-atomic laws,
infinite path measures, conditional distributions, and real integrals. An
executable definition is preferred when its effective input contract applies;
the analytic declaration remains the semantic interpretation outside that
contract.

Two requirements have equal force:

1. **Generality is preserved.** General carriers, arbitrary measurable kernels,
   infinite paths, and analytic theorems keep their original domains and
   conclusions. No finite representation is inserted into the universal EFG
   records.
2. **Effective instances use algorithms.** When a particular model supplies
   executable decisions and effective laws, operational consumers compute from
   those data and use compatibility theorems to recover the general semantics.

“Algorithm-first” therefore describes operational routing for an effective
instance. It does not make a finite representation the only library model and
does not narrow a theorem stated for arbitrary analytic inputs.

## Two-track representation policy

The library uses one shared structural EFG theory and two probability/execution
representations:

```text
                     shared structural EFG
                    /                     \
                   v                       v
        executable representation     analytic representation
 FiniteLaw / EffectiveLaw / Rat        Measure / Kernel / integral
                   \                       /
                    +-- compatibility ---+
```

- **Executable track.** Used whenever the intended model has an effective
  representation and the operation can be implemented without changing its
  meaning. This is the preferred operational API.
- **Analytic track.** Used for genuinely general objects that have no faithful
  executable representation at the required scope, including arbitrary
  kernels without an effective event/observable presentation, supplied
  infinite-path laws, general conditioning, and arbitrary integration.
- **Compatibility bridge.** Proves equality, a certified error bound, or an
  accurately scoped almost-everywhere relation between the two tracks.

This is not two copies of the entire EFG library. Histories, information,
strategies, objectives, deviations, and representation-neutral theorem
statements remain shared wherever their definitions do not depend on the law
representation. Only probability generation, path execution, numerical
evaluation, and their representation-specific proofs split into two tracks.

### Route selection

| Mathematical situation | Library route |
|---|---|
| Exact effective representation exists | executable definition is the operational API; add an exact semantic theorem when needed |
| Requested result has an effective approximation with a certified modulus | executable approximation plus error theorem; retain the exact analytic target |
| Only finite observations are effective | expose finite-prefix or cylinder queries; retain the full infinite analytic object |
| No faithful effective representation is available | analytic definition only; do not manufacture an algorithm from supplied answers |

When both tracks exist, effective consumers migrate to the executable track.
Analytic consumers remain on the analytic track, and the wider analytic
definition remains current rather than being labeled legacy.

## Primary representation rule

EconCSLib is an algorithmic game-theory library. Whenever the mathematical
input has an effective representation and the requested result is computable,
the executable object is the primary operational representation for that
instance:

- finite probability is represented by `FiniteLaw`, not first by `Measure`;
- non-atomic probability with a selected event language is represented by
  `EffectiveLaw`/`EffectiveKernel` and rational enclosure oracles;
- finite execution is represented by recursive `map`/`bind`, not by first
  constructing an infinite trajectory and projecting it;
- finite expectations are represented by exact sums, not by defining an
  integral-valued numerical function;
- finite conditioning is represented by an explicit partial algorithm, not by
  selecting a regular conditional distribution;
- finite equilibrium questions are represented by enumerators and checkers
  when the strategy domain is explicitly finite.

The analytic object is constructed or referenced only to state general
mathematics or to interpret the computed result. A proof that an algorithm has
the intended analytic meaning belongs to the compatibility layer; it does not
move ownership of the computed value into that layer.

There is no requirement that every inhabitant of a general `Measure`, `Kernel`,
or function space admit an executable realization. Such a requirement would
change the mathematical domain. Effective realization is an additional local
capability of some instances, not a field of the general EFG carrier.

## Three-layer contract

```text
effective input
     |
     v
executable algorithm --------------------+
  FiniteLaw / Rat / Bool / Option         |
     |                                    | compatibility theorem
     v                                    v
explicit interpretation ------------ analytic semantics
  finite Dirac measure, integral,         Measure / Kernel / path law
  coordinate map, or path marginal
```

1. **Executable layer.** Definitions consume finite or otherwise effective
   data and return executable values. Proofs may certify the result, but a
   caller never supplies the result being computed.
2. **Analytic semantic layer.** General `Measure`, `Kernel`, infinite-path,
   conditioning, and integral definitions state the mathematical meaning at
   their natural level of generality.
3. **Semantic compatibility layer.** Theorems identify the interpretation of
   an executable result with the existing analytic definition, or state a
   precisely delimited approximation or almost-everywhere relation when exact
   equality is mathematically unavailable.

The compatibility layer is a logical layer, not one broad import aggregate.
Its files stay beside the analytic subject they connect so execution,
equilibrium, continuation, and restart remain separate dependency branches.

## Rules

### Executable ownership

- Numerical or decision-producing definitions belong below `Execution/`, the
  relevant finite frontend, or reusable `Math/Probability/` code.
- Exact finite probability uses `FiniteLaw`; exact finite payoffs use rational
  arithmetic where the input contract is rational.
- Termination, equality, event membership, and finite enumeration must be
  supplied by executable data or local decidability assumptions. A
  measurability proof is not a decision procedure.
- An algorithm returns explicit failure such as `Option.none` when its
  effective contract does not determine a result, for example conditioning on
  a zero-mass finite event.
- When an exact executable representation exists, new effective consumers use
  it directly. They must not compute a finite answer by constructing an
  analytic path measure and then applying `Measure.map`, `integral`, or
  `condDistrib`.

### Analytic ownership

- General analytic definitions retain their original names and mathematical
  statements. They are not deprecated merely because a finite algorithm now
  covers a subdomain.
- `noncomputable` records the implementation boundary of the analytic object;
  it is not a lifecycle label and is not evidence that every special case is
  mathematically noncomputable.
- A general definition remains an active semantic reference whenever it
  accepts inputs that the executable representation cannot encode.

### Compatibility evidence

- Exact replacement requires a theorem of the form
  `interpret (compute input) = analytic input`, with every representation and
  measurability assumption visible in the theorem.
- The theorem must be derived from local realization of primitive steps. It
  must not accept the target path law, marginal equality, integral value, or
  desired result as an input certificate.
- History-dependent execution retains the complete prefix, dependent action
  occurrence, terminal convention, and clock. State projection happens only
  after action-recording execution when later behavior can depend on actions.
- Absolute continuation and time-zero restart remain different algorithms and
  different semantic objects until a named compatibility theorem proves their
  equality under explicit hypotheses.
- For approximation, the algorithm returns a center and a certified error or
  a requested-precision result. Convergence or almost-sure termination without
  an effective modulus does not by itself implement the approximation.
- Almost-everywhere equality is recorded as almost-everywhere equality. It
  does not justify pointwise replacement at null histories.

### Consumer migration

- Effective consumers call the executable definition. They use the
  compatibility theorem only when a proof must cross into analytic semantics.
- Analytic consumers may continue to use the general definition directly.
- A previous analytic definition becomes a compatibility-only path only after
  an exact theorem covers the consumer's full input contract and all internal
  effective consumers have migrated. If the analytic definition has a wider
  domain, it remains a current general API even after every effective consumer
  migrates. It is still described as an analytic semantic definition, not as
  legacy.
- A restricted-domain algorithm, a numerical approximation, or an
  almost-everywhere theorem never authorizes claiming that the general
  analytic definition has been replaced.

## Registered semantic compatibility bridges

This table is the documentation mirror of
`SEMANTIC_COMPATIBILITY_BRIDGES` in
`scripts/check_efg_governance.py`. Each row is one registered dictionary
entry; multiple executable owners in one row are the complete owner set for
that bridge.

| Work item | Semantic compatibility module | Required executable owner(s) | Analytic target | Smallest governed facade |
|---|---|---|---|---|
| A19 | `EconCSLib.Math.Probability.Effective.Semantics` | `EconCSLib.Math.Probability.Effective.Enclosure`<br>`EconCSLib.Math.Probability.Effective.Core` | proof-only event/observable denotation and representation certificates for expectation, pushforward, law bind, and kernel composition | `EconCSLib.Math.Probability.Effective.Analytic` |
| A19 | `EconCSLib.Math.Probability.Effective.UniformSemantics` | `EconCSLib.Math.Probability.Effective.Uniform` | exact rational interval-event queries and simple-observable expectations as unit-interval volume, plus constant non-atomic kernel correctness | `EconCSLib.Math.Probability.Effective.Analytic` |
| A03 | `EconCSLib.GameTheory.ExtensiveGame.Simulation.Kernel.FiniteExecution` | `EconCSLib.GameTheory.ExtensiveGame.Execution.Discrete.HistoryKernel`<br>`EconCSLib.GameTheory.ExtensiveGame.Execution.Discrete.FiniteObservation` | measurable-kernel steps, arbitrary finite prefixes, and state/event coordinate marginals | `EconCSLib.GameTheory.ExtensiveGame.Interface.Execution.Analytic` |
| A05/A08 | `EconCSLib.GameTheory.ExtensiveGame.Simulation.Kernel.EffectivePathLaw` | `EconCSLib.GameTheory.ExtensiveGame.Execution.Discrete.EffectivePathLaw` | every queried coherent effective prefix law as the corresponding analytic partial-trajectory marginal, plus direct finite marginals of the original tail event/state path measures | `EconCSLib.GameTheory.ExtensiveGame.Interface.Execution.Analytic` |
| A15 | `EconCSLib.GameTheory.ExtensiveGame.Simulation.Kernel.CertifiedPathApproximation` | `EconCSLib.GameTheory.ExtensiveGame.Execution.Discrete.CertifiedPathApproximation` | exact finite-marginal integration of the prefix observable, then interval enclosure and searched-tolerance correctness from an external pointwise uniform path-utility certificate | `EconCSLib.GameTheory.ExtensiveGame.Interface.Execution.Analytic` |
| A06 | `EconCSLib.GameTheory.ExtensiveGame.Simulation.Kernel.FiniteRealizedInformation` | `EconCSLib.GameTheory.ExtensiveGame.Execution.Discrete.RealizedInformation` | finite `bind`/`map` realization as the existing analytic `realizedKernel`, plus realization of the compiled event policy | `EconCSLib.GameTheory.ExtensiveGame.Interface.Execution.Analytic` |
| A09 | `EconCSLib.GameTheory.ExtensiveGame.Simulation.Kernel.FiniteCompleteEventPath` | `EconCSLib.GameTheory.ExtensiveGame.Execution.Discrete.FiniteCompleteEventPath` | finite prefix and coordinate marginals of a bounded-terminal complete event-path law as analytic partial trajectories | `EconCSLib.GameTheory.ExtensiveGame.Interface.Execution.Analytic` |
| A20 | `EconCSLib.GameTheory.ExtensiveGame.Simulation.Presentation.Kernel.EffectiveBehavioralProfile` | `EconCSLib.GameTheory.ExtensiveGame.Execution.Discrete.EffectiveKernelBehavioralProfile` | the executable high-level profile's compiled policy as the original analytic compiled policy, with equality of every finite event-prefix and projected state-prefix marginal; `Simulation.Restart.Observed` further gives the direct continuation-event, continuation-state, fresh-restart-state, and normalized-continuation finite marginals | `EconCSLib.GameTheory.ExtensiveGame.Interface.Execution.Analytic` / `Interface.Restart` |
| A04 | `EconCSLib.GameTheory.ExtensiveGame.Simulation.Continuation.FiniteConditioning` | `EconCSLib.GameTheory.ExtensiveGame.Execution.Discrete.ConditionalContinuation` | exact finite posterior continuation as bind against partial trajectories and absolute-path finite marginals; the neighboring analytic conditioning leaf also identifies positive-prefix RCD finite marginals | `EconCSLib.GameTheory.ExtensiveGame.Interface.Equilibrium.Analytic` |
| A03/A10 | `EconCSLib.GameTheory.ExtensiveGame.Simulation.Equilibrium.FinitePayoff` | `EconCSLib.GameTheory.ExtensiveGame.Execution.FinitePayoff` | finite Dirac, supplied-path, and partial-trajectory integrals, including stopped-payoff truncation bounds | `EconCSLib.GameTheory.ExtensiveGame.Interface.Equilibrium.Analytic` |
| A19 | `EconCSLib.GameTheory.ExtensiveGame.Simulation.Equilibrium.EffectivePathUtility` | `EconCSLib.Math.Probability.Effective.Core` | simple-observable expectation oracle as the existing path-utility integral when the observable denotes the player's utility | `EconCSLib.GameTheory.ExtensiveGame.Interface.Equilibrium.Analytic` |
| A07 | `EconCSLib.GameTheory.ExtensiveGame.Simulation.Presentation.Chance.FiniteExecution` | `EconCSLib.GameTheory.ExtensiveGame.Execution.Discrete.ObservedChance` | observed player/chance finite action laws, bounded event prefixes, and complete finite state-prefix marginals as the measurable presentation's kernel/path semantics | `EconCSLib.GameTheory.ExtensiveGame.Interface.Execution.Analytic` |
| A05 | `EconCSLib.GameTheory.ExtensiveGame.Simulation.Restart.FiniteExecution` | `EconCSLib.GameTheory.ExtensiveGame.Execution.Discrete.FiniteObservation` | fresh-clock, absolute-clock, and spliced restart-prefix measures | `EconCSLib.GameTheory.ExtensiveGame.Interface.Restart` |

These bridge modules may add reindexing functions, realization predicates, and
proofs. They do not own new `noncomputable` result-producing definitions. The
governance checker verifies that each bridge reaches its executable owner,
that its facade reaches the bridge, that the dependency does not run back from
the executable owner, and that the bridge contains an equality theorem but no
new noncomputable data declaration.

## Registered algorithm-first owners

This table is the documentation mirror of
`ALGORITHM_FIRST_EXECUTABLE_OWNERS` in
`scripts/check_efg_governance.py`. Each row records one protected owner and
the exact smallest facade through which the checker requires it to be
reachable.

| Work item | Executable owner | Required finite facade | Method or responsibility |
|---|---|---|---|
| A19 | `EconCSLib.Math.Probability.Effective.Enclosure` | `EconCSLib.Math.Probability.Effective` | exact rational enclosures and arbitrary-positive-tolerance query oracles |
| A19 | `EconCSLib.Math.Probability.Effective.Core` | `EconCSLib.Math.Probability.Effective` | coded-event laws, finite rational simple observables, inverse-image pushforwards, law bind, and expectation-transformer kernel composition |
| A19 | `EconCSLib.Math.Probability.Effective.Uniform` | `EconCSLib.Math.Probability.Effective` | exact non-atomic unit-interval backend for finite rational interval-union event codes |
| A03 | `EconCSLib.GameTheory.ExtensiveGame.Execution.Discrete.HistoryKernel` | `EconCSLib.GameTheory.ExtensiveGame.Interface.Execution.Finite` | history-dependent finite-law state and action-recording execution |
| A03/A05 | `EconCSLib.GameTheory.ExtensiveGame.Execution.Discrete.FiniteObservation` | `EconCSLib.GameTheory.ExtensiveGame.Interface.Execution.Finite` | bounded prefix laws, observations, clock conversion, and restart primitives |
| A08 | `EconCSLib.GameTheory.ExtensiveGame.Execution.Discrete.EffectivePathLaw` | `EconCSLib.GameTheory.ExtensiveGame.Interface.Execution.Finite` | coherent, uniformly queryable finite-prefix laws and cylinder masses |
| A14 | `EconCSLib.GameTheory.ExtensiveGame.Execution.Discrete.EffectivePathUtility` | `EconCSLib.GameTheory.ExtensiveGame.Interface.Execution.Finite` | exact rational expectations of finite-prefix observables |
| A15 | `EconCSLib.GameTheory.ExtensiveGame.Execution.Discrete.CertifiedPathApproximation` | `EconCSLib.GameTheory.ExtensiveGame.Interface.Execution.Finite` | rational scheme centers, declared radii, intervals, and first acceptable-horizon search |
| A16 | `EconCSLib.GameTheory.ExtensiveGame.Execution.Discrete.DiscountedPathUtility` | `EconCSLib.GameTheory.ExtensiveGame.Interface.Execution.Finite` | exact first-H rational discounted rewards, geometric tail radii, vanishing proof, and least-horizon search |
| A09 | `EconCSLib.GameTheory.ExtensiveGame.Execution.Discrete.FiniteCompleteEventPath` | `EconCSLib.GameTheory.ExtensiveGame.Interface.Execution.Finite` | bounded-terminal event execution replayed as finite laws of terminal-absorbing complete event and projected state paths |
| A06 | `EconCSLib.GameTheory.ExtensiveGame.Execution.Discrete.RealizedInformation` | `EconCSLib.GameTheory.ExtensiveGame.Interface.Execution.Finite` | exact finite abstract-action selection followed by prefix-dependent concrete realization |
| A20 | `EconCSLib.GameTheory.ExtensiveGame.Execution.Discrete.EffectiveKernelBehavioralProfile` | `EconCSLib.GameTheory.ExtensiveGame.Interface.Execution.Finite` | high-level effective presentation/profile assembly, raw policy compilation, and finite-prefix execution |
| A04 | `EconCSLib.GameTheory.ExtensiveGame.Execution.Discrete.ConditionalContinuation` | `EconCSLib.GameTheory.ExtensiveGame.Interface.Execution.Finite` | positive-mass finite Bayes filtering and absolute-clock posterior continuation |
| A10 | `EconCSLib.GameTheory.ExtensiveGame.Execution.Discrete.ContinuationTruncation` | `EconCSLib.GameTheory.ExtensiveGame.Interface.Execution.Finite` | exact continuation centers, unfinished-mass radii, and bounded or least-horizon search |
| A07 | `EconCSLib.GameTheory.ExtensiveGame.Execution.Discrete.ObservedChance` | `EconCSLib.GameTheory.ExtensiveGame.Interface.Execution.Finite` | direct finite action policy and event execution for observed chance games |
| A03/A10 | `EconCSLib.GameTheory.ExtensiveGame.Execution.FinitePayoff` | `EconCSLib.GameTheory.ExtensiveGame.Interface.Execution.Finite` | exact rational finite-history and finite-prefix payoff expectations |
| A03 | `EconCSLib.GameTheory.ExtensiveGame.Execution.FiniteCompletePath` | `EconCSLib.GameTheory.ExtensiveGame.Interface.Execution.Finite` | bounded Arena execution replayed as terminal-absorbing complete paths |
| A10 | `EconCSLib.GameTheory.ExtensiveGame.Execution.Truncation` | `EconCSLib.GameTheory.ExtensiveGame.Interface.Execution.Finite` | exact stopped-payoff truncation bounds and horizon search |
| A17 | `EconCSLib.GameTheory.ExtensiveGame.Observed.FinitePureNash` | `EconCSLib.GameTheory.ExtensiveGame.Interface.Equilibrium.Discrete` | finite pure-profile checking, enumeration, and ordered witness search |
| A01 | `EconCSLib.GameTheory.ExtensiveGame.Observed.FiniteMeasureStrategy` | `EconCSLib.GameTheory.ExtensiveGame.Interface.Equilibrium.Discrete` | finite pure-profile marginals, outcome laws, and path laws by `FiniteLaw.map` |

Each must be reachable through its finite facade, contain no noncomputable data
declaration, and avoid analytic `Simulation`, supplied infinite-path, finite-law
measure-interpretation, and direct Mathlib measure-theory imports. This list is
expanded when another general algorithm becomes a supported main-library
owner.

A15's interval is a **scheme interval**: its center is computed exactly and
its radius is executable input.  The registered analytic bridge proves that
the interval encloses a particular infinite-path utility when the caller
supplies exact finite marginals, measurability/integrability, and a pointwise
uniform prefix-approximation bound by that radius.  The target value is not an
input to the search algorithm, and arbitrary measurable utilities do not
acquire such a certificate automatically.

A19 makes effective non-atomic probability a supported subdomain without
placing a finite-support assumption on the represented measure.  The model
chooses an event-code language. `EffectiveLaw` returns rational enclosures for
those codes, `EffectiveMap` supplies executable preimages, and
`EffectiveKernel` supplies simple-observable pullbacks so bind and composition
remain executable.  The pure `Effective` aggregate is frozen to the three
measure-free owners; the opt-in `Effective.Analytic` aggregate contains the
proof-only `Denotes`/`Represents` layer.  The first backend computes exact
unit-interval volume for finite rational interval unions.  None of this turns
an arbitrary measurable set, arbitrary integrable function, or null-prefix
regular conditional distribution into executable input.

A09 and A20 have exact semantic bridges only for every requested finite
prefix or coordinate marginal. Those theorems do not construct or identify a
general `Measure` on infinite path space. A09 may compute a finite law whose
atoms are terminal-absorbing path functions, but its registered analytic
claim remains the finite-marginal statement. A20 likewise compiles a coherent
finite-query interface; its continuation bridges preserve the canonical
absolute prefix and clock, while its fresh-restart bridge executes from time
zero, so no theorem silently identifies those two semantics.

A11--A13 and the finite-state exact part of A16 are also part of the algorithmic track, but their reusable
finite-chain owners are not registered in the facade-specific algorithm-owner map:
`EconCSLib.Math.Probability.FiniteMarkovChain.Reachability` computes exact
finite-chain reachability, terminal/nontermination laws, and zero-on-nonhit
rewards;
`EconCSLib.Math.Probability.FiniteMarkovChain.ReachabilitySemantics` proves
their Bellman, normalization, and late-hit results; and
`EconCSLib.Math.Probability.FiniteMarkovChain.Discounted` computes and proves
exact rational discounted values. A19's three reusable probability owners do
appear in `ALGORITHM_FIRST_EXECUTABLE_OWNERS` because the checker also freezes
their pure/analytic aggregate split.

## Classification consequences

The 58-item main-library feasibility ledger uses this contract as follows:

- finite-data and finite-prefix declarations receive executable counterparts
  and exact compatibility theorems;
- arbitrary measure/kernel and infinite-path declarations remain analytic
  semantics, with effective subdomain algorithms added separately;
- exact general conditioning, arbitrary exact integration, and pathwise
  eventual utility retain their analytic definitions; finite positive-mass,
  bounded-horizon, and certified-approximation results do not overstate their
  scope.

The per-declaration decision and hypotheses remain recorded in
[`efg-library-computability-declarations.md`](efg-library-computability-declarations.md).
Examples are consumers and regressions; they do not own any part of this
architecture.

## Unavoidable boundary

No library can simultaneously require all three of the following:

1. arbitrary mathematical measures, kernels, real functions, and infinite
   paths as inputs;
2. a total terminating exact program for every semantic query;
3. no additional effective representation, decision procedure, or convergence
   modulus.

This architecture keeps the first requirement. It obtains executable results
when a model also supplies the effective data needed by the second, and
otherwise retains the general analytic statement without claiming a
nonexistent algorithm. The mathematical generality of the library is
unchanged; only universal executability is deliberately not promised.
