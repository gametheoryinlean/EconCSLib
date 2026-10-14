# EFG proof trust, finite semantics, and namespace ownership

Lean declarations determine what is proved. A successful build checks a
statement against its hypotheses; it does not establish that the statement
matches its prose, that its hypotheses are inhabited, or that a supplied
certificate has been constructed. This note records the proof-dependency gate
and the semantic boundaries reviewed after the A–F computability migration.
It supplements the [semantic-regime contract](efg-semantic-universes.md).
The latest focused update is the algorithm-first two-track closure below.
The finite-observation section and the pre-Q/R, A–F, G, Q, and R sections are
historical checkpoints; their counts describe the named checkpoint rather
than the current tree.

## Algorithm-first two-track closure — 2026-09-04

The current file plan inventories every one of the **182 EFG source modules**
and **36 directly supporting probability/game-form modules**, for **218
governed main-library modules**.  It separately inventories all **69 example
modules**, which were not used as implementation owners.  The executable and
semantic work lands in **45 modules**, with two additional A19 navigation
aggregates separating pure execution from analytic interpretation. Governance
recognizes **20 algorithm-first owners** and **15 one-way semantic bridges**; an algorithm
owner cannot import `Measure`, an analytic bridge, or a supplied infinite-path
semantics in order to manufacture its returned value.

Items A01–A20 in the
[implementation ledger](efg-algorithm-implementation-ledger.md) are now
implemented.  They cover exact finite profile laws; history-dependent finite
execution; conditioning, continuation and fresh restart; finite realization
and observed chance; coherent prefix laws and bounded complete paths;
certified truncation; nonabsorbing rational Markov reachability, outcome,
nontermination and discounted values; rational cylinder utilities; certified
path approximation; finite pure-Nash enumeration; terminal-time DFA products;
finite-chain min-parity reduction; the high-level effective kernel-profile
adapter; and A19's effective coded-event probability layer. A19 supplies
rational enclosure oracles, finite rational simple observables, executable
pushforwards, law bind and kernel composition, plus an exact non-atomic
unit-interval backend. Its proof-only representation layer connects those
queries to measures, kernels, and integrals, including S082/S085/S086/S101.
Arbitrary `Set`, `Measure`, real-valued functions, and null-prefix RCD versions
still do not themselves provide executable event, observable, or conditioning
data.

The approximation certificate is substantive.  Its runtime computes only a
rational center and radius from finite marginals.  The semantic leaf proves
that the lifted finite-prefix observable has that center under the original
path measure and derives the target-integral error from a pointwise uniform
bound.  Thus the desired target error is a conclusion, not an input
certificate.  The current semantic result is the state-path uniform version;
an event-path or purely `L¹` interface may be added when a consumer supplies
the corresponding effective data.

Discounted path rewards read the reward at the absolute time `start + k`, but
normalize the discount exponent at the supplied continuation start as
`γ ^ k`.  The finite Markov solver uses a transient reward
`r : Fin n → ℚ`; after the original terminal is first hit, reward is zero.
These conventions are part of the algorithm contract and prevent a silent
change between continuation value and global-clock discounting.

The min-parity solver proves that its accepting and rejecting vectors equal
`terminalProbability 0` and `terminalProbability 1` in the constructed
two-terminal reduction.  It does not yet prove that the same rationals equal
the original total-chain path-measure event.  That final semantic leaf needs
proofs that the original finite chain almost surely enters a bottom SCC and
that the relevant states in a bottom SCC recur infinitely often.  Max-parity,
general MDP/stochastic-game solvers, and arbitrary Borel objectives are also
outside the current result.

The live computability scan now covers **265 modules** and classifies all **137 retained
noncomputable declarations** as 69 analytic definitions and 68 analytic
dependency propagations, with zero unresolved executable/review items.  The
A19 adds no noncomputable declaration. Governance reports the 218 modules,
20 owners and 15 bridges listed above and freezes the direct imports of both
the pure `Effective` and opt-in `Effective.Analytic` aggregates. Targeted A19
module builds, its runtime smoke, placeholder, computability, governance and
whitespace checks pass. The explicit A19 API decision records 97
Canonical/Frontend module paths and 1,670 current public declarations under the
unchanged 1,689-declaration ceiling; the two new paths are declaration-free
aggregates. The root and Examples builds, API-growth gate, and axiom gate over
all 265 audited modules also pass, with zero forbidden axiom dependencies.

## Historical checkpoint: finite observation and restart-prefix architecture — 2026-09-04

`Execution/Discrete/FiniteObservation.lean` adds pure exact queries over the
existing state/event history executor: arbitrary coordinates, final
coordinates, reindexed tails, arbitrary absolute horizons, time-zero fresh
restarts, and fresh continuations spliced after a retained prefix. Horizons
inside the retained prefix are deterministic truncations. Absolute
continuation retains the original clock; fresh execution starts at zero and
drops its duplicate root coordinate when spliced. Event histories retain the
selected actions until a caller explicitly projects to states.

`Simulation/Kernel/FiniteExecution.lean` now derives the state-coordinate,
event-coordinate, and event-to-state coordinate measure equalities from its
existing arbitrary finite-prefix `partialTraj` theorem. The computation is
therefore not justified by substituting a state-only policy or by accepting a
target marginal certificate.

`Simulation/Restart/FiniteExecution.lean` connects those pure laws directly to
the pre-existing restart semantics. The fresh executor recurses at time zero
without a dependent `0 + n` cast. Separate all-horizon theorems identify its
Dirac interpretation, the absolute-clock law, and the spliced-fresh law with
the original analytic restart-prefix measures. Horizons inside the retained
prefix reduce to deterministic truncation rather than executing unused random
steps.

These files, `Simulation.Continuation.FiniteConditioning`, and
`Simulation.Equilibrium.FinitePayoff` are now the four registered branches of
the [semantic compatibility layer](efg-semantic-compatibility.md). Governance
checks that computation owns the returned values, dependencies run only from
the semantic bridge to the executable owner, each bridge is exposed by its
documented facade, and no bridge introduces a new noncomputable data
definition. The general analytic targets remain current semantics rather than
being relabeled as legacy.
Seven finite owners are additionally guarded as algorithm-first modules: they
cannot import the analytic bridge, supplied infinite-path semantics, or measure
interpretation, and cannot introduce noncomputable data definitions.
These guards constrain effective execution routes only; they do not narrow the
general analytic carriers or theorem domains.

The full governed build covers 187 registered modules. The current axiom audit
covers **12,007 declarations in 239 modules**, with **zero forbidden axiom
dependencies**. The computability audit reports **137 noncomputable
declarations** (69 analytic definitions and 68 analytic dependency
propagations) and zero unresolved executable/review items. A pure smoke model
evaluates an absolute-clock continuation to `103` and the corresponding
time-zero fresh restart to `101`, and checks retained-prefix, tail, state
projection, and recorded-action coordinates. Root build, all-module build,
placeholder, API-growth, computability, governance, axiom, and whitespace
checks pass.

## R automatic finite-chain absorption — 2026-09-03

The [R checkpoint](efg-computability-migration.md#r-checkpoint--2026-09-03)
closes the automatic certificate obligation in the existing finite Markov
examples. `autoBound`, `autoCheck`, and `autoSolve` use only finite enumeration,
matrix powers, exact rationals, and the retained determinant/Cramer solver.
The checker covers all `Fin n`, including unreachable closed components.

The critical completeness argument is formalized through increasing finite
sets of states with positive-probability terminal routes. Their recurrence
uses nonnegative normalized rows; cardinality stabilization supplies the
finite path-shortening bound. This proves the automatic Boolean check iff the
independently stated convergence property `AbsorbsAll`. Failure supplies one
state with survival exactly one at all horizons. Successful checking proves
normalization of the original joint first-hit law, nonsingularity, actual
solver success, unique Bellman solutions, integrability, and equality to the
original reward and actual first-hit-time integrals.

Concrete checks cover all requested successful values, an already terminal
start, two empty-transient-domain shapes, a no-terminal closed chain,
deterministic multistep absorption, exact tiny positive exit probability, and
the good/bad-start distinction inside `closedClass`. The starting/final
checkpoint scan covered **227 modules** and preserved exactly **138 identities**,
with zero additions and removals. The axiom gate checks **11,534 declarations**
and reports **zero forbidden dependencies**. Both baseline files remain
byte-identical to task start. `Lean.isNoncomputable` returns false for the four
new public data functions and all five new regression chains.

Stable and example builds, `FiniteLawSmoke.lean`, placeholder/API/computability/
axiom/governance checks, both modified-module `leanchecker` replays, local
document links and whitespace checks pass. The `--skip-build` audits verify
freshness using Lake's rehashed dependency traces. Only the two existing
Markov Lean modules changed during R; Q and the frozen API remain preserved.

## Q positive-tolerance approximation — 2026-09-03

The [Q checkpoint](efg-computability-migration.md#q-checkpoint--2026-09-03)
closes the positive-tolerance approximation obligation in the existing
`FiniteTruncation.lean` opt-in prototype. The proof uses measurable decreasing
no-hit events, their exact nontermination intersection, actual-law
normalization and continuity from above. Identification with `noneMass`
passes through `measure_no_hit` and its almost-sure absorption proof.
`exists_radius_le` derives the decidable search predicate's existence from
the original reachability hypothesis and positive rational tolerance;
`leastHorizon` actually runs `Nat.find`, and `approximate` uses M's estimate.

`approximate_correct` retains all of M's semantic assumptions and the same
original eventual-utility integral. Minimality and both sides of the old
budget boundary are proved. Concrete consumers include the actual geometric
executor, negative and zero terminal rewards, a terminal current history,
and an absolute-clock policy whose result distinguishes a nonempty incoming
history from the root. The old zero-tolerance budget semantics is preserved.
No runtime bound, finite expected hitting time, or exact real expectation
follows from this result. R supplies a separate fixed finite-chain result.

The same historical 227-module full scan retained exactly the starting **138
noncomputable identities**, with no additions or removals. The axiom scan
checks **11,448 declarations** and finds **zero forbidden dependencies**.
Both algorithms are explicitly unmarked by `Lean.isNoncomputable`.
Stable/example builds, runtime smoke, placeholder/API/computability/axiom/
governance checks, modified-module kernel replay, document links and diff
whitespace checks pass. Both baseline files remain unchanged from task start.

## Pre-Q/R semantic review — 2026-09-03

The proof-dependency scan at that checkpoint covered **227 finite-law, EFG,
and extensive-game example modules**, including **11,366 owned declarations** and
their transitive axiom dependencies. It found **zero forbidden dependencies**.
The accepted logical axioms remain exactly `propext`, `Quot.sound`, and
`Classical.choice`. The full computability scan still finds **138 identities**:
58 library identities and 80 example identities. Neither baseline changed.

Manual semantic review follows the finite-law representation, finite history
execution, its analytic kernel bridge, the H–O computation prototypes, and
the statements that connect them to payoff and equilibrium semantics. It also
checks the supplied complete-law adapters, the scope of pure SPE and Kuhn
transfer, evaluator-relative sequential equilibrium, and the positive-atom
conditional-kernel boundary. This is not a claim that every one of the 11,366
declarations received an individual mathematical interpretation review.

No incorrect theorem or circular correctness argument was found in these
reviewed chains. In particular, the new work may rely on the following actual
results, with the stated boundaries:

| Source and checked result | Mathematical content and boundary |
|---|---|
| `Math/Probability/FiniteLaw/Core.lean`: normalization, `bind`, `HasPositiveAtom`, `Equivalent` | Nonnegative rational weights sum to one; bind multiplies the original weights. Duplicate atoms contribute repeatedly, zero atoms do not imply reachability, and semantic equivalence compares all rational observables. |
| `StochasticTreeCompilation.lean`: `totalExpectedPayoff_eq_expectedPayoffWithFuel` | The computed structural bound includes leaf fuel one and every child, including zero-weight branches. The theorem preserves occurrence policy and incoming path. Real payoff arithmetic is not arbitrary-real numerical approximation. |
| `FiniteLawIntegral.lean`: `integrable`, `integral_eq_expectRat` | The actual finite weighted Dirac measure is normalized and integrates the same rational payoff. Measurable singletons support the pointwise integration theorem; the ambient carrier need not be finite or countable. |
| `FiniteExecutionIntegral.lean`: `historyLaw_eq_coordinate`, `integral_stoppedUtility` | The measure is the existing history-lifted `Kernel.traj`, not an input marginal certificate. `PathExecution.nonempty` constructs its analytic witness in `Prop`; the proof then substitutes the defining equations. The finite executor retains the complete incoming history. |
| `Execution/Discrete/FiniteObservation.lean`: coordinate, tail, absolute-prefix, fresh-restart, and splice laws | Every query maps the exact `FiniteLaw` executor rather than sampling an analytic path law. Absolute continuation retains the full old prefix and clock; fresh restart uses only the latest state at time zero; finite splicing omits the duplicate fresh root. Horizons inside the old prefix are deterministic truncations. Event policies retain actions until any final state projection. |
| `Simulation/Kernel/FiniteExecution.lean`: `measure_coordinateLawFrom_eq_partialTraj_map`, `measure_eventCoordinateLawFrom_eq_partialTraj_map`, `measure_stateCoordinateLawFrom_eq_partialTraj_map` | The exact coordinate queries are derived by measurable projection from the already-proved arbitrary-prefix equality. The event-to-state theorem projects only after the action-recording partial trajectory has executed, so it does not silently replace an event-history policy by a state-only policy. |
| `FiniteConditionalContinuation.lean`: `conditionalPayoff_bayes`, `conditionalLaw_joint`, `conditionalPayoff_joint_integral` | Positive observations use the computed normalized posterior, and impossible observations return `none`. The joint law records the observation-time history and the final history. This is finite-window conditioning, not an arbitrary infinite-utility evaluator. |
| `FiniteCompletePath.lean`: `completePaths_marginal`, `completePaths_legalTransition`, `exists_pathLaw` | The supplied horizon must terminate every positive final atom. The algorithm replays stored histories at `current.length + n`; all-time marginals and legal absorbing paths are proved. The finite path law and its measure witness are constructed, but the horizon is not discovered. |
| `FiniteTruncation.lean`: `measure_no_hit`, `estimate_correct`, `search_correct` | Legal transitions, absorption, normalization, marginals and integrability are proved for the actual trajectory. The process premise is almost-sure terminal reachability; a bounded extension and terminal-payoff agreement remain explicit. The error radius is exactly `bound * noneMass`. |
| `FinitePureNash.lean`: `check_iff` and occurrence bridge | The finite tables are the original root-bound pure strategy types, so deviations are not silently restricted to a selected list. In general the utility is a horizon-dependent stopped payoff. Sufficient termination fuel is needed for eventual-outcome interpretation. |
| `Math/Probability/FiniteMarkovChain.lean`: `run_expect`, `run_firstHit`, `run_survival` | The actual normalized rows generate censored execution. `inr (r,a)` records first termination at time `r+1`; active mass remains explicit. These results identify the coefficients `Q^r R`, not just a guessed matrix model. |
| `Math/Probability/FiniteMarkovChain/Semantics.lean`: `hasSum_firstHit`, `integrable_time`, `solve_correct`, `autoCheck_iff_absorbsAll` | A checked strict finite-step absorption bound proves summability, nonsingularity, normalization and integrability. The actual rational solver output is uniquely identified with reward and hitting-time integrals under the constructed first-hit law. The automatically computed full-domain certificate is sound and complete for absorption. This is a fixed full-domain Markov model, not an EFG endpoint quotient. |
| `Math/Probability/RationalIntervalUnion.lean`: `intervalMass`, `intersect`, `probability` | The pure evaluator clips rational bounds and performs exact recursive inclusion-exclusion. Its finite description language retains overlap, duplicates, reversed bounds, out-of-range bounds, singletons, and touching endpoints without deciding arbitrary real predicates. |
| `Math/Probability/RationalIntervalUnion/Volume.lean`: `intervalEvent_intersect`, `probability_eq_volume`, `probability_nonneg`, `probability_le_one` | Endpoint intersection preserves the represented set, and the executable rational result equals the original non-atomic unit-interval volume. The semantic proof does not replace volume by a finite law or claim an evaluator for arbitrary measurable events. |

Paths in this table that start with `Math/` are main-library probability
modules; the remaining unqualified paths are under
`EconCSLib/Examples/ExtensiveGame/`. The associated source imports and kernel
bridge declarations were reviewed alongside the listed entry points.
Concrete nonzero and signed-payoff examples witness that the central
correctness premises are inhabited; zero-weight, zero-observation,
insufficient-fuel, repeated-history and nonabsorbing examples exercise their
failure boundaries.

### Definitions and certificates that are not new existence theorems

### Mathematical contract for the two next tasks

At this pre-Q/R checkpoint, the [Q and R prompts](efg-finite-computation-prompts.md)
were pending work. The earlier temporary probes established only local
executable constructions. Q and R were subsequently completed as recorded
above; the obligations below preserve the original review contract.

**Q — guaranteed positive-tolerance approximation.** On arbitrary raw paths,
being nonterminal at coordinate `H` need not form a decreasing family of
events. Use the decreasing measurable no-hit events
`B_H = {path | ∀ t ≤ H, path t is nonterminal}` instead. The existing
`measure_no_hit` identifies their probabilities with the computed `q_H` using
the proved almost-sure absorption. Almost-sure reachability and continuity of
measure from above then give `q_H → 0`; normalization supplies finite measure.
This is the missing direction beyond the existing
`ae_reaches_of_mass_tendsto_zero` theorem. After the exact cast conversions,
positive rational tolerance gives an inhabited decidable search predicate.
`Nat.find` may execute that search with a proof-only termination argument;
no numerical bound or convergence-rate oracle is needed. The EFG-facing
entry point must derive that argument from the existing process assumptions,
not request the target threshold existence from its caller. Bounded reward
is required for the error theorem; finite expected hitting time is not.
Tolerance zero is outside the uniform termination guarantee.

**R — automatic finite-chain absorption and solution.** Compute
`k = n + 1` and `c = max ({0} ∪ {∑ j, (Q^k) i j | i : Fin n})` using exact
rationals, then reuse `admissible` and `solve`. General completeness still
requires proof: a positive route to a terminal state can have repeated
nonterminal states removed, yielding a route of length at most `n`. If every
state has such a route, all `k`-step survival rows are strictly below one;
otherwise a terminal-inaccessible reachable region retains its probability
mass. The verdict concerns every supplied nonterminal state, including bad
components unreachable from a preferred start. Failure is not a statement
that all starts fail. Handle `n=0`, `m=0`, exact positive probabilities and
terminal time zero explicitly. Success must reuse `solve_correct`, including
its integrability and probability conclusions, rather than only solve a
linear equation. The first-hit law remains distinct from a general EFG
complete-path law.

An independent exact-rational check compared this proposed matrix criterion
with positive-edge terminal reachability on 1,040 substochastic matrices of
dimensions zero through three with half-integer probability entries. The
verdicts agreed, including the empty case. This is finite diagnostic evidence,
not the required general completeness theorem, and is not a substitute for
R's Lean proof.

### Revalidation

The stable library and example builds, finite-law runtime smoke test,
placeholder/API-growth/computability/axiom/governance checks, and all 17
computability/axiom audit tests passed. The axiom scan follows dependencies
outside its owned modules; anonymous native runtime checks are not used as
exported theorem evidence. All **227 modules then in scope** also passed exact
per-module replay using the pinned checker's `replayFromImports` routine
from Lean's `LeanChecker` source. The explicit source
module list avoids obsolete cached modules selected by broad prefixes. This
rechecks owned declarations with the Lean kernel while trusting their
imports; it is not a fresh replay of all Mathlib or an external verifier.
Source hashes were checked against the starting snapshot. No Lean source or
baseline was changed by this review. Document links, formatting and
`git diff --check` were checked separately. The historical counts below have
not been rewritten.

## Proof-dependency gate

Run `python3 scripts/check_efg_axioms.py` from the repository root. The script
rebuilds the same finite-law, EFG, and extensive-game example modules as the
computability audit, then asks `Lean.collectAxioms` for every owned declaration.
It includes generated/private declarations and follows dependencies into other
modules. The only permitted axioms are `propext`, `Quot.sound`, and
`Classical.choice`. Custom axioms, `sorryAx`, and generated `native_decide`
axioms fail the check. `--skip-build` verifies freshness with Lake's rehashed
dependency traces instead of rebuilding; it rejects stale artifacts.

The gate is part of the build workflow. Integration fixtures exercise a
standard classical proof, a false external assumption passed through a private
helper, a missing proof, and a public native-computation proof with a downstream
consumer. Native execution examples may still test runtime behavior, but they
are not accepted as exported mathematical proof evidence.

The 2026-09-03 audit found five generated native axioms in
`Examples.RandomTermination`, affecting eleven exported theorem conclusions.
The five direct proofs were:

- `balanced_one_step_win_probability` and
  `immediate_one_step_win_probability`;
- `balanced_noneMass_zero`, `balanced_noneMass_one`, and
  `balanced_noneMass_two`.

Their values agree with the concrete model: the fair policy wins at one step
with probability one half, the immediate policy with probability one, and
unfinished mass at horizons zero, one, and two is one, one half, and zero.
The issue was the additional proof trust, not a numerical counterexample.
The proofs now use finite-law identities, reduction, `simp`, and `norm_num`.
All theorem statements and downstream conclusions are retained.

After the A–F proof repair, the elaborated audit covered **10,551 declarations
in 219 modules**, with **zero forbidden axiom dependencies**. This is an axiom audit
of that entire scope, not a manual interpretation of every theorem in it.
`leanchecker` additionally replays the 24 Lean modules changed during A–F,
the finite-law modules, stopped execution, infinite trajectory, and the
analytic complete-law adapter: 33 modules in total. Replay uses the pinned
Lean kernel and trusts imported dependencies; it is not an external verifier
or a fresh replay of all Mathlib.

## Semantic checks

The manual review follows the definitions, hypotheses, and consumers involved
in A–F, with particular attention to the following distinctions.

| Surface | Meaning checked and retained |
|---|---|
| Finite terminal decisions | Constructor cases decide emptiness of available actions. Unreachable ghost states are still handled; reachability assumptions are not silently made global. |
| History objectives | Histories retain their actions. Two paths reaching the same terminal state can have different objectives; endpoint equality does not replace history equality. |
| Occurrence strategies | The two repeated-subtree occurrences are distinguished. The length test is used only after an exhaustive proof that these are the two relevant decision histories. Non-isomorphism excludes an arbitrary isomorphism, not only the canonical forgetting map. |
| Finite laws | Atoms have nonnegative rational weights with total weight one. Duplicate atoms and ordering are representational; `Equivalent` compares outcome masses. The random-policy inequality has an event-mass witness. Zero-mass conditioning returns `none`. |
| Bounded terminal search | `none` means no terminal coordinate was found within the supplied fuel. It does not establish nontermination. `boundedWinUtility` is the expectation of a win indicator, not the expected value of the separate payoff function taking terminal values two and one. |
| Stopped utility | At the selected terminal coordinate it returns the terminal payoff; otherwise it returns zero. The new reduction checks use a nonterminal payoff of seven, so the zero branch cannot pass accidentally because the original root payoff was already zero. |
| Eventual utility and convergence | Eventual utility requires eventual terminal absorption for the pointwise identification. Almost-everywhere convergence uses the stated almost-sure certificate; the integral limit also uses boundedness. No bounded terminal decision is advertised as an algorithm for deciding eventual absorption. |
| Supplied path-law interfaces | `Arena.pathLaw` projects a supplied probability measure. Its marginal and legality conclusions require explicit coherence assumptions. Such accessors do not construct a law or prove its existence. The analytic adapter constructs its measure but still requires canonical history legality where stated. |

`KernelArena.toMeasurable` embeds a **finite rational law** by a finite weighted
sum of Dirac measures. Its normalization proof is retained. The old module
comments describing a general `PMF.toMeasure` embedding were inaccurate and
have been corrected, together with the project design summary. Arbitrary
countably supported real-weighted PMFs are outside this embedding's scope.

No contradictory theorem was found in the reviewed statements. This conclusion
is limited to the stated model, hypotheses, proof-dependency scan, and manual
review scope; an assumed certificate is not counted as a new existence result.

## Namespace ownership

The Formech reference uses mathematical owners such as `Agent`, `Mech`,
`Prefs`, and `Single_Item_Auction`, with sections for local assumptions and
notation. EconCSLib follows that ownership pattern while retaining its existing
Lean/Mathlib naming conventions and public qualified names.

In `Simulation/Equilibrium/Outcome` and `Simulation/Continuation/Observed`,
owner blocks are explicit nested namespaces under `MeasurableHistoryModel`,
`TerminalPayoffExtension`, `BoundedTerminalPayoffExtension`, and
`MeasurableKernelPresentation.KernelBehavioralProfile`. An empty namespace was
removed. `StoppedUtility` and `StoppedConvergence` sections organize the bounded
results; required decidability remains explicit at the declarations that use
it. This also preserves universe and argument order.

`HistoryObjectiveContinuation.RouteObjective` and
`OccurrenceNonIso.OccurrenceDecision` are **sections**, not new namespaces.
They restrict the local decision instances to their actual uses. Comparing
the elaborated before/after environments of the two core modules found the
same 176 non-private declarations and exactly the same declaration types.
No aliases or new public namespace roots were introduced.

Style provenance: the local Formech checkout was based on commit
`d0bb1913acc1f710ba6eadf1244b633abbc75fb9` with existing local edits. The
reviewed snapshots were `lean/formech.lean` (SHA-256
`48c52039c4b229bba33ae793c3757842ec8727dff3eda136769d4d372e5ac310`)
and `lean/single_item_fixed_price.lean` (SHA-256
`42ffc7e4e678492b485bd80ef075acd2261f6fbdb22e02c02b305531b59a234f`).
That checkout was read only; neither its code nor its Lean version was copied.

## Computability evidence

At the A–F proof-review checkpoint, the retained set was 140 noncomputable
identities, with unchanged elaborated types and noncomputable dependency sets. Source evidence was renewed
only after reviewing the affected spans and regression files. Both the API
growth baseline and the noncomputability baseline remain unchanged. See the
[migration record](efg-computability-migration.md) for classification policy;
classification hashes are change detectors, not mathematical proofs.

Validation passed: `lake build`, `lake build EconCSLib.Examples`, the finite-law
runtime smoke test, the placeholder/API-growth/computability/governance checks,
the full axiom audit, the 33-module kernel replay, 17 computability/axiom tooling
tests, and `git diff --check`. Existing unrelated worktree edits were preserved.

### G follow-up — 2026-09-03

The [G checkpoint](efg-computability-migration.md#g-checkpoint--2026-09-03)
reduces that set from 140 to **138**, with no new identity. `Countable Node`
uses an explicit two-tag injection proved inside `Prop`; its measurability
consumers remain intact. `halfAction` uses an exact rational cast, and the
kernel-checked `halfAction_coe` theorem identifies it with real `1/2`. Existing
lower-half cylinder nonemptiness, properness, and probability theorems remain.
No runtime countability encoding, arbitrary-real numerical algorithm, or new
analytic-law construction is claimed.

The current full axiom audit covers **10,548 declarations in the same 219
modules**, with **zero forbidden axiom dependencies**. Both changed examples
also pass `leanchecker`. Stable/example builds, the finite-law smoke test,
placeholder/API-growth/computability/governance checks and `git diff --check`
pass. Direct environment queries mark neither `instCountableNode` nor
`halfAction` as noncomputable. Both baselines
are unchanged; the classification retains its original A–F snapshot separately
from the live G evidence.
