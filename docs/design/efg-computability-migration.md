# EFG Computability Review and Migration Prompts

> Historical development ledger. Counts and checkpoints below describe their
> dated development snapshots. The completed publication subset excludes
> sequential-equilibrium and arbitrary-measure pure-strategy prototypes and
> their adapters. Use `efg-module-status.md` and the live audit tools for the
> submitted module and declaration census.

This is an operational workflow for making EFG execution computable while
preserving its mathematical semantics. Lean source, the architecture documents,
and `scripts/check_efg_computability.py` own the live implementation and audit.
This document does not establish new API-growth exceptions.
Executable ownership, analytic interpretation, and correspondence evidence
follow [`efg-semantic-compatibility.md`](efg-semantic-compatibility.md).

## Current objective — 2026-09-03

Finite execution must use executable decisions, explicit data, and effective
search. General analytic semantics may retain individually justified
`noncomputable` definitions. Supplying a mathematical object or projecting a
certificate is recorded separately from computing that object.

This objective replaces the earlier blanket zero-audit target and the old
pending numeric prompts 8–12. Completed numeric prompts 0–7 and the partial
analytic migration checkpoint are preserved below as historical records only.
The sequential **A–F** workflow is complete. Its prompts remain below as an
operational record. The checker now enforces the reviewed boundary while the
existing declaration-identity baseline remains unchanged.

The subsequent A–P workflow and tasks Q–R are complete. See the Q/R checkpoints
and the dated O/P records for the finite capabilities and final audits.

## A19 effective event and simple-observable layer — 2026-09-04

The live computability scan now covers **265 modules**: 182 main EFG modules,
69 EFG examples, seven `FiniteLaw` modules, and seven `Effective` probability
modules. It still finds **137 noncomputable identities in 35 modules**. A19
adds no noncomputable data declaration; its analytic interpretation is stated
with proof-only `Denotes` and `Represents` relations.

The measure-free `Effective` aggregate exposes rational enclosures, coded-event
effective laws/maps/kernels, finite rational simple observables, and the exact
unit-interval rational-interval backend. Its direct imports are frozen to
`Enclosure`, `Core`, and `Uniform`. The opt-in `Effective.Analytic` aggregate
is separately frozen to the pure aggregate plus `Semantics` and
`UniformSemantics`. The semantic leaves prove enclosure, expectation,
pushforward, law bind, kernel composition, volume, and constant non-atomic
kernel correctness without moving computed values into the analytic layer.

All module counts in the dated checkpoints below describe those historical
checkpoints; they are not the current 265-module scanner inventory.

Removing a constructor and requiring its result as an input is not, by itself,
a computational implementation. A migration must preserve the original
construction, existence result, or realization theorem under the original
mathematical hypotheses; any stronger computational input must be explicit.
Do not turn a formerly proved conclusion into an assumed certificate merely
to reduce the count.

## Effective finite-law and non-atomic event queries — 2026-09-03

Following the existing-declaration search, six retained analytic identities
now have [implemented effective counterparts](efg-computability-search.md#effective-implementations-with-explicit-representations).
The two existing history-policy examples compute transition, action, and
one-step laws as `FiniteLaw` values. Exact equalities recover each original
analytic kernel, and `stepLaw_eventMass` recovers all Boolean event queries.
The event-history example retains recorded actions; the state-history example
retains the initial state and incoming clock. Their original reverse
representation theorems remain intact.

The existing non-atomic example now executes
`RationalIntervals.probability` on finite lists of rational endpoint pairs.
Its recursive inclusion-exclusion accounts for overlaps, duplicates,
out-of-range endpoints, reversed intervals, and singleton events without
caller certificates. The result is proved to lie in `[0,1]` and to equal both
unit-interval volume and the probability of the corresponding coordinate-one
cylinder under the original complete state-path law.
`abstractProbability_eq` additionally preserves zero mass at terminal
information. The algorithm has exponential worst-case cost in the list
length and does not decide arbitrary real events.

The analytic identities remain **137**: the executable outputs use different
representations or an explicit finite event descriptor. No original
construction is deleted, renamed, or replaced by a supplied answer. Ten new
executable entry points are protected by the existing audit, and the
classification records their precise interpretation theorems. Both baselines
remain unchanged. All work stays in the three existing example modules;
there is no new Canonical/Frontend API or module.

Validation passes: stable and example builds, compiled regressions, finite-law
smoke execution, and `leanchecker` on all three changed modules. Direct
environment inspection confirms all ten protected entry points are
computable. Placeholder, API-growth, computability and governance checks pass;
the axiom audit checks 11,633 declarations in the same 227 modules with zero
forbidden axiom dependencies. Documentation references and `git diff --check`
pass.

## Existing-declaration implementation search — 2026-09-03

The [per-declaration search](efg-computability-search.md) reviews all 138
identities retained at R. Modifier-only compiler probes cover every original
identity, and the review distinguishes original-signature replacements from
different law representations, stronger effective inputs, and approximations.

`Examples.ObservedNonAtomicKernelBoundary.historyUnitAction` now constructs
its interval subtype using Mathlib's computable real `min` and `max`, keeping
the inequalities in proof fields. `historyUnitAction_eq_projIcc`, proved by
`rfl`, identifies the function with the original projection on every history,
including out-of-range terminal actions. No signature, hypothesis, or input
changes. Existing measurability and non-atomic path-law results still build.

The same 227-module environment audit reports **138 → 137** noncomputable
identities: exactly that removal, with zero additions. The remaining 35
nonzero modules contain 58 library and 79 example identities (69 analytic
definitions and 68 dependency-propagation declarations). Each has an explicit
candidate route and input/representation boundary in the classification.
These proposals are not completed replacements or impossibility theorems.
Both the declaration-identity and API-growth baselines remain byte-for-byte
unchanged from the starting worktree.

Validation passes: stable and example builds, finite-law smoke execution,
placeholder, API-growth, computability and governance checks, 17 audit-tooling
tests, and `leanchecker` on the changed module. The axiom audit checks 11,535
declarations in the same 227 modules with zero forbidden axiom dependencies.
Direct environment inspection confirms the changed function is computable;
local semantic checks cover the root, below-zero, interior, and above-one
terminal actions. Documentation references and `git diff --check` pass.

## R checkpoint — 2026-09-03

R extends the two existing opt-in finite Markov examples. For a `Chain n m`,
`autoBound` computes the maximum `(n+1)`-step survival row sum over every
`Fin n`, with zero for the empty domain; `autoCheck` submits that exact rational
certificate to `admissible`, and `autoSolve` invokes the retained solver. The
algorithm does no unbounded search, real comparison, noncomputable matrix inverse,
reachability pruning, strategy optimization, or EFG state quotient.

The finite-dimensional completeness proof tracks states having a positive
terminal route. Its positive-edge recurrence and monotonicity show that these
finite sets stabilize after at most `n` cardinality increases. Consequently,
any positive terminal route has a witness within `n` steps and the common
`n+1` survival row sums are all strictly below one exactly when every state
absorbs. `AbsorbsAll` is independently defined by `survival H i → 0`; the
semantic theorem proves `autoCheck = true ↔ AbsorbsAll`. Rejection formally
exhibits one state whose survival is one at every horizon, without claiming
that all starts fail.

`autoSolve_correct` proves the computed successful check makes `1-Q`
nonsingular, the actual solver returns, both Bellman equations have the unique
returned rational solutions, and those solutions equal the original first-hit
reward and actual `(r+1)` time integrals. The first-hit measure is normalized
and both observables are integrable. Terminal inputs retain reward and time
zero. Existing `solve` errors and caller-supplied certificate consumers remain.

Kernel regressions and compiled execution verify the following automatic
certificates and outputs, with no floating tolerance:

| Input | Computed `(k,c)` | Actual selected `(reward,time)` |
|---|---|---|
| `geometric` | `(2,1/4)` | `(7,2)` |
| `twoRewards` | `(2,1/4)` | `(1,2)`; terminal state one gives `(5,0)` |
| `delayed` | `(3,1/4)` | `(7,3)` |
| `terminalOnly`, `n=0,m=1` | `(1,0)` | Terminal `(7,0)` |
| `empty`, `n=0,m=0` | `(1,0)` | Successful pair of empty functions |
| `deterministic`, three steps | `(4,0)` | `(7,3)` |
| `tinyExit`, exit `1/1000000` | `(2,999998000001/1000000000000)` | `(7,1000000)` |
| `closedClass` | `(3,1)` | `absorptionBound` error |
| `noTerminals`, `n=1,m=0` | `(2,1)` | `absorptionBound` error |

The first three cases consume `autoSolve_integrals` and `autoSolve_correct`
to identify the actual integral values. `closedClass_absorption_boundary`
proves that state zero absorbs despite global rejection; state one has
survival identically one. The final validation record is in the R proof-audit entry.

## Q checkpoint — 2026-09-03

Q extends the existing opt-in `FiniteTruncation.lean` prototype. It preserves
M's `estimate`, `searchHorizon`, `search`, their hypotheses and exhaustion
semantics. There is no new module, root import, Canonical/Frontend API, or
consumer migration. R's automatic Markov certificate construction is not
implemented by this task.

`leastHorizon` executes `Nat.find` on the decidable rational predicate
`bound * Arena.noneMass policy current H ≤ tolerance`. `approximate` returns
that least `H` together with the existing `estimate` center and radius.
Runtime inputs are the executable terminal decision, finite rational complete
history policy, retained current history, rational payoff, rational bound and
positive rational tolerance. No horizon, budget, convergence rate, runtime
history enumeration, integral, real comparison, or classical witness selection
is an algorithm input. The proof-only inputs are countability of complete
histories, tolerance positivity and almost-sure terminal reachability under
the same actual history `Kernel.traj` used by J/M.

The termination proof is constructed from those assumptions:

- `measurableSet_no_hit`, `no_hit_antitone` and `iInter_no_hit` prove that
  `B_H = {path | ∀ t ≤ H, path t is nonterminal}` is measurable, decreases,
  and has nontermination as its intersection, even on raw nonabsorbing paths.
- `mass_tendsto_zero_of_ae_reaches` uses the actual trajectory's proved
  probability normalization, almost-sure reachability and Mathlib's
  `tendsto_measure_iInter_atTop`. M's `measure_no_hit` identifies the event
  probabilities with computed `noneMass` using proved almost-sure absorption.
- `radius_tendsto_zero` applies continuity of `ENNReal.toReal` at zero and
  rational-cast multiplication. `exists_radius_le` converts eventual strict
  real comparison with positive tolerance back to the exact rational
  inequality. This existence proof only justifies the terminating sequential
  search; it does not supply its runtime answer.
- `leastHorizon_spec` and `leastHorizon_eq_iff` establish success and
  minimality. `searchHorizon_eq_leastHorizon` and `search_eq_approximate`
  prove the old interfaces return exactly the same result when `budget > H`
  and return `none` when `budget ≤ H`.

`approximate_correct` reuses `estimate_correct` to prove
`|∫ U∞ dμ - center| ≤ radius` and `radius ≤ tolerance`. It keeps the original
`BoundedTerminalPayoffExtension` on the discrete complete-history model,
rational agreement with the original terminal payoff, a rational bound
dominating the extension's bound, and almost-sure reachability under the same
actual trajectory from the same incoming history. Legality, absorption,
normalization, marginals and integrability remain proved, not new caller
certificates. The mathematical target is still the existing
`eventualUtility` integral. Countability is used only in its semantic proof.

Kernel-checked numerical theorems and a guarded compiled `#eval` execute the
new algorithm on the following cases:

| Case | Actual `(H, center, radius)` | Semantic consumer |
|---|---|---|
| Fair repeat-or-stop, incoming length five, bound one, tolerance `1/8` | `(3, 7/8, 1/8)` | `approximation_integral`; minimality and budgets three/four via `approximation_budgets` |
| Already terminal incoming history | `(0, 1, 0)` | Original terminal payoff, reachability from its actual coordinate-zero law |
| Same process with terminal reward `-1` | `(3, -7/8, 1/8)` | `approximation_negative_integral` for that game's original eventual utility |
| Zero terminal reward and bound zero | `(0, 0, 0)` | `approximation_zero_integral` |
| Policy repeats until absolute history length three; start at length two | `(2, 1, 0)` | `approximation_absolute_time` contrasts the retained prefix with the root |
| Same clock-sensitive policy from the root | `(4, 1, 0)` | Exact comparison with the preceding case |

The existing geometric `survival` and `no_finite_bound` results remain:
every finite horizon has positive unfinished mass. `zero_tolerance_budget`
also checks the old interface at tolerance zero: every finite budget misses
the active geometric process, while the terminal current succeeds at horizon
zero. The new positive-tolerance guarantee does not assert a runtime bound,
finite expected hitting time, success at zero tolerance, exact arbitrary-real
expectation, or termination without the stated process premise.

Final validation passes: `lake build`, `lake build EconCSLib.Examples`,
`lake env lean tests/FiniteLawSmoke.lean`, placeholder, API-growth,
computability, axiom and governance checks, and
`lake env leanchecker EconCSLib.Examples.ExtensiveGame.FiniteTruncation`.
The audits using `--skip-build` first verify artifact freshness with Lake's
rehashed dependency traces. The exact starting/final identity comparison
covers the same **227 modules** and reports **138 → 138 identities**, with
**zero additions and zero removals**. The full axiom audit covers **11,448
declarations**, with **zero forbidden axiom dependencies**. Direct
`Lean.isNoncomputable` queries return false for both new algorithms and the
three new regression data definitions. The modified module adds no warnings;
pre-existing dependency warnings remain.

Both baseline files are byte-for-byte unchanged from the task's starting
worktree. The classification retains P's snapshot in its history, records Q,
protects the two executable declarations and renews only the reviewed
`FiniteTruncation` regression evidence. Documentation links and
`git diff --check` pass. All pre-existing worktree changes are preserved;
no commit or baseline reset was made.

## G checkpoint — 2026-09-03

G is complete; H–P have not been executed by this checkpoint. Full rebuilt
environment scans before and after the change cover the same **219 modules**:
**140 → 138 noncomputable identities**, with exactly two removals and no
additions. The remaining 35 nonzero modules contain 58 library identities and
80 example identities; `FiniteLaw` remains at zero. The unchanged
342-identity baseline now has 204 absent identities.

| Existing example | Before → after | Implementation and preserved semantics |
|---|---:|---|
| `ObservedMeasurableKernelAlmostSureOutcomeBoundary` | 2 → 1 | `Node` retains `DecidableEq` and `Countable`; the latter now proves injectivity of `active ↦ 0`, `terminal ↦ 1` inside `Prop`, eliminating the deriving-generated noncomputable helper. |
| `ObservedNonAtomicKernelBoundary` | 16 → 15 | `halfAction` constructs `((1 / 2 : ℚ) : ℝ)` in the unit interval without `noncomputable`; `halfAction_coe` proves equality with the original real `1/2`. |

Neither change adds runtime inputs or mathematical hypotheses. Countability
is still proof data, not an encoder extracted by the executor. The only
computational value changed is a closed exact rational midpoint cast to `ℝ`;
this is not an algorithm for arbitrary real division, comparison, or numeric
approximation. All history/action countability and measurability consumers
remain available. The non-atomic event's properness proof and volume calculation
now use the midpoint equality instead of relying on real-division definitional
equality. The existing lower-half cylinder still has probability exactly
`ENNReal.ofReal (1 / 2 : ℝ)` and is nonempty and proper.

The retained classification has 70 analytic definitions, 68 dependency
propagations, and no proof-generated helpers. Its live snapshot, 76 cleared
identities, and 15 regression sources include G; `review_history` preserves the
original A–F snapshot. The `historyModel` evidence range moved with the new
instance, but its source text and hash are unchanged. Both example sources
were reviewed and added as semantic regression evidence. The 184 protected
zero modules, audit scope, API-growth baseline, and computability baseline are
unchanged. No module or root import was added.

Validation passed: `lake build`, `lake build EconCSLib.Examples`,
`lake env lean tests/FiniteLawSmoke.lean`, placeholder/API-growth/full
computability/governance checks, and the full axiom audit (**10,548 declarations,
219 modules, zero forbidden dependencies**), and `git diff --check`. Direct
`Lean.isNoncomputable` queries confirm that `instCountableNode` and `halfAction`
are both unmarked. Kernel replay covers both changed example modules.
Existing build warnings are retained; G adds no new unchecked
proof or axiom. The almost-sure example still requires its supplied analytic
profile and finite-marginal certificate; G does not construct them. The A–F
records below are historical and their counts have not been rewritten.

## H checkpoint — 2026-09-03

H implements total finite stochastic-tree evaluation in the existing opt-in
`EconCSLib/Examples/ExtensiveGame/StochasticTreeCompilation.lean` module, under
`Examples.ExtensiveGame.StochasticTreeCompilation`. These are proved example
prototypes, not additions to the frozen Canonical/Frontend API. I–P remain
unexecuted.

`requiredFuel` structurally computes one for a leaf and one plus the maximum
child bound at a player or chance node. `Finset.univ` enumerates the existing
`Fin (arity + 1)` child domain. Both `requiredFuel_child_lt_player` and
`requiredFuel_child_lt_chance` prove a strict decrease for **every** child,
including zero-mass chance occurrences. No depth certificate, global player
enumeration, choice operation, or additional finiteness assumption is needed.

`totalExpectedPayoff` takes the existing tree, policy, occurrence path, and
player, and returns the structurally evaluated real payoff. Player choices
append their occurrence index to the incoming path; chance evaluation sums
the constructor's exact rational atom weights against child payoffs. The
theorem `totalExpectedPayoff_eq_expectedPayoffWithFuel` proves equality with
the existing bounded evaluator for every policy/path/player whenever
`requiredFuel tree ≤ fuel`. The bound is computed from the tree, and this
inequality is discharged by reflexivity when that bound is used as fuel.
No former conclusion is replaced by a caller-supplied certificate.

The existing bounded definitions, signatures, compiler, and all prior
theorems are unchanged. In particular, fuel zero still returns zero even at
a leaf. Only the overstrong `expectedPayoffAtFuel` comment was corrected:
finite child enumeration does allow computation of a sufficient horizon.
Real payoffs remain mathematical inputs; finite real arithmetic is not an
algorithm for arbitrary-real comparison or effective numerical approximation.
No integral or infinite-path law is constructed by H.

The new regressions use root weights `1/2`, `1/3`, and `1/6` with leaves at
depths one, two, and three. The same decision subtree appears at paths `[1]`
and `[2, 0]`, where the executable policy chooses payoffs two and minus four.

| Checked case | Result |
|---|---|
| Leaf bound and nonzero leaf payoff | fuel one; total payoff seven; bounded fuel zero/one gives zero/seven |
| Unequal-depth tree | computed bound four |
| Full expectation from the empty path | `5/2` |
| Existing bounded evaluation at fuel three | `19/6`, because the deepest negative payoff is truncated |
| Existing root evaluator at the computed bound | `5/2`, by the general sufficiency theorem |
| Same tree with incoming prefix `[7]` | `7/2`, demonstrating retained occurrence history |

The numerical equalities are kernel-checked proofs. A guarded `#eval` also
executes the leaf/tree bounds and the two finite occurrence choices, yielding
`(1, 4, 0, 1)` without inspecting arbitrary real values.

No module, import, or root entry was added. A future frontend promotion would
require an explicit freeze decision for the two algorithms and their
sufficiency theorem; the two child-bound lemmas can remain internal. H does
not perform that promotion or require a consumer migration.

The full rebuilt audit covers the same **219 modules**, with the exact same
**138 noncomputable identities before and after**: no removal and no addition.
The 35 nonzero modules still own 58 library and 80 example identities,
classified as 70 analytic definitions and 68 dependency propagations.
`FiniteLaw`, the stochastic-tree owner, its compiler, and the extended example
remain at zero. Direct `Lean.isNoncomputable` queries return false for
`requiredFuel`, `totalExpectedPayoff`, and `occurrencePolicy`.

The classification preserves the G snapshot in `review_history` and records
H as the current stage. The reviewed example is the sixteenth regression
source; the 184 protected zero modules, 76 cleared identities, retained
declaration evidence, and both existing baselines are unchanged. The
342-identity computability baseline still has 204 absent identities.

Validation passed: `lake build`, `lake build EconCSLib.Examples`,
`lake env lean tests/FiniteLawSmoke.lean`, placeholder/API-growth/full
computability/governance checks, and the full axiom audit (**10,595
declarations, 219 modules, zero forbidden dependencies**). Both modified
Lean modules pass `lake env leanchecker`; `git diff --check` passes. The
example adds no warning; the existing bounded evaluator's unused-`arity`
warning and other pre-existing build warnings remain.

The additional Mathlib-style `check_distillation.py` passed.
`check_benchmark.py` stopped at its preservation gate on the pre-existing root
`AGENTS.md` modification, as at the earlier checkpoint. That unrelated change
was preserved, so the full benchmark is not reported as passing.

## I checkpoint — 2026-09-03

I adds the opt-in prototype
`EconCSLib/Examples/ExtensiveGame/FiniteLawIntegral.lean`, under
`Examples.ExtensiveGame.FiniteLawIntegral`, and registers it in
`EconCSLib.Examples`. The new module is included automatically in both complete
environment audits. It is not imported by `EconCSLib.lean`, and no governed
Canonical/Frontend module or declaration was added. J–P remain unexecuted.

The existing `FiniteLaw.expectRat` remains the numerical algorithm. I proves
its equality with the Bochner integral of a rational utility cast to real
values, against the **actual finite weighted Dirac expression** already used
by `KernelArena.toMeasurable`. The file-local `μ[atoms]` notation expands to
the list fold of `(weight : ENNReal) • Measure.dirac outcome`, starting at zero.
It is notation in theorem statements and proofs, not a new runtime measure
constructor, supplied measure, or assumed integral certificate.

| Prototype theorem | Guarantee and assumptions |
|---|---|
| `measure_eventMass` | The measure of a measurable Boolean event equals its executable `FiniteLaw.eventMass`, cast to `ENNReal`. Event measurability permits evaluation of each Dirac measure. |
| `isProbabilityMeasure` | The finite Dirac expression is normalized, proved from the existing atom-weight normalization field on any measurable outcome space. |
| `integrable` | Every real-valued utility is integrable against the finite atom measure when singletons are measurable. No global bound or global measurability of that utility is assumed. |
| `integral_eq_expectRat` | Under the same measurable-singleton condition, the rational utility's integral equals `(law.expectRat utility : ℝ)`. |
| `measure_eq_of_equivalent` | `FiniteLaw.Equivalent` implies equality of interpreted measures on any measurable outcome space. Classical membership decisions are used only inside this proof. |
| `integral_eq_of_equivalent` | Equivalent presentations have equal rational-utility integrals on any measurable outcome space, by equality of their measures. |

Neither the outcome type nor its sigma algebra must be finite or countable.
Measurable singletons suffice for pointwise Dirac integration and hence finite
additivity of the integral; the theorem constructs the integrability proof.
The event, normalization, and equivalence results do not require measurable singletons.
No converse from measure equality to `Equivalent` is asserted for an arbitrary
sigma algebra, which may not distinguish the outcomes.

The regression uses the infinite carrier `ℕ` with its discrete sigma algebra.
Its atom list is `[(2, 1/4), (7, 1/3), (2, 1/4), (99, 0), (11, 1/6)]`;
the equivalent reordered and merged list is
`[(11, 1/6), (2, 1/2), (7, 1/3)]`. They are formally unequal as sparse
representations but equivalent for every rational observable and equal as
measures. The utility at states two, seven, and eleven is respectively
`-3/2`, `5/2`, and `-1`; off-support it is `state + 1000`.

Kernel-checked results give expectation and integral **`-1/12`** for both
presentations, duplicate-state probability **`1/2`**, and zero-weight-state
probability **zero**, despite that state's utility being 1099. Guarded `#eval`
executes both rational expectations and both event-mass calculations.

The finite-law core, all existing interfaces and hypotheses, and all prior
consumers are unchanged. No caller acquires a new certificate obligation.
The six general theorems remain example prototypes; promotion needs a
separately reviewed downstream analytic home. No measure or integral import
was added to `FiniteLaw/Core.lean`.

The full rebuilt audit expands from **219 to 220 modules** and retains exactly
the same **138 noncomputable identities**: no additions or removals. The 35
nonzero modules still contain 58 library and 80 example identities, classified
as 70 analytic definitions and 68 dependency propagations. The new module and
`FiniteLaw` audit at zero. Direct `Lean.isNoncomputable` queries return false
for `FiniteLaw.expectRat`, `splitLaw`, `mergedLaw`, and `payoff`.

The classification preserves the H snapshot in `review_history`, adds the new
module to the protected zero set (**185 modules**), and records this source as
the seventeenth execution regression. All prior declaration and regression
evidence, the 76 cleared identities, and both baselines are unchanged. The
342-identity computability baseline still has 204 absent identities.

Validation passed: `lake build`, `lake build EconCSLib.Examples`,
`lake env lean tests/FiniteLawSmoke.lean`, and the placeholder, API-growth,
full computability, and governance checks. The full axiom audit covers
**10,631 declarations in 220 modules, with zero forbidden dependencies**.
`git diff --check` passes. The new module adds no warning.

Kernel replay passed for the new module using `lake env leanchecker
EconCSLib.Examples.ExtensiveGame.FiniteLawIntegral`. The import-only
`EconCSLib.Examples` aggregate also passed the pinned checker's exact
`replayFromImports` routine, invoked from a temporary `import LeanChecker`
driver after initializing Lean's search path. The CLI's aggregate-prefix
invocation was stopped after it selected an obsolete cached
`EconCSLib.Examples.«CentipedeGame 3»` module with no current source; that
invocation is not reported as passing. Existing artifacts were preserved, and
both complete environment audits include all 220 current source modules.

The additional Mathlib-style `check_distillation.py` passed.
`check_benchmark.py` again stopped at its preservation gate on the pre-existing
root `AGENTS.md` modification. That unrelated change was preserved, so the full
benchmark is not reported as passing.

## J checkpoint — 2026-09-03

J adds the opt-in prototype
`EconCSLib/Examples/ExtensiveGame/FiniteExecutionIntegral.lean`, under
`Examples.ExtensiveGame.FiniteExecutionIntegral`, and registers it in
`EconCSLib.Examples`. It is outside the frozen Canonical/Frontend surface and
the stable root closure. A–J now comprise ten completed steps of the sixteen
A–P steps; K–P remain unexecuted.

`stoppedExpectedPayoff` takes an arena with an executable terminal decision,
an executable `StochasticHistoryPolicy`, a current complete history, a natural
number horizon, and a rational history payoff. It uses the existing
`stochasticHistoryLawFrom` and `FiniteLaw.expectRat`. Only histories terminal
at the selected horizon contribute their payoff; every nonterminal result
contributes zero. A terminal initial history contributes its payoff even at
horizon zero. The general terminal-continuation theorem proves absorption for
every remaining horizon.

The semantic conclusion is against the **actual `Kernel.traj` expression**
driven by `policy.toKernelPolicy.toMeasurable.pathStepKernel`, initialized at
the supplied current history. The local `historyPath(...)` macro abbreviates
this expression only inside statements and proofs. It creates no analytic
constructor declaration, and callers supply no complete path law, target
marginal equality, integrability certificate, or path realization equation.

`historyLaw_eq_coordinate` identifies every analytic coordinate with the
weighted Dirac interpretation of the executable complete-history law. Its
proof reuses the existing horizon inductions in
`Arena.historyKernelArena_stateLawFrom_eq_stochasticHistoryLawFrom` and
`KernelArena.Policy.toMeasurable_endpointMeasure`, and the coordinate recursion
in `StatePath`. Their base case is a Dirac initial history; terminal branches
absorb; nonterminal branches use the actual rational action distribution and
deterministic history append. `PathExecution.nonempty` supplies the analytic
construction inside the proof, with its fields identified with `Kernel.traj`
and its pushforwards. Eliminating this `Nonempty` into a theorem introduces no
runtime measure selection. The older supplied-law realization bridge retains
its existing role and signature.

`integrable_historyPayoff` proves finite-horizon integrability for any real
history observable, including unbounded off-support values.
`integral_historyPayoff` combines the coordinate equality, change of variables,
and I's finite-law integral theorem. `integral_stoppedPayoff` applies it to the
terminal-gated rational observable. Finally, `integral_stoppedUtility` identifies
the existing `TerminalPayoffExtension.stoppedUtility` on the discrete observed
history model with that computation. Its payoff compatibility hypothesis says
only that the rational payoff casts to the same base terminal payoff; auxiliary
off-terminal extension values are unrestricted. The regression constructs
this extension and proves compatibility by reflexivity.

The complete-history sigma algebra is discrete and the path sigma algebra is
its countable product. There is no ambient `Fintype` or `Countable` premise,
uniform termination bound, or global payoff bound. The theorem applies to the
existing finite-support action-policy regime and its history-kernel embedding.
It does not establish the correspondence for arbitrary non-atomic policies or
assert that arbitrary history policies satisfy an observed information
partition. All existing general analytic interfaces and consumers are
unchanged. The finite-law core and I's implementation are unchanged.

The regression has three root actions with weights `1/2`, `1/3`, and `1/6`.
Action zero reaches the terminal world state immediately; actions one and two
visit the same intermediate world state and then the same terminal world
state. The existing `Arena.unfoldFrom` preserves the actual occurrences and
makes the history-dependent payoff an ordinary payoff on the unfolded base
state. The direct route pays `3/2`; both longer routes pay `-3`. All nonterminal
world states have auxiliary payoff 17. Thus the source state-payoff interface
is respected: routes share a compact world endpoint but have distinct unfolded
states and complete action histories.

| Kernel-checked regression | Result |
|---|---|
| Full two-step atom list | Three complete histories with weights `1/2`, `1/3`, `1/6`; both middle occurrences remain present |
| Same compact endpoint, different routes | Direct payoff `3/2`; longer-route payoff `-3` |
| Horizon zero | Auxiliary payoff 17, stopped expectation and analytic integral zero |
| Horizon one | Stopped expectation and existing stopped-utility integral `3/4`; only the early branch contributes |
| Horizon two | Stopped expectation and existing stopped-utility integral `-3/4` |
| Already terminal direct continuation | Payoff `3/2` for every remaining horizon |

The numerical proofs use ordinary kernel reduction (`decide +kernel`),
rational normalization, and the general integral theorem. A guarded `#eval`
also executes the horizon-zero/one/two expectations, an absorbed continuation
at horizon five, and both longer-route payoffs. No exported proof uses
`native_decide`.

The full rebuilt audit expands from **220 to 221 modules**, retaining exactly
the same **138 noncomputable identities** with no additions or removals. The
35 nonzero modules still contain 58 library and 80 example identities,
classified as 70 analytic definitions and 68 dependency propagations.
`FiniteLaw` and the new module audit at zero. Direct `Lean.isNoncomputable`
queries return false for `stoppedExpectedPayoff`, `rootLaw`, `policy`, `payoff`,
and `payoffExtension`.

The classification preserves I in `review_history`, adds the new module to
the protected zero set (**186 modules**), and adds the eighteenth execution
regression. All prior declaration evidence, the 76 cleared identities, prior
regression evidence, and both baselines remain unchanged. The 342-identity
computability baseline still has 204 absent identities.

Validation passed: `lake build`, `lake build EconCSLib.Examples`,
`lake env lean tests/FiniteLawSmoke.lean`, and the placeholder, API-growth,
full computability, and governance checks. The full axiom audit covers
**10,718 declarations in 221 modules, with zero forbidden dependencies**.
The new module passes `lake env leanchecker` and adds no warning. The aggregate
passes the pinned checker's exact `replayFromImports` routine, using the
temporary driver described at I to avoid the CLI's cached-module prefix
discovery. Both complete audits retain all 221 current source modules.
`git diff --check` passes. No checker implementation or existing consumer
signature changed.

## K checkpoint — 2026-09-03

K adds the opt-in prototype
`EconCSLib/Examples/ExtensiveGame/FiniteConditionalContinuation.lean`, under
`Examples.ExtensiveGame.FiniteConditionalContinuation`, and registers it in
`EconCSLib.Examples`. A–K now comprise eleven completed steps of A–P;
L–P remain unexecuted. The new module is outside the frozen Canonical/Frontend
surface and the stable root closure.

`conditionalLaw` takes an executable stochastic history policy, a finite prior
on complete histories, an executable observation and observation equality
decision, an observed value, and a remaining horizon. It calls the existing
`conditionOnFiber`, then binds `stochasticHistoryLawFrom` from every posterior
history. `conditionalPayoff` applies `expectRat` and returns `Option ℚ`.
For an observation at time `t`, the prior is the existing executor's law at
`t`. No global state/history enumeration or history equality decision is
needed. Terminal decisions, action laws, observations and rational payoffs are
explicit computational inputs; the concrete regression implements all of them.

`expectRat_conditionOnFiber` proves Bayes' formula for every rational
observable, extending the existing point-mass formula without requiring
history equality. `conditionalLaw_exists` constructs a normalized result
at every positive observation. `conditionalPayoff_eq_none_iff` proves that
exactly zero observation mass returns `none`, distinct from `some 0`.
No off-path posterior is selected.

`jointExecution` records both the actual observation-time history and the
final complete history. `jointExecution_snd` recovers the original executor
at `t + H` exactly, using its existing additive-horizon theorem.
`condition_joint` and `conditionalLaw_joint` prove that conditioning this
joint execution and projecting the final coordinate is equivalent to continuing
from the posterior. The conclusion uses `FiniteLaw.Equivalent`, so it does not
confuse sparse presentation order, duplicate occurrences, or zero-weight atoms
with distributional differences. Both zero- and positive-mass cases are proved.
The same policy receives each actual retained history; its absolute length and
action memory are never replaced with a world endpoint or a local clock.

The analytic correspondence is limited to this finite window on discrete
complete histories. `jointExecution_integral` interprets every rational
observable of the two recorded histories as an iterated integral: the prior
finite history measure, followed by J's actual `Kernel.traj` continuation from
that middle history. `conditionalPayoff_analytic` proves the normalized Bayes
integral formula with the actual continuation integral in the numerator.
`conditionalPayoff_joint_integral` proves equality of the optional computed
value with integration against the computed joint posterior, including `none`.
I supplies the finite atomic integral correspondence, and J supplies the actual
history-trajectory integral theorem. Their finite-support arguments discharge
integrability; no supplied path law, target integral, or realization certificate
is an input to these results.

This does not instantiate the existing general `BoundedPathUtility.ConditionalEvaluation`
class for arbitrary analytic profiles or utilities: that interface conditions on
canonical complete prefixes, while this prototype conditions a finite prior on
an observation fiber. Its existing constructors, hypotheses and consumers,
including independent off-path beliefs, are unchanged. No equality with an
arbitrary regular conditional kernel or arbitrary infinite-path utility is
asserted. The payoff here is an explicit finite-window history observable;
a stopped observable can explicitly gate nonterminal histories to zero.

The regression starts from a nonempty history ending at `fork`. Its chance
list is `[(0, 1/4), (1, 1/4), (0, 1/4), (2, 1/4), (1, 0)]`.
All routes merge at `middle`. Observation zero groups routes zero and one;
observation one selects route two; observation two is impossible. The policy
at `middle` reads both the retained fork action and absolute history length.
The first hidden route yields six, the second minus three, and their shared
observation has probability `3/4`.

| Kernel-checked regression | Result |
|---|---|
| Hidden histories share endpoint and observation | Continuation payoffs six and minus three |
| Posterior route weights and normalization | `2/3`, `1/3`, total one |
| Positive conditional payoff and analytic Bayes integral | Three |
| Impossible observation | `none` |
| Identically zero payoff on a positive observation | `some 0` |
| Zero continuation horizon at nonterminal middle | `some 17` |
| Same compact fork with the incoming step removed | `some (-3)` |
| Other positive observation | `some (-3)` |
| Further continuation after termination | `some 3` |

The numerical theorems use `decide +kernel`. A guarded `#eval` executes the
positive, impossible and clock-offset cases. No exported proof uses
`native_decide`. New capabilities remain example prototypes; promotion needs
a separate decision about their downstream home and minimum public surface.
No existing consumer signature, finite-law implementation or checker changed.

The full rebuilt audit expands from **221 to 222 modules** and retains exactly
the same **138 noncomputable identities**, with no additions or removals.
The 35 nonzero modules still own 58 library and 80 example identities,
classified as 70 analytic definitions and 68 dependency propagations.
`FiniteLaw` and the new module remain at zero. Direct `Lean.isNoncomputable`
queries return false for `conditionalLaw`, `conditionalPayoff`, `jointExecution`,
`route`, `policy`, `forkLaw`, `observe`, and `payoff`.

The classification preserves J in `review_history`, adds the new module to
the protected zero set (**187 modules**), and adds the nineteenth execution
regression. All existing declaration and regression evidence, the 76 cleared
identities and both baseline files remain unchanged. The 342-identity
computability baseline still has 204 absent identities.

Validation passed: `lake build`, `lake build EconCSLib.Examples`,
`lake env lean tests/FiniteLawSmoke.lean`, and the placeholder, API-growth,
full computability and governance checks. The full axiom audit covers
**10,838 declarations in 222 modules, with zero forbidden dependencies**.
The new module passes `lake env leanchecker` and adds no warning. The
import-only aggregate passes the pinned checker's exact `replayFromImports`
routine from a temporary `import LeanChecker` driver, as at I and J; this avoids
CLI prefix discovery of unrelated stale cached example names. Existing build
warnings and artifacts are preserved. `git diff --check` passes.

## L checkpoint — 2026-09-03

L adds the opt-in prototype
`EconCSLib/Examples/ExtensiveGame/FiniteCompletePath.lean`, under
`Examples.ExtensiveGame.FiniteCompletePath`, and registers it in
`EconCSLib.Examples`. A–L now comprise twelve completed steps of A–P;
M–P remain unexecuted. No Canonical/Frontend declaration or stable-root import
was added, and no existing consumer signature changed.

`prefixAt` structurally reads a complete history's absolute prefix, holding
its endpoint after exhaustion. `completePaths` runs the existing
`stochasticHistoryLawFrom` to the supplied horizon, then maps each result
to this coordinate function with offset `current.2.length`. Coordinate zero
is therefore the actual incoming history. Runtime inputs are the arena,
executable terminal decision, finite rational history policy, current history,
and horizon. No global enumeration, history/path equality, infinite array,
or proof-extracted witness is used.

Correctness assumes only that every positive atom at the horizon is terminal.
The sparse list can retain zero-weight nonterminal histories, but they are
never bundled as legal complete plays. `completePaths_legal` identifies each
positive path with `prependHistory` followed by terminal `stutter`, shifted
by the retained incoming length. `completePaths_legalTransition` additionally
proves that every nonterminal step uses an action with positive policy mass.
The history-length bound proves termination at the supplied horizon.

`completePaths_marginal` proves `FiniteLaw.Equivalent` with the original
executor at every natural-number coordinate, including both `n ≤ H` and
`n > H`. Its induction preserves actual action occurrences and terminal
absorption. The finite law is normalized by construction through the existing
executor and `map`; no normalization certificate is supplied.

`measure_finiteMarginal` interprets the constructed finite path law as its
actual weighted Dirac measure. It works on any measurable history space.
With measurable singletons, `exists_pathLaw` constructs a `ProbabilityMeasure`
equal to that explicit expression and proves all the certificates consumed
by `Arena.pathLaw`: finite marginals, almost-sure positive-policy transition
legality, canonical complete-play legality, termination at the bound, and
terminal absorption. The countable coordinate product then also has measurable
singletons; no countability assumption on histories is needed. The concrete
`regression_pathLaw` consumes this result on discrete complete histories.
Measures occur in statements and proofs, while finite data and coordinate
computation remain executable. No supplied measure or target realization
equation is an input, and no uniform termination condition was added to the
general infinite-execution interfaces.

The regression starts from a one-action incoming history at a fork. Its
chance list is `[(0, 1/2), (1, 1/3), (0, 1/6), (2, 0)]`. Action zero terminates
immediately, action one terminates after a second step at the same world
endpoint, and action two enters a loop with actions available forever.
The two-step positive-atom termination bound is proved, while the retained
zero-weight loop history is proved nonterminal and its constant continuation
is proved **not** to be a legal complete play.

Kernel-checked coordinate lists begin at the fork and distinguish the two
termination times. The exact expected absolute history length is **7/3** at
both coordinates two and one hundred. A separate horizon-zero regression
at an already terminal nonempty history gives the constant path. Guarded
`#eval` computes the weighted lengths `[(2, 1/2), (3, 1/3), (2, 1/6), (3, 0)]`
and their rational expectation. No exported proof uses `native_decide`.

The rebuilt audit expands from **222 to 223 modules** and retains the same
**138 noncomputable identities**, with no additions or removals. The 35
nonzero modules still own 58 library and 80 example identities, classified
as 70 analytic definitions and 68 dependency propagations. The new module
and `FiniteLaw` remain at zero. Direct environment queries mark `prefixAt`,
`completePaths`, `policy`, and `forkLaw` as computable.

The classification preserves K in `review_history`, adds the new module to
the protected zero set (**188 modules**), and records the twentieth execution
regression. All prior declaration and regression evidence, the 76 cleared
identities, and both baseline files remain unchanged. The 342-identity
computability baseline still has 204 absent identities.

Validation passed: `lake build`, `lake build EconCSLib.Examples`,
`lake env lean tests/FiniteLawSmoke.lean`, and the placeholder, API-growth,
full computability, and governance checks. The full axiom audit covers
**10,962 declarations in 223 modules, with zero forbidden dependencies**.
The new module passes `lake env leanchecker` and adds no warning. The
import-only aggregate passes the pinned checker's exact `replayFromImports`
routine from a temporary `import LeanChecker` driver, avoiding prefix discovery
of unrelated obsolete cached example names. Existing warnings and artifacts
are preserved. `git diff --check` passes.

## M checkpoint — 2026-09-03

M adds the opt-in prototype
`EconCSLib/Examples/ExtensiveGame/FiniteTruncation.lean`, under
`Examples.ExtensiveGame.FiniteTruncation`, and registers it in
`EconCSLib.Examples`. A–M now comprise thirteen completed steps of A–P;
N–P remain unexecuted. No Canonical/Frontend declaration or stable-root import
was added, and no existing consumer signature changed.

`estimate` returns a rational center and nonnegative rational radius. The
center uses J's `stoppedExpectedPayoff`, hence the existing finite history
executor and `FiniteLaw.expectRat`; nonterminal coordinates contribute zero.
The radius is the supplied rational terminal bound times `Arena.noneMass`.
Runtime inputs are the executable terminal decision, finite rational history
policy, actual current complete history, rational payoff, bound, and horizon.
There is no global enumeration or runtime countability encoder.

`searchHorizon` tests horizons `0, ..., budget - 1` using exact rational
comparison. `search` returns `some (horizon, center, radius)` or `none`.
The budget counts candidate horizons, including zero; it does not bound the
number of atoms generated within each candidate. The soundness theorems prove
that a returned horizon lies inside the budget and its radius meets the
tolerance. `searchHorizon_eq_none_iff` characterizes exhaustion by failure of
exactly the tested inequalities. In particular, exhaustion does not imply
nontermination. Positive tolerances are supported, and the same soundness
statements also hold at tolerance zero; no arbitrary budget is promised to
succeed and no rate of convergence is inferred.

The semantic target is the **actual `Kernel.traj` history law used by J** and
the existing `BoundedTerminalPayoffExtension.eventualUtility`. The local
`historyPath(...)` macro spells out that measure expression with the discrete
history sigma algebra; it adds no runtime measure constructor or assumed law.
`measure_unfinished` uses J's coordinate theorem and I's finite event-mass
theorem. `ae_legal` uses the trajectory's finite-prefix/next-coordinate joint
law and the actual weighted Dirac one-step interpretation to prove
positive-policy transition legality. `ae_completePlay` derives the existing
canonical complete-play certificate, and `ae_absorbing` proves constancy after
every terminal visit. Thus `measure_no_hit` identifies `noneMass` with
`Pr(T > H)`, expressed as no terminal coordinate through `H`.

`eventual_eq_stopped_of_terminal` proves that an absorbing path already
terminal at `H` has no truncation error. At an unfinished coordinate stopped
utility is zero, so `truncation_pointwise` bounds the difference by **M** on
that event and zero elsewhere. This is why the theorem does not require the
generic **2M** bound for a difference of two arbitrary bounded utilities.
`integrable_eventual` derives measurability and integrability from the existing
stopped-utility convergence theorem under almost-sure terminal absorption.
`estimate_correct` combines these results with J's stopped integral and the
computed dominating-observable integral to prove
`|E[U∞] - center| ≤ M * q_H`. `search_correct` proves that every successful
returned interval contains this actual eventual expectation.

The automatic legality and integral-correctness theorems currently assume
**countable discrete complete histories** to make the varying history relation
measurable. This is a proof-only condition, not an algorithm input. The
algorithms, finite-marginal mass correspondence and finite dominating integral
do not require countability; the pointwise and eventual-integrability lemmas
also work on general measurable history models. Correctness additionally
requires a rational bound dominating the extension's terminal bound,
agreement of the rational payoff with the original base payoff at terminal
histories, and almost-sure terminal reachability under the actual law.
Absorption, legality, normalization, marginal equality and integrability are
proved rather than supplied. No uniform termination bound or L-style bounded
termination premise is used. Arbitrary non-atomic policies and automatic
uncountable-history legality remain outside this prototype.

The regression reuses the existing fair repeat-or-stop arena, history policy,
and general survival proof, giving `q_H = (1/2)^H` at every retained repeat
offset. Vanishing mass proves almost-sure reachability for the actual law,
without the older example's supplied analytic profile or marginal certificate.
Positive mass at every finite horizon rules out a deterministic termination
bound. The existing base terminal payoff remains one, while the auxiliary
nonterminal extension value is deliberately 17.

| Kernel-checked regression | Result |
|---|---|
| Active history, horizon zero | Center zero, radius one; auxiliary 17 is ignored |
| Tolerance `1/8`, three candidate horizons | `none`, despite almost-sure termination |
| Tolerance `1/8`, four candidate horizons | `some (3, 7/8, 1/8)` |
| Five retained repeat actions before the same search | `some (3, 7/8, 1/8)` |
| Already terminal nonempty history, one candidate | `some (0, 1, 0)` |
| Already terminal history, zero candidates | `none` |
| Returned successful interval | Actual eventual expectation is within `1/8` of `7/8` |

The numerical equalities use `decide +kernel`; a guarded `#eval` executes the
exhausted, successful and already terminal cases. No exported proof uses
`native_decide`. The existing general analytic interfaces and all I–L sources
remain unchanged. Promotion of the algorithms and correctness theorems needs
a separate review of their downstream public home and minimum API surface.

The full rebuilt audit expands from **223 to 224 modules** and retains exactly
the same **138 noncomputable identities**, with no additions or removals.
The 35 nonzero modules still own 58 library and 80 example identities,
classified as 70 analytic definitions and 68 dependency propagations.
The new module and `FiniteLaw` remain at zero. Direct environment queries
mark `estimate`, `searchHorizon`, `search`, the regression payoff and extension,
the reused `fairHistoryPolicy`, and `Arena.noneMass` as computable.

The classification preserves L in `review_history`, adds the new module to
the protected zero set (**189 modules**), and records the twenty-first
execution regression. All previous declaration and regression evidence, the
76 cleared identities, and both baseline files remain unchanged. The
342-identity computability baseline still has 204 absent identities.

Validation passed: `lake build`, `lake build EconCSLib.Examples`,
`lake env lean tests/FiniteLawSmoke.lean`, and the placeholder, API-growth,
full computability, and governance checks. The full axiom audit covers
**11,032 declarations in 224 modules, with zero forbidden dependencies**.
The new module passes `lake env leanchecker` and adds no warning. The
import-only aggregate passes the pinned checker's exact `replayFromImports`
routine from a temporary `import LeanChecker` driver, avoiding CLI prefix
discovery of obsolete cached modules. Existing warnings and artifacts are
preserved. `git diff --check` passes.

## N checkpoint — 2026-09-03

N adds the opt-in prototype
`EconCSLib/Examples/ExtensiveGame/FinitePureNash.lean`, under
`Examples.ExtensiveGame.FinitePureNash`, and registers it in
`EconCSLib.Examples`. A–N now comprise fourteen completed steps of A–P;
O–P remain unexecuted. No existing consumer signature, stable-root import,
Canonical/Frontend declaration, or baseline changes in this step.

`strategicForm` uses the original `ObservedGame.PureStrategy` family directly.
It embeds each pure choice as a Dirac behavioral action, retains the declared
finite rational chance kernel, executes `Arena.stochasticHistoryLawFrom`, and
evaluates `FiniteLaw.expectRat`. A terminal history contributes the game's
original rational payoff; an unfinished history contributes zero. Thus the
general checker concerns the specified stopped horizon. An insufficient
horizon can change the equilibrium answer.

`check` enumerates players and the dependent finite function tables and calls
the existing `isNashEq`. `check_iff` reuses `isNashEq_iff` to prove soundness
and completeness for every original EFG pure unilateral deviation. The
profile and deviation types are definitionally the original EFG types; no
assumed surjectivity, outcome equality, or Nash certificate is used.
An information coordinate is one represented information set, so two
histories in that set cannot choose different abstract actions. Distinct
coordinates in an occurrence presentation remain distinct.

Runtime inputs are executable player enumeration and equality, represented
information enumeration and equality, legal-action enumeration, terminal
decisions, the original game/profile, current complete history, and horizon.
The generic prototype does not derive these enumerations from `Finite`,
`Countable`, or a finite tree. It needs no global state enumeration or
payoff comparison on arbitrary reals. Information is bound to the game's
original `base.init`; continuing from a nonempty `current` keeps that same
strategy domain and does not prune or restart it.

`HiddenAction` constructs all enumeration data: Boolean players and actions,
and a singleton represented information coordinate per player with an actual
decision-history witness. Each player has two strategies, and
`profile_complete` proves that every original pure profile is one of the
four two-bit tables. The second player's different concrete histories share
one information coordinate. The chance bonus has exact weights `2/3` and
`1/3`. `root_terminates` proves that every atom is terminal after three
actions for every original pure profile, so these root checks use final
payoffs rather than truncated ones.

| Kernel-checked regression | Result |
|---|---|
| Coordination payoff, with a common random bonus | Exactly equal choices pass; payoff is `4/3` at either equilibrium |
| Matching-pennies payoff with the same chance law | All four profiles fail; no original EFG pure Nash profile exists |
| Second player's two hidden-action histories | Histories differ but every pure profile chooses the same action |
| Horizon zero with auxiliary nonterminal payoff 17 | Stopped payoff zero; the matching-pennies candidate passes only this truncated check |
| Continue after the first action was `true` | Payoff `4/3`; restarting the same profile at the root yields `1/3` |

The numerical claims use `decide +kernel`. A guarded `#eval` executes the
actual checker and yields `(true, false, false, false)` for the selected
coordination and matching-pennies profiles.

`Occurrence.historyLaw_eq_pure` connects the existing occurrence compiler's
pure behavioral execution to its deterministic stopped history using the
existing pure-policy and Dirac-execution theorems.
`payoff_eq_occurrenceOutcome` then proves equality with the original
`GameTree.occurrenceOutcome` at every structurally sufficient horizon and
retained history. The existing `root.size` bound suffices everywhere below
that root; no termination certificate is supplied. With executable
occurrence-table enumerations, `check_iff_occurrenceNash` covers all original
occurrence-dependent pure deviations, and `check_backwardInduction` proves
that the existing backward-induction profile passes at every continuation.
This reuses the perfect-information compiler's results only in their stated
scope. It does not construct arbitrary finite-tree occurrence enumerations,
declare the global `GameTree.PlayerStrategy` function space finite, establish
imperfect-information SPE, or solve mixed equilibria.

These are example prototypes. Promotion would require separate review of the
finite-table checker and its semantic bridge; the API-growth freeze remains
in force. No previous construction or theorem is replaced by an external
certificate. Earlier checkpoints retain their dated counts.

The full rebuilt audit expands from **224 to 225 modules**, retaining exactly
the same **138 noncomputable identities**, with no additions or removals.
The 35 nonzero modules still own 58 library and 80 example identities,
classified as 70 analytic definitions and 68 dependency propagations. The
new module and `FiniteLaw` remain at zero. Direct environment queries mark
`strategicForm`, `check`, the local terminal/information/action instances,
`HiddenAction.game`, and `HiddenAction.rootCheck` as computable. All example
instances are locally scoped.

The classification preserves M in `review_history`, protects the new zero
module (**190 modules**), and records the twenty-second execution regression.
All previous declaration and regression evidence, the 76 cleared identities,
and both baseline files remain unchanged. The 342-identity computability
baseline still has 204 absent identities. The generic finite-table
requirements are executable data; no analytic law, correctness certificate,
or new assumption on existing consumers was introduced.

Validation passed on the final source: `lake build`,
`lake build EconCSLib.Examples`, `lake env lean tests/FiniteLawSmoke.lean`,
placeholder, API-growth, full computability, and governance checks. A separate
`audited_modules`/`run_audit` query confirms exact equality of the before/after
identity sets. The full axiom audit covers **11,201 declarations in 225
modules, with zero forbidden dependencies**. The new module passes
`lake env leanchecker`; the import-only aggregate passes the pinned checker's
exact `replayFromImports` routine through a temporary `import LeanChecker`
driver, avoiding CLI prefix discovery of old cached modules. The new module
adds no warning; existing dependency warnings are retained.
`git diff --check` passes.

The additional Mathlib-style `check_distillation.py` passed.
`check_benchmark.py` remains blocked at its preservation gate by the
pre-existing root `AGENTS.md` modification, as at the earlier checkpoints.
That unrelated change and the benchmark rules were preserved, so the full
benchmark is not reported as passing.

## O checkpoint — 2026-09-03

O implements fixed finite absorbing rational chains in the opt-in
`EconCSLib/Examples/ExtensiveGame/FiniteMarkovChain.lean` and
`FiniteMarkovChainSemantics.lean`, under
`Examples.ExtensiveGame.FiniteMarkovChain`. Both are imported only by the
example aggregate, included automatically in the environment audits, and
protected as zero-noncomputability modules. The stable root and frozen
Canonical/Frontend surface are unchanged.

The computational input is a `Chain n m`: explicitly encoded transient
`Fin n` states and terminal `Fin m` states, nonnegative rational blocks
`Q` and `R`, row-normalization proofs, and a rational terminal-state reward.
This is a fixed Markov specification. It neither converts arbitrary EFG
histories into states nor restricts to a supposedly reachable subchain.
An EFG adapter would still need proofs of stationarity and state sufficiency.

`row` uses executable `List.ofFn` enumeration to construct each original
`FiniteLaw` transition. `step` makes terminals absorbing. `run` executes a
bounded number of transitions, returning either an unfinished transient
state or the pair `(r, terminal)` recording the first hit after `r + 1`
transitions. `run_expect` proves the whole censored distribution against any
rational observable; `run_firstHit` identifies every hit coefficient with
`Q^r R`, and `run_survival` identifies unfinished probability with the row
sum of `Q^H`. Zero weights and zero rewards never stand for nontermination.

The supplied numbers `k` and `c` are checked, not trusted: `admissible` tests
`k > 0`, `0 ≤ c < 1`, and every row sum of `Q^k ≤ c`. Thus every transient
state has probability at least `1-c > 0` of terminating within `k` steps.
It works when some states have zero chance of one-step termination. The
checker covers the entire supplied state domain; the caller supplies no
inverse, solution, path law, or expectation equality.

After searching the pinned Mathlib matrix implementation, `solveLinear`
reuses its executable determinant and Cramer construction. It tests the
determinant before division. `solve` actually computes both
`(I-Q)v = Rg` and `(I-Q)t = 1`, returning terminal values `g` and times zero.
Errors distinguish a failed absorption bound from a singular linear system.
Cramer's rule is adequate for these small exact examples; this work makes no
large-matrix performance claim and introduces no general elimination library.

The analytic proof first bounds the operator norm of the real cast of
`Q^k`. Decomposition into finitely many residue classes proves summability
of all powers and of `(r+1)Q^r`. The ordinary series proves that `I-Q` is
invertible. A shifted weighted-series identity supplies the first moment.
`hasSum_firstHit` proves that the first-hit coefficients sum to one.
`firstHit_probability` constructs their countable weighted Dirac probability
measure on `(r, terminal)`; `firstHit_singleton` and `run_firstHit` connect
its atoms to actual finite execution. This is a joint first-hit law, not a
new full-state trajectory constructor. It suffices for reward and hitting
time, and has no residual nontermination mass under the checked bound.

`integrable_reward` and `integrable_time` prove integrability.
`solve_correct` constructs the actual successful solver result, proves both
Bellman equations and uniqueness, and identifies both rational vectors with
their Bochner expectations under that probability law. `terminal_semantics`
handles an already terminal start. `delayed_expectations` consumes the
computed two-step result and the general semantic theorem; neither an
integral equality nor an integrability certificate is an input. Measures,
infinite sums and real analytic operations occur only in theorem statements
and proofs; no analytic wrapper definition or global instance was added.

| Kernel-checked regression | Actual result |
|---|---|
| Probability `1/2` self-loop, terminal reward seven | value `7`, expected time `2` |
| Self-loop and terminal rewards `-3`, `5`, each exit mass `1/4` | value `1`, expected time `2` |
| Already at the second terminal | value `5`, expected time `0` |
| First state must transition to a geometric state | two-step bound succeeds; value `7`, expected time `3`; one-step bound fails |
| Closed nonterminating class in the supplied domain | explicit `absorptionBound` error |
| Zero matrix with nonzero right-hand side | `solveLinear` returns `none` |
| Zero block length or margin `1-c=0` | bound rejected |
| Geometric first hit on transition three | exact executed probability `1/8` |

A guarded `#eval` runs the actual solver for the geometric, signed-reward,
and two-step examples. The arithmetic regression proofs use kernel-checked
`norm_num`, not `native_decide`.

The scan expands from **225 to 227 modules**, retaining the same **138
noncomputable identities** with **zero removals and zero additions**.
The 35 nonzero modules still contain 58 library and 80 example identities,
classified as 70 analytic definitions and 68 dependency propagations, with
no proof-generated helpers. The new modules have zero such identities.
The classification preserves N in `review_history`, adds two protected zero
modules (**192 total**) and two regression sources (**24 total**). The 76
previously cleared identities, both baseline files, and all old evidence are
unchanged. O's completed source is covered by the final validation below.

## P final semantic and computability audit — 2026-09-03

A–P are complete within the stated finite/prototype scopes. This audit reads
the implemented statements and their consumers, rather than interpreting
compilation or a reduced noncomputable count as semantic correctness.
Historical A–F and G–N figures below/above remain their dated checkpoints.

| Stage and implemented computation | Inputs and actual premises | Proved correspondence and consumers/regressions |
|---|---|---|
| G: constructor countability proof and rational midpoint | Explicit two-constructor node; fixed rational `1/2`. `Countable` is proof data, not an extracted encoder. | Original almost-sure/countability consumers and the non-atomic lower-half probability theorem remain; `halfAction_coe` identifies the original real midpoint. No general real comparison algorithm. |
| H: `requiredFuel`, `totalExpectedPayoff` | Existing finite stochastic tree, occurrence policy, retained path and supplied real payoff data. All finite child indices are explicit. | `totalExpectedPayoff_eq_expectedPayoffWithFuel` holds at every computed sufficient bound; leaf fuel is **one**. Unequal depths, repeated subtree occurrences, and prefix-sensitive policies run. No real approximation claim. |
| I: existing `FiniteLaw.expectRat` plus finite measure interpretation | Finite normalized rational atom list, rational utility; measurable singletons for pointwise integration. No finite/countable ambient carrier requirement. | `integral_eq_expectRat`, integrability, normalization, event mass and equivalence invariance; duplicate/reordered/zero atoms on `ℕ` give `-1/12`. J and K consume these results. |
| J: `stoppedExpectedPayoff` | Executable terminal decision, finite-support history policy, current **complete history**, horizon and rational payoff. | `historyLaw_eq_coordinate` and `integral_stoppedUtility` use the actual history `Kernel.traj`; finite-coordinate integrability is proved. Same endpoints with different histories, signed payoffs, terminal absorption and zero horizon are tested. K and M consume the bridge. |
| K: `conditionalLaw`, `conditionalPayoff`, `jointExecution` | Finite prior, decidable observation equality, executable history policy and finite continuation horizon. Positive observation mass only for the division formula. | `conditionalPayoff_bayes`, `conditionalLaw_joint`, `conditionalPayoff_joint_integral`; posterior and normalization are computed. Hidden routes, impossible observation `none`, genuine `some 0`, terminal continuation and retained-clock offsets run. No arbitrary infinite-utility conditional expectation. |
| L: `completePaths` | Finite execution with a supplied finite horizon and proof that **positive** final atoms are terminal. The bound itself is not discovered here. | All-time marginals and legal absorbing paths; `exists_pathLaw` constructs the measure and certificates consumed by the existing `Arena.pathLaw` projection. Zero-weight unfinished ghosts are excluded from almost-sure legality, and prefix length is retained. |
| M: `estimate`, `searchHorizon`, `search` | Exact stopped payoff and unfinished mass; finite candidate budget. Analytic correctness additionally needs a bounded terminal payoff extension, a dominating rational bound, agreement with original terminal payoff, countable discrete complete histories and almost-sure terminal reachability. | `estimate_correct`, `search_correct` prove the exact `M*q_H` radius. Actual trajectory legality/absorption and integrability are proved. Geometric reachability is proved in the regression, not supplied as the target equality. `none` is failure inside the finite search budget only. |
| N: `strategicForm`, `check` using existing `isNashEq` | Executable finite player, represented-information and legal-action tables; rational chance laws, current history and horizon. | `check_iff` quantifies over the original full root-bound pure deviation space. Coordination has a pure Nash equilibrium; matching pennies has none; information consistency and nontrivial chance bonuses are checked. The occurrence bridge proves sufficient-horizon utility equality and consumes existing backward induction only for its perfect-information compiler. |
| O: `row`, `run`, `admissible`, `solveLinear`, `solve` | Explicit finite rational fixed-chain data and the checked uniform finite-step absorption inequalities. | Finite first-hit probabilities, eventual probability normalization, integrability, determinant nonzero, unique solutions, and actual expectations in `solve_correct`; all eight boundary/regression rows above and `delayed_expectations`. |

The error radius in M is **`M*q_H`, not `2*M*q_H`**: at a finished
coordinate the stopped and eventual utility agree, and at an unfinished
coordinate the stopped utility is zero while eventual utility has absolute
value at most `M`. The theorem's original payoff agreement, bound and
reachability hypotheses remain visible. Mere finiteness, a small observed
sample, or a successful compiler run supplies none of these premises.

Finite support does not mean finite ambient histories. J/K retain action
memory and absolute history length; continuing from a stored history is not
restarting from its endpoint. L's horizon condition only concerns positive
atoms. N checks a horizon-dependent stopped game in general; a sufficient
termination horizon is established for its worked games and occurrence
bridge. No general pure Nash existence, imperfect-information SPE, arbitrary
mixed equilibrium, or unconditional behavioral/mixed conversion is asserted.
O's states are a standalone fixed Markov model; no EFG endpoint quotient or
unproved reachable-state reduction has been introduced.

Namespace and import review found the additions confined to explicit example
prototype namespaces. General matrix summation helpers in O are private;
the solver is scoped to the finite rational task. Norm notation is locally
scoped and `NeZero` instances occur inside proofs. N's enumeration instances
are local. `Math/` gains no domain dependency, and finite-law execution gains
no analytic imports. No facade alias, Canonical/Frontend declaration, global
instance or frozen API baseline was added. Promotion of any prototype still
requires the existing separate API review; this audit does not authorize it.

The retained analytic boundary is unchanged: **70 analytic definitions and
68 dependency propagations** remain, individually source-linked in the
classification ledger. General measures, kernels, infinite trajectory laws,
conditional kernels, integrals and analytic strategy realization are not
finite numerical algorithms. In particular, the recorded general
`Arena.pathLaw`, `CompletePathLawSemantics` and countable-presentation
interfaces still receive their stated external mathematical data. L
constructs one bounded-termination specialization; J/M prove results for
explicit existing trajectory expressions; O constructs its fixed-chain
first-hit law. None replaces the general supplied-law contracts.

Remaining capabilities outside these completed prompts are explicit:
arbitrary finite-tree occurrence enumeration, general history-to-Markov
state reduction, MDP optimization, general mixed-equilibrium solving,
unbounded conditional-utility computation, and numerical algorithms for
arbitrary real/nonatomic analytic data are not implemented. M's bounded
search has no universal effective success guarantee. O checks a supplied
finite-step bound rather than automatically searching for one. These are
scope limits, not conclusions hidden in certificates.

Final validation passed: `lake build`, `lake build EconCSLib.Examples`,
`lake env lean tests/FiniteLawSmoke.lean`, placeholder, API-growth,
full computability, full axiom and governance checks, and `git diff --check`.
The axiom audit covers **11,366 declarations in 227 modules**, with
**zero forbidden dependencies**; it traverses private/generated declarations
and dependencies outside the audited modules. Only the existing permitted
`propext`, `Quot.sound` and `Classical.choice` may occur. No public proof
introduces a `native_decide` axiom.

Batched kernel replay covers all eleven G–O implementation modules, including
both new O modules. The import-only example aggregate is replayed with the
pinned checker's exact `replayFromImports` routine, avoiding broad prefix
selection of obsolete cached modules. The new modules add no build warnings;
pre-existing dependency warnings remain.

An independent final `audited_modules`/`run_audit` query compares exact
module/declaration pairs with the O/P starting set: **138 retained, zero
removed, zero new**. Direct environment queries confirm the new finite
algorithms are unmarked. The unchanged 342-identity baseline still has 204
absent identities. The API baseline SHA-256 remains
`c418323fc254fc6ead84b0e34f388285499f6a16a17b305d5d5c625a2de35ef3`;
the computability baseline remains
`5dd2c21096fd2128fef8b95fecf94a7c7277689955a0ac93324247b41759bf27`.
The ledger now records P as current and preserves both N and O snapshots.
All 227 modules in that checkpoint, including every then-new opt-in module,
were scanned.

The additional Mathlib-style `check_distillation.py` passed.
`check_benchmark.py` again stops at its preservation gate because the root
`AGENTS.md` already differed before this work. That unrelated user change
and the benchmark rules were preserved, so the full benchmark is not claimed
to pass. No commit, reset or baseline update was performed.

## A–F completion and enforcement — 2026-09-03

At A–F completion, the rebuilt audit covered **all 219 modules** and reported
**140 noncomputable declarations in 35 modules**: 58 library declarations and 82 example
declarations. `FiniteLaw` remains at zero. This workflow removed **74 exact
identities**, added none, and preserved the original mathematical constructions
and their proofs. The unchanged 342-identity baseline now has 202 absent
identities, including the 128 removed before this workflow.

| Stage | Before | After | Result |
|---|---:|---:|---|
| A | 214 | 212 | Two redundant tiny-game modifiers |
| B | 212 | 204 | Eight executable finite decisions |
| C | 204 | 194 | Finite choices, occurrence comparisons, proof-only countability encodings |
| D | 194 | 194 | Individual review of every remaining identity |
| E | 194 | 140 | 33 redundant modifiers, 17 concrete operations, three bounded evaluators, one outcome consumer |
| F | 140 | 140 | Review coverage and executable-boundary enforcement |

The retained set contains **71 general analytic definitions**, **68 analytic
dependency propagations**, and **one proof-generated helper**. There are
**zero unresolved executable operations** in the reviewed scope. The helper
is the generated `Countable Node` injection in
`ObservedMeasurableKernelAlmostSureOutcomeBoundary`; its countability proof
uses do not make it an execution dependency. The JSON ledger records every
retained identity, reason, dependencies, runtime role, mathematical guarantee,
source span/hash, and compiler-obstruction evidence. Its
`resolved_declarations` lists all 74 removed identities by stage.

The three stopped-utility operations now require an executable terminal test
only where bounded observation is performed. Constructor decisions instantiate
them in the outcome example. General eventual utility, integrability, and
expected eventual utility retain their prior hypotheses, using classical
reasoning locally in proofs. No law, normalization, legality, or realization
conclusion was replaced by an external certificate. See the exact consumer
migration in [`efg-api-migration.md`](efg-api-migration.md).

The checker retains the complete `Lean.isNoncomputable` module-ownership scan
and exact identity-subset test. Classification never removes an identity from
the total. It additionally checks exact review coverage, source evidence,
184 explicitly listed zero modules, and the 74 cleared identities. Thirteen
regression sources cover rational finite laws, actual history execution,
terminal/nonterminal decisions, occurrence distinctions, fuel-limited search,
event memory, clocks, and stopped-payoff branches. Existing import-boundary
checks remain in the governance suite. Supplied-law adapters are recorded
separately from algorithms that construct laws.

Both normal and `--skip-build` audits use Lake's dependency traces with
`--rehash`; the latter fails if an artifact is stale or missing. The checker
never silently audits old oleans. Review hashes require source inspection and
a deliberate record update after a retained declaration changes; they are
not a proof of mathematical correctness. The declaration list remains the
original one-way ratchet; its policy metadata now states the current two-track
rule that retained analytic identities require review while executable
boundaries remain clear. No declaration-list baseline update is part of A–F.

The [G–P prompt sequence](efg-finite-computation-prompts.md) covers two
additional cleanup candidates and finite computation with semantic proofs.
G–N are recorded above; O–P remain prospective. Neither the prompts nor
these follow-ups change the completed A–F counts or reopen Canonical/Frontend
API growth.

The subsequent [proof and semantic review](efg-proof-audit.md) replaces five
public native-computation proofs with kernel-checkable proofs, adds the EFG
axiom-dependency CI gate, corrects the finite-law embedding's documented scope,
and scopes namespace/instance blocks without changing the retained identities.

Validation: stable and example builds; `tests/FiniteLawSmoke.lean`; placeholder,
API-growth, full computability, and governance checks; checker unit/integration
tests including a real failing noncomputable data dependency and a stale
transitive dependency with preserved mtime; and `git diff --check`.
All of these passed, including 14 checker tests. The additional Mathlib-style
`check_distillation.py` passed. `check_benchmark.py` stopped at its preservation
gate because the pre-existing root `AGENTS.md` modification is outside that
benchmark's expected change list. This workflow preserved that unrelated
worktree change; the full benchmark is therefore not reported as passing.

## Verified starting snapshot

The 2026-09-03 audit rebuilt all 219 audited modules before querying
`Lean.isNoncomputable`. It found **214 declarations in 45 modules**: **62** in
18 EFG library modules, **152** in 27 example modules, and **0** in `FiniteLaw`.
The declaration set is a subset of the 342-identity baseline: 128 removed,
none added. These are dated counts, not acceptance thresholds.

| Remaining library area | Declarations | Modules |
|---|---:|---:|
| `Simulation/Kernel` | 22 | 6 |
| `Simulation/Presentation` | 9 | 4 |
| `Simulation/Continuation` and `Simulation/Restart` | 16 | 5 |

The complete `FiniteLaw`, EFG `Execution`, `Compiler`, `FOSG`, and `Winning`
trees audit at zero. So do the finite observed chance/behavior/mixed and
Kuhn/deferred-sampling surfaces, `Observed/Controlled/Semantics`, `Observed/SPE`,
and `Simulation/Presentation/Chance/Countable`. Preserve these results.
A zero audit on a supplied-law adapter does not establish an algorithm for
constructing its law.

In a temporary copy, removing only the two `noncomputable` modifiers on
`tinyObservedGame` and `tinyObservedRecallCertificate` in
`EconCSLib/Examples/ExtensiveGame/FiniteImperfectCompilation.lean` compiled
successfully. This was the pre-A observation; A subsequently applied exactly those removals.

## How to run

每次复制下方“Common contract”和一个提示词，按 A → B → C → D → E → F
顺序执行。前一任务已经完成的修改应保留；重新审计后跳过已归零的目标。
以下提示词保留任务顺序；本次 A–F 已执行完成，结果以完成记录和实时检查器为准。

| 提示词 | 任务 | 完成依据 |
|---|---|---|
| A | 删除确认多余的修饰符 | 原定义体、类型和证明不变，编译通过 |
| B | 实现有限例子的可判定输入 | 终止与相等性判定可执行 |
| C | 实现有限策略、历史选择与编码 | 明确算法或数据，保持 occurrence 区别 |
| D | 分类剩余分析声明 | 每项有原因、依赖、处理决定和证据 |
| E | 清理分析层中的有界操作 | 保持一般数学语义，验证有效输入下的计算 |
| F | 固化分层审计与最终报告 | 可执行部分清零，保留项逐项可解释且仍受审计 |

## Common contract

```text
在 EconCSLib 仓库根目录工作。阅读 AGENTS.md、README.md、docs/design.md、
docs/design/efg-document-authority.md、docs/design/efg-minimal-core-freeze.md、
docs/design/efg-governance.md、docs/design/efg-semantic-universes.md、
docs/design/efg-semantic-compatibility.md，以及目标模块、导入与消费者。
所有仓库路径使用相对路径。保留已有工作区改动。

执行本提示词附带的单一任务。当前目标是有限执行真正可计算，并对分析语义逐项
解释其 noncomputable 原因；不要求一般测度和无限路径的数学定义全部清零。

修改前：
1. git status --short --branch。
2. python3 scripts/check_efg_computability.py --skip-build。
   若已有 olean 缺失或比源码旧，先运行不带 --skip-build 的完整检查。
3. 使用检查器的 audited_modules/run_audit 提取目标的准确 module/declaration
   身份清单；普通文本搜索不足以发现 section 和编译生成的私有声明。
4. 用 rg 追踪消费者，记录当前数据输入、数学前提、产出及相关定理。

约束：
- 不新增 noncomputable 身份、noncomputable section、sorry、admit、axiom 或其他
  用来跳过证明/编译检查的手段。已审计的分析定义可以保留原有标记。
- 不移动、改名、删去功能、缩小扫描范围或增大基线来隐藏残留；分类不会从总数中
  排除任何声明。检查器继续检查全部 EFG、FiniteLaw 和全部 EFG 示例。
- API 增长冻结仍然有效。优先现有接口和一对一替换，不新增平行 API、别名层、
  redirect 模块或 facade。类型变化同步迁移消费者并记录在
  docs/design/efg-api-migration.md。不存在用新接口绕过冻结的默认授权。
- 有限概率运算继续使用 FiniteLaw 和精确有理数。Decidable/Fintype/Encodable
  必须有实际可执行实现；不能仅把 Classical 实例换成显式参数就声称完成。
- Prop 中的存在性证明不是运行时数据。需要时使用显式见证、实际枚举、有界搜索、
  构造性递归或已经存在的有效表示。经典推理可以留在不产生运行时数据的证明中。
- 部分操作用 Option/Except 或显式定义域。搜索在给定 fuel 内未找到，不等于永远
  不存在。保持零概率条件事件、空动作集和缺少终止见证的原有语义。
- 保持历史发生位置、信息一致性、时间索引、边缘分布、非终止语义和已证明等式。
- 一般 Measure/Kernel、积分、条件分布、无限路径律可以是分析定义。把对象变成
  输入或证书投影，必须标为“依赖外部数学数据”，不能计作新实现了该对象的算法。
- 有效消费者优先调用算法；一般分析定义保留为当前语义，不因有效子域可计算而标为
  legacy。跨层结论必须引用精确等式、带误差界的逼近或如实陈述的几乎处处定理。
- 不把原来证明的存在性、归一性、合法性或边缘一致性改成调用方新增假设来完成
  任务。若需要更强的有效输入，明确列出；原有数学结论仍须在原前提下可获得。
  若当前冻结或接口无法同时满足这点，保留现有分析定义并记录具体限制。

验证按修改范围执行：
- Lean 修改：构建修改模块及直接消费者；运行 lake build、
  lake build EconCSLib.Examples、lake env lean tests/FiniteLawSmoke.lean、
  python3 scripts/check_lean_placeholders.py EconCSLib、
  python3 scripts/check_efg_api_growth.py、
  python3 scripts/check_efg_computability.py、
  python3 scripts/check_efg_governance.py。
- 只改文档：检查声明/文件引用、数字和链接，不为文档重复全量 Lean 构建。
- 改校验脚本：遵守 AGENTS.md 要求的相关工作指南，运行对应单元/集成测试及
  被修改的检查器；检查器结果不能依赖陈旧 olean。
- 所有修改运行 git diff --check，交接前再次检查 git status --short --branch。

报告：准确的前后声明数、移除身份、残留身份及原因、类型/假设变化、消费者迁移、
验证结果。区分“移除旧标记”“实现算法”“依赖外部证书”“保留分析语义”。
代码清理任务在目标仍存在且已完成时应实际减少可消除项；分类/规则任务可以不降
总数。总数下降不是数学能力保持的证明。不要自动更新既有基线。
```

## Prompt A — redundant modifiers

```text
执行残留清理的第一步，仅处理
EconCSLib/Examples/ExtensiveGame/FiniteImperfectCompilation.lean 中的：
- Examples.ImperfectInformation.tinyObservedGame
- Examples.ImperfectInformation.tinyObservedRecallCertificate

先确认它们仍在当前审计中。此前临时副本仅移除这两处 noncomputable 修饰符就能
编译通过；现在对仓库源码完成这一修改，并构建原模块及其消费者。

不得为了通过检查修改定义体、类型、证明、假设、实例或依赖；不顺带改其他示例。
若再次验证发现依赖已经变化，报告准确的编译障碍，不把本任务扩展为接口迁移。

完成时这两个身份应从审计消失，相关语义定理继续通过，没有新增身份。说明这是
遗留标记清理，而不是刚实现了两个新算法。若两项已不在审计中，验证后直接报告
已完成，不重复修改。遵守公共契约中的验证要求。
```

## Prompt B — executable decisions

```text
处理下列示例中剩余的终止判定和相等性实例，目标路径均位于
EconCSLib/Examples/ExtensiveGame/：
- AbsentMinded.lean：DecisionKey 的 DecidableEq 实例。
- HistoryObjectiveContinuation.lean：terminalDecidable、endpointTerminalDecidable。
- ReachableNoChance.lean：terminalDecidable。
- WinningSemantics.lean：terminalDecidable、arenaTerminalDecidable。
- InfiniteInformationKuhnBoundary.lean：terminalDecidable、observedTerminalDecidable。

起始审计包含这八个身份；以当前审计为准。有限观察上的判定不应依赖无限策略
空间的全局可判定性。使用具体状态构造子的模式匹配，或由已有可执行字段推出
相等性。将实例限制在真正需要的示例/操作处。

不要用 Classical.propDecidable、Classical.decEq、Classical.choice，或把这些实现
搬到调用方。涉及 subtype 时证明其投影判定与原命题等价，不对整个一般 History
或 Arena 添加全局实例。除直接类型 fallout 外，不在此任务改策略选择或分析核。

对实际入口验证终止和非终止两个分支，并验证必要的相等/不相等情形。优先在已有
示例加入少量有意义的 native_decide/#eval 回归；不要为每个包装器复制测试。
全部目标及直接消费者构建通过，审计无新增，列出实际消失的身份。
```

## Prompt C — finite witnesses, occurrences, and encodings

```text
在 A、B 完成后，处理 EconCSLib/Examples/ExtensiveGame/ 的下列残留：
- HistoryObjectiveContinuation.lean：routeObjective、profile。
- ReachableNoChance.lean：profile、pureHistoryPolicy、initialContinuationGameForm。
- FiniteReachableUnfolding.lean：routeTerminalOutcome。
- OccurrenceNonIso.lean：separatingOccurrenceStrategy。
- DesignatedContinuationSPEBoundary.lean：occurrenceThreatProfile。
- RandomTermination.lean：审计中的两个 Countable 派生私有辅助声明。

先逐项尝试移除确实多余的修饰符；需要算法时，直接构造具体合法动作，使用已有
信息/历史编码进行比较，或在显式有限集合中按确定顺序搜索。不得从 Nonempty、
Exists 或 representedInfo_nonempty_infoAction 用经典选择取出运行时数据。

历史比较必须区分达到同一状态的不同路径，不能用终点相等代替历史相等；策略
必须仍能在两个相同子树的不同 occurrence 上选择不同动作。合法但未到达的信息
状态也要按原策略类型正确处理，不能靠任意默认动作或新增不可达前提绕开。

对 Countable 派生声明先判断实际作用：运行时编码需要可执行 encoder/decoder
及往返性质；只用于证明的辅助项不应仅因它在审计中就强加全局计算结构。保留
原有 Countable 结论，不通过删除实例、改名或搬走声明使审计漏报。

验证左/右路径结果、两个 occurrence 的动作区别、实际单步执行以及确实需要的
编码往返。保持原来的不等式、不可同构、续局与终止定理。
先完成有限选择和历史部分，再处理编码；每个步骤都检查消费者，避免一次重写
全部示例。若一个生成项只能保留为证明用分析构造，给出证据并交由 D 分类。
```

## Prompt D — classify the analytic remainder

```text
在有限清理后，审计全部剩余 noncomputable 身份。本任务以检查和分类为主，不
批量将 Measure/Kernel 参数化，不修改数学 API，也不要求总数下降。

为每个 module/declaration 记录：分类、直接非计算原因、关键依赖、运行时作用、
现有数学保证、处理决定和可核查的源码/定理证据。把结果保存到
scripts/efg_computability_classification.json，供 F 接入检查器；此时它只是一份
审查记录，不改变现有检查器的通过条件。

至少区分：遗留标记、可消除的运行时判定/选择、依赖传播、一般分析定义、证明
生成辅助项。对已归零但以外部 Measure/Kernel/完整路径证书为输入的相关接口，
在本工作文档中单独说明其有效性前提，不把它们计作生成测度的算法。

具体核查 Kernel.traj、Measure.map/bind、condDistrib、积分，以及
stoppedUtility 的有限终止判定和 eventualUtility 的无限最终吸收判断。
不能因为模块位于 Simulation 就把所有残留都归类为必要分析定义，也不能从
Mathlib 使用 noncomputable 推导数学上不存在任何可计算特例。

提出逐项决定：可直接清理、可在现有有效输入下实现、保留一般数学定义，或需要
独立接口设计。保留解析构造/存在性及 realization 定理；任何建议增加的输入都
要解释是否把原来的结论变成了假设。若某项原因不明，明确列为待解决，不自动
归入允许保留的集合。输出 E 的准确处理清单和仍需数学审查的问题。
```

## Prompt E — bounded operations inside analytic semantics

```text
依据 D 的证据，优先处理
EconCSLib/GameTheory/ExtensiveGame/Simulation/Equilibrium/Outcome.lean 中：
- TerminalPayoffExtension.stoppedUtility
- TerminalPayoffExtension.stoppedPathUtility
- BoundedTerminalPayoffExtension.stoppedBoundedPathUtility
以上名称位于 ExtensiveGame.ObservedGame.MeasurableHistoryModel 命名空间。

这三项只观察给定 horizon，首先检查非计算原因是否仅是经典终止判定及其传播。
在最窄的位置使用实际可执行的判定，复用现有接口，不向所有一般解析模型强加
有效编码或可判定假设。同步处理受影响的定义、定理、continuation/outcome 示例；
在原前提下保留一般数学结果，明确有效计算额外需要的数据。

保持 stoppedUtility 在该坐标尚未终止时取零、终止时取指定 payoff 的原语义。
通过已有有限/有理数实例验证相应分支和执行；包装或返回一个给定的 ℝ 值不等于
实现任意实数求值，更不等于实现积分。不要为了运行测试改一般收益语义。

对 eventualUtility 保留一般数学解释，不假定任意无限路径的最终吸收性可判定。
需要实际终止查询时复用现有 fuel 有界 Option 接口；none 仅表示该界内没找到。
一般 expectedUtility、unfinishedMass、条件分布和完整路径律仍可保留为分析定义。

如果消除某项需要把已证明的语义改成假设、削弱一般性或违反 API 冻结，保持该
分析定义，记录准确障碍及现有可计算特例；不要用外部 certificate 填空完成。
更新 D 的逐项分类及迁移记录。报告真正去除的运行时非计算依赖与仍保留的数学
构造，不以本模块必须全零作为验收条件。
```

## Prompt F — enforce the reviewed boundary

```text
在 A–E 完成后，将审查结果接入
scripts/check_efg_computability.py、tests/test_check_efg_computability.py，
并同步 docs/design/efg-computability-migration.md 与实际涉及的权威文档。
修改验证脚本前按 AGENTS.md 阅读所要求的指南。

保留 Lean.isNoncomputable、完整模块所有权扫描和精确身份集合的 subset 检查。
维护 scripts/efg_computability_classification.json 中逐项的理由与证据。
分类不能替代原身份基线，不能把分析项从总数或新增身份检查中排除。

分别报告：可执行路径上的未解决项、外部证书前提、保留的分析定义、证明生成
辅助项，以及总数。数据生产者依赖 noncomputable 实例，即使该实例通常只在证明
中使用，也必须按其实际运行时作用审查。新身份、同数量身份替换、缺失分类、
有限路径中的经典数据选择和未解释的剩余项应被发现；目录名称不构成豁免。

以具体声明、现有 import 边界和可执行回归限定零要求。已清零的 FiniteLaw、
有限执行、编译器等范围不能退化；仅有一个非计算的证明用辅助声明时应独立记录，
不要据此声称整个算法不可执行。标记集合与实际可执行性仍需分别说明。

保留或补充有针对性的回归：原身份基线拒绝新增/同数替换；分类记录遗漏会失败；
正确保留的分析项仍计入总数；向受保护的可执行入口引入非计算依赖能被编译或
运行回归检出。不要编写只复述 JSON 字段或实现步骤的测试。

本任务不自动放宽或更新既有基线，也不把分类记录的存在当成数学正确性证明。
对 A–E 发现但未解决的实际计算问题，给出具体声明和原因，不能凭分类宣告完成。
最终成功标准是：约定的可执行入口通过执行验证，所有残留逐项有据可查，原数学
能力保持，审计持续防止回归。允许最终总数大于零。

输出最终数量、分类统计、实际可执行入口、外部数据/证书前提、保留分析项及
验证结果。删除或改正仍在发布“全部 noncomputable 必须清零”目标的活动说明；
历史快照保留并明确标为历史。仅改与此决策直接有关的文档。
```

## D review checkpoint — before E (2026-09-03)

A–C were executed in order. Their complete build/check suite passed with
**194 declarations in 35 modules** (62 library, 132 examples), down from
214/45 with no added identity. The exact removals and consumer effects are
in [the API migration record](efg-api-migration.md#executable-example-decisions-and-occurrences-2026-09-03-ac).
Both existing baselines remain unchanged.

D recorded every then-remaining identity in
[`scripts/efg_computability_classification.json`](../../scripts/efg_computability_classification.json).
The ledger now records the final live set plus resolved identities. It includes
source ranges and hashes, elaborated types, direct
noncomputable references, runtime roles, mathematical guarantees, treatment
decisions, and compiler diagnostics from temporary modifier-only probes.
References inside erased types/proofs are distinguished from compiler-reported
data dependencies. This is review evidence, not a replacement for proof checking.

| D category | Count |
|---|---:|
| General analytic definition | 71 |
| Dependency propagation | 88 |
| Redundant legacy marker | 33 |
| Bounded runtime decision | 1 |
| Proof-generated helper | 1 |
| **Total** | **194** |

`Kernel.traj` extends cylinder content to a full infinite-path probability
measure; its normalization and projective-limit theorems remain available.
`Measure.map` constructs pushforwards, and `Measure.bind` integrates the
conditional measures. Even `Kernel.partialTraj` with finite horizon still
composes arbitrary analytic kernels. `condDistrib` constructs a conditional
version: the a.e. equality, positive-atom formula, and zero-mass boundary must
remain distinct. General Bochner integrals are not executable finite sums.
These are reasons about the present mathematical representation, not claims
that computable special cases cannot exist.

The D probe found only a classical terminal decision at the requested
coordinate in `stoppedUtility`, propagated by its two wrappers. E replaced
that decision with the narrowly scoped effective input described above. In contrast, `eventualUtility` classically decides an unbounded
eventual-absorption proposition and takes its least witness with `Nat.find`.
The latter retains its general semantics. `Arena.terminalTime path fuel` is
the operational bounded alternative; `none` means no termination found at
that bound.

Zero-marker interfaces with external data still require care:

- `Arena.pathLaw` takes a supplied `ProbabilityMeasure`; marginal and legality
  conclusions consume separate coherence certificates. It does not construct
  a measure from a stochastic policy.
- `ControlledObservedGame.CompletePathLawSemantics` stores per-root normalized,
  almost-surely legal path measures and their coordinate laws. It does not
  infer a common causal process or restart consistency.
- `ObservedChanceGame.CountablePresentation.informationAtHistory` and the
  other effective selectors consume concrete decisions/encodings. Analytic
  realization in their examples additionally takes the existing measurable
  presentation/profile and compatibility data. Selector execution is not
  construction of those analytic inputs.

D's exact 53-item work list follows; E completed every entry below and also
made the outcome example's `evaluation` consumer executable. `remove_modifier` means no mathematical body
change; `specialize_existing_operation` means unfold a concrete finite
field/prefix expression while preserving its original type and equations.
`implement_with_effective_input` applies only to the three stopped-utility
operations and preserved general theorems using proof-local classical
decisions. No new external law/normalization/legality certificate was added.

| Module suffix | Decision | Declarations (final name components) |
|---|---|---|
| `Examples.EventHistoryKernelBoundary` | `remove_modifier` | `eventArena_actionBundleFintype`, `eventArena_pathEventFintype`, `eventArena_stateSubsingleton` |
| `Examples.EventHistoryKernelBoundary` | `specialize_existing_operation` | `falseActionPrefix`, `rememberedAction`, `trueActionPrefix` |
| `Examples.HistoryDependentKernelBoundary` | `remove_modifier` | `historyArena_stateFintype` |
| `Examples.MeasurableKernelContinuationNashBoundary` | `remove_modifier` | `actionBundleMeasurableSingletonClass`, `assembly`, `evaluation`, `historyMeasurableSingletonClass`, `realizationKernel_isFinite`, `realizationKernel_isSFinite` |
| `Examples.MeasurableKernelContinuationNashBoundary` | `specialize_existing_operation` | `eventInformation`, `historyMeasurable` |
| `Examples.MeasurableKernelFreshRestartClockBoundary` | `remove_modifier` | `actionBundleCountable`, `actionBundleMeasurableSingletonClass`, `incomingMeasurableSingletonClass`, `pathEventCountable`, `pathEventMeasurableSingletonClass`, `stateMeasurableSingletonClass` |
| `Examples.MeasurableKernelFreshRestartClockBoundary` | `specialize_existing_operation` | `absoluteSecondPrefix`, `freshSecondPrefix`, `selectedBundle` |
| `Examples.MeasurableKernelRestartInformationRebaseBoundary` | `remove_modifier` | `actionBundleMeasurableSingletonClass`, `stateMeasurableSingletonClass` |
| `Examples.MeasurableKernelRestartInformationRebaseBoundary` | `specialize_existing_operation` | `freshPrefix`, `retainedPrefix` |
| `Examples.ObservedChanceKernelBridgeBoundary` | `specialize_existing_operation` | `firstPrefix`, `secondPrefix` |
| `Examples.ObservedKernelProfileAssemblyBoundary` | `remove_modifier` | `assembly` |
| `Examples.ObservedKernelProfileAssemblyBoundary` | `specialize_existing_operation` | `rootPrefix`, `secondPrefix` |
| `Examples.ObservedMeasurableKernelAlmostSureOutcomeBoundary` | `remove_modifier` | `baseHistoryMeasurable`, `completeHistoryActionCountable`, `historyCountable`, `historyMeasurable`, `historyModelPathEventCountable`, `localActionCountable`, `terminalPayoff` |
| `Examples.ObservedMeasurableKernelOutcomeBoundary` | `remove_modifier` | `assembly`, `historyMeasurableSingletonClass`, `terminalPayoff` |
| `Examples.ObservedMeasurableKernelOutcomeBoundary` | `specialize_existing_operation` | `historyMeasurable`, `rootPrefix` |
| `Examples.ObservedNonAtomicKernelBoundary` | `remove_modifier` | `lowerHalfCylinder`, `lowerHalfHistoryEvent` |
| `Examples.ObservedNonAtomicKernelBoundary` | `specialize_existing_operation` | `rootPrefix` |
| `Examples.RealizedInformationBoundary` | `remove_modifier` | `rungMeasurableSpace` |
| `Simulation.Equilibrium.Outcome` | `implement_with_effective_input` | `stoppedBoundedPathUtility`, `stoppedPathUtility`, `stoppedUtility` |
| `Simulation.Kernel.Arena` | `remove_modifier` | `toMeasurable` |

The remaining generated `Countable Node` helper is used only in the
almost-sure example's countability/measurability proof chain. It is recorded
separately from execution; no data producer in that example extracts its
existential witness. General real clamping and real division in the
non-atomic example retain their current analytic representation.

## Historical numeric prompts and checkpoints

The following records describe the earlier completed work and its former
zero-audit objective. They are preserved for traceability and are not active
instructions. In particular, the final historical paragraph's proposed next
steps are superseded by A–F above. Do not reapply the old contract or rerun
completed migrations solely because they appear here.

<details>
<summary>Earlier snapshots, completed prompts 0–7, and the partial analytic checkpoint</summary>

## Planning snapshot

The 2026-09-02 working-tree audit reported 342 elaborated noncomputable
declarations in 69 modules: 177 in library modules and 165 in examples. This is
only a dated planning snapshot. Always rerun the checker for the live count.

The executable `FiniteLaw` carrier and the bounded finite-law migration are
already established. In particular, the current audit has no noncomputable
declarations in `FiniteLaw`, `Execution/StochasticExecution.lean`, the finite
observed chance/behavior/mixed modules, or the finite Kuhn-conditioning and
deferred-sampling stack. Keep those surfaces regression-locked; do not redo
their completed carrier migration.

### Checkpoint after Prompt 5

Prompts 1–5 were completed against the same declaration-identity baseline on
2026-09-02. The live elaborated audit is now **313 declarations in 59 modules**:
148 in library modules and 165 in examples. It contains no new identity and is
a strict 29-identity reduction from the 342/69 planning snapshot. The checked
baseline has deliberately not been tightened pending review.

| Prompt | Removed identities | Audit after prompt |
|---|---:|---:|
| 1 — terminal/action decisions | 1 | 341 / 68 modules |
| 2 — explicit termination witnesses | 8 | 333 / 66 modules |
| 3 — GameTree occurrence compilation | 4 | 329 / 65 modules |
| 4 — finite determinacy selectors | 5 | 324 / 64 modules |
| 5 — FOSG sequentialization | 11 | 313 / 59 modules |

The continuation prompts below were regenerated from this checkpoint. Their
listed counts are scheduling information, not allowances: rerun the audit and
use its exact identities before each task.

The remaining dependency order is:

1. harden the audit so a same-count declaration swap cannot pass;
2. remove hidden decisions and proof-erased witnesses from finite execution;
3. finish finite GameTree compilation and determinacy selection;
4. finish the FOSG compilation cone;
5. separate executable finite prefixes from supplied infinite-path laws;
6. make countable presentations effective rather than merely classical;
7. turn analytic measure/kernel construction into explicit presentations;
8. migrate continuation, restart, equilibrium, and examples to those inputs;
9. reach and permanently enforce a zero audit.

## Prompt 0 — harden the declaration-identity audit

```text
Harden scripts/check_efg_computability.py before further migration work.

Replace the count-only ratchet with a declaration-identity ratchet. The checked
baseline must store the exact sorted set of module/declaration pairs. A current
set is acceptable only when it is a subset of the baseline. A same-module,
same-count replacement with a new noncomputable declaration must fail.

Make --update-baseline refuse growth: it may remove declarations after a
reviewed reduction, but it must not silently record any new declaration. Audit
every Lean file under EconCSLib/Examples/ExtensiveGame rather than relying on a
textual direct-import heuristic. Continue auditing the complete EFG and
FiniteLaw trees by elaborated module ownership.

Add tests for parsing, subset/reduction behavior, same-count replacement
rejection, new-module rejection, baseline-update refusal, and one integration
fixture whose elaborated environment contains a noncomputable declaration.
Keep the checker runnable from a clean checkout and wire no temporary files
into the repository.

This infrastructure task need not reduce the current Lean count. It is done
only when the existing baseline passes, injected/new declaration identities
fail, all checker tests pass, and the full repository verification passes.
```

## Prompt 1 — executable terminal/action decisions

```text
Remove the classical terminal/action-emptiness decision from
Execution/Discrete/KernelTrajectory.lean, beginning with
KernelArena.instDecidableIsEmptyAction and its consumer cone.

Terminality and action availability must be decided by explicit executable
data at the narrowest owner. Prefer a supplied Decidable argument or an
existing Boolean/decidable terminal test. Do not install a global fallback
instance and do not choose an action from Nonempty or from a Prop proof.

Keep Policy partial exactly where terminal action fibers are empty. Preserve
stepLaw, stateLawFrom, traceLawFrom, coupling transfer, and their equations.
Add or update a small native_decide/#eval-style regression demonstrating that
a finite KernelArena executes without a noncomputable instance.

Stop after this declaration and its coherent immediate fallout reach zero.
Do not fold GameTree, FOSG, or analytic work into this task.
```

## Prompt 2 — explicit terminal witnesses and continuation outcomes

```text
Hard-migrate the data-producing termination API in
Observed/Controlled/Semantics.lean and Observed/SPE.lean.

The current terminalFuel route extracts a Nat from a Prop-valued existence
proof. Replace that runtime ownership with explicit computational input: a
fuel plus terminal proof, a dependent witness, a computable bound plus search,
or an executable well-founded search. Keep PureTerminatesFrom as a proposition
when it is useful for theorem statements, but never extract data from it with
Exists.choose.

Thread the replacement through terminal history, payoff/objective evaluation,
continuation game forms, Nash/SPE definitions, examples, and preservation
theorems. For profile-indexed totality, take an executable profile-to-fuel
provider and prove its terminal specification separately. Do not introduce a
default fuel or assume a uniform bound unless one is explicitly supplied.

The final API must make it visible which runtime datum causes execution to
stop, while preserving the existing terminal-history and equilibrium claims.
```

## Prompt 3 — constructive GameTree occurrence compilation

```text
Remove the audited noncomputable declarations from
Compiler/GameTreeObserved.lean, including Subtree.toArenaHistory,
observedStrategyToPlayerStrategy, observedProfileToPlayerProfile, and
observedToGameForm.

Trace the exact hidden choices and dependent equality transports. Use explicit
occurrence identifiers, decidable equality, ordered finite traversal, or
supplied witnesses/equivalences as required. Preserve occurrence sensitivity:
equal-valued subtrees at distinct occurrences must not collapse.

Do not fall back to the endpoint-only GameTree semantics, do not add a second
compiler, and do not retain the old definitions as aliases. Update all
in-repository consumers and regression examples in the same hard migration.
Demonstrate executable compilation and outcome evaluation on a finite tree.
```

## Prompt 4 — constructive finite determinacy selectors

```text
Remove terminalWinner, backwardWinner, backwardAction,
backwardRepresentative, and backwardStrategy from the noncomputability audit
in Winning/Determinacy.lean.

Make every finite choice deterministic from executable inputs. Use an explicit
finite enumeration and order for players/actions/representatives, request a
nonempty witness where mathematically required, and state the tie-breaking
rule. Return Option when a selector can legitimately fail. Do not use
Classical.choose, Fintype.choose, or an arbitrary default action.

Separate the executable backward-induction algorithm from logical determinacy
theorems. Reprove correctness, winner, strategy, and compatibility results
against the new algorithm. Preserve theorem strength; if a previous theorem
depended on a hidden choice, expose the missing hypothesis honestly.
```

## Prompt 5 — finish the FOSG sequentialization cone

```text
Remove all remaining audited noncomputable declarations from
FOSG/Sequentialization and its compiler/example consumers.

Target initialPolicy, initializedTargetStateLaw, weakSerialization,
macroDeterministicPolicy, macroPolicy, macroKernelSimulation,
serializedMacroPolicy_match, serializedBehavioralMacroPolicy,
probabilisticWeakSimulation, macroExecutionAction, and
serializedMacroPolicy, using the live audit as the exact list.

Use FiniteLaw and the constructive finite coupling layer throughout. Replace
initialization and macro-action choice by deterministic finite data or explicit
witnesses. Preserve source/target timing, synthetic-root behavior, occurrence
semantics, state/trace marginals, and weak-simulation relations.

Do not add PMF or Measure adapters to the finite cone. Split this prompt into
multiple reviewable commits/tasks if necessary, but each task must close a
consumer-complete subcone and strictly reduce the audit.
```

## Prompt 6 — executable finite prefixes, supplied infinite laws

```text
Start from the post-Prompt-5 audit (313 declarations in 59 modules) and
hard-migrate the infinite discrete execution owner. The current library target
is 16 identities: all 10 declarations in Execution/InfiniteTrajectory.lean,
both declarations in Observed/InfiniteExecution.lean, both declarations in
Observed/Controlled/Law.lean, and both declarations in
Observed/Controlled/Law/DiscretePath.lean. Confirm those identities from the
live elaborated audit before editing and include their immediate examples and
facade consumers.

Finite-prefix evolution, prefix probabilities, bounded stopping, and finite
observables must be executable with FiniteLaw. A coherent complete path law is
supplied certified data: it owns the mathematical infinite-path measure and
proofs that every finite marginal agrees with executable prefixes. Definitions
may project that data; they may not manufacture pathLaw, trajectoryKernel,
stepKernel, pathMarginal, pathProbabilityMeasure, or behavioralPathLaw through
choice or an extension theorem.

Represent lazy operational sampling separately from a completed path measure.
Do not claim that a terminating definition returns an entire infinite sample.
Move existence/Kolmogorov-extension arguments to Prop-valued theorems. Make
terminalTime and terminalPayoff explicitly partial when no stopping witness is
available, and keep stoppedPayoffLaw/terminalPayoffLaw as projections or finite
computations from supplied data.

Migrate terminal-time, stopped payoff, winning, and infinite-execution
consumers. Preserve every finite-prefix equation as the regression boundary,
add one executable bounded-prefix regression, and stop only after this entire
consumer cone strictly reduces the audit with no new identity.
```

## Checkpoint after Prompt 6

Prompt 6 was completed from the 313/59 checkpoint on 2026-09-02. The live
elaborated audit is now **297 declarations in 55 modules**: 132 in library
modules and 165 in examples. All 16 targeted identities were removed, and
`Execution/InfiniteTrajectory.lean`, `Observed/InfiniteExecution.lean`,
`Observed/Controlled/Law.lean`, and
`Observed/Controlled/Law/DiscretePath.lean` each audit at zero. No new
identity was introduced. The checked baseline remains deliberately untightened
pending review.

The executable boundary is now `FiniteLaw`-valued finite prefixes, exact
bounded unfinished mass and stopped-payoff laws, plus fuel-bounded `Option`
terminal search. Complete path and terminal-payoff probability measures are
supplied by callers together with marginal, legality, and realization
certificates.

## Prompt 7 — effective countable presentations

```text
Starting from the live audit after Prompt 6, remove the current 24 audited
identities owned by Simulation/Presentation/Chance/Countable.lean and the nine
current identities in ObservedChanceCountablePresentationBoundary.lean and
ObservedChanceCountableSparsePlayersBoundary.lean. Treat the live audit as the
exact list and migrate every consumer of those declarations.

A bare Countable or Nonempty instance is insufficient. Require explicit
enumerations, executable equality/terminal/action decisions, effective weight
data, and explicit fallback witnesses only where the mathematics guarantees a
nonempty fiber. Partial lookup or conditioning must return Option rather than
choosing an arbitrary information state or action.

Keep the boundary honest: finite support uses FiniteLaw; genuinely countable or
measure-valued semantics consume an effective/supplied presentation. Do not
reintroduce a PMF compatibility carrier merely to obtain countable support.

In particular, classify and migrate the current selector family
informationAtHistory, informationOfPlayerInformation, eventInformation,
fallbackAction, and realizedAction separately from the analytic projections
abstractMeasure, abstractKernel, realizationMeasure, realizationKernel,
measurablePresentation, and kernelPresentation. Countability and measurable
space instances must be derived from explicit encodings rather than opaque
Classical.choice-based equivalences.

Preserve the represented-information, history/action-bundle, realization, and
kernel-compatibility theorems. Update countable presentation examples to build
the required executable data explicitly. Require both countable example
modules and the owner module to finish at zero audited identities.
```

## Checkpoint after Prompt 7

Prompt 7 was completed from the 297/55 checkpoint on 2026-09-03. The live
elaborated audit is **262 declarations in 52 modules**: 108 library and 154
example declarations. All 24 owner identities and all nine countable-example
identities were removed. The consumer-complete migration also removed the
automatic presentation/profile pair from
`ObservedMeasurableKernelAlmostSureOutcomeBoundary`. The countable owner and
both required countable examples audit at zero, with no new identity or
per-module growth. The baseline remains untightened pending review.

Finite selectors use executable terminal/reachability/tag-equality decisions;
lookup and mismatched action realization return `Option`. Examples supply
concrete encoders and partial decoders. The automatic analytic constructor and
its adapter wrappers are gone: consumers take the existing supplied analytic
presentation/profile and exact compatibility or finite-marginal certificates.
The full identity list and type migration are recorded in
[`efg-api-migration.md`](efg-api-migration.md).

### Partial progress on prompts 8–10 (2026-09-03)

The reviewed input to this batch was 262 declarations in 52 modules. The
current verified audit is **214 declarations in 45 modules**, a strict
48-identity reduction with no additions or module growth. The baseline is
unchanged. This does **not** complete prompts 8–10: their direct owners still
contain 22, 9, and 16 identities respectively, and the remaining analytic
example consumers must migrate with those owners.

Completed owner changes and every removed identity are recorded in
[`efg-api-migration.md`](efg-api-migration.md#supplied-analytic-data-and-effective-profile-assembly-2026-09-03).
The next work remains the supplied arena/step/history/event/realization
foundation, followed by the remaining presentation, continuation, and restart
laws. The endpoint, observed-information, profile-assembly,
observed-conditioning, and structural-factorization reductions must be kept.

</details>
