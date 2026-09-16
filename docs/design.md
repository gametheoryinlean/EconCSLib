# EconCSLib Design Guide

This document describes the current public architecture of EconCSLib. The
source tree under `EconCSLib/` and the stable aggregate import `EconCSLib.lean`
are authoritative.

## Project Scope

EconCSLib provides reusable Lean infrastructure for computational economics,
not a collection of isolated theorem ports. The initial release covers a
deliberately limited set of definitions and proved results while the knowledge
blueprint records broader mathematical targets.

## Architectural Rules

### Keep assumptions local

Structures should store data, not avoidable assumptions. Add requirements such
as `[Fintype]`, `[DecidableEq]`, order, topology, or algebraic structure at the
definition or theorem sites where the mathematics needs them.

When arithmetic needs a field and an order, prefer the weakest suitable
Mathlib assumptions instead of hardcoding `ℝ`. Analytic results may genuinely
need `ℝ`; executable finite developments can often remain polymorphic and
instantiate to `ℚ`.

### Preserve layer boundaries

```text
Foundation/   Math/
      \       /
       domain modules
            |
         Examples/
```

- `Foundation/` contains shared vocabulary and helpers.
- `Math/` contains reusable mathematics and must not depend on EconCS domain
  modules.
- Domain modules may import `Foundation/` and `Math/`.
- `Examples/` contains worked examples and regression targets. It is not part
  of the root import surface.
- `OpenProblem/` contains experimental opt-in interfaces. It is not part of the
  root import surface.

### Prefer existing interfaces

- Search Mathlib before adding custom definitions, structures, or notation.
- Prefer stable predicates and standard types over wrapper abstractions that do
  not remove real complexity.
- Use targeted imports in new files. Avoid `import Mathlib` when a narrower
  import is clear.
- Add intended stable modules to `EconCSLib.lean`.

### Keep the stable Lean tree placeholder-free

Public Lean source under `EconCSLib/` must not contain ordinary `sorry` or
`admit`.
Mathematical targets that are not yet implemented belong in the knowledge
blueprint or issue tracker, not as deferred Lean declarations.

Experimental open-problem interfaces under `EconCSLib/OpenProblem/` have one
scoped exception: theorem statements may use `answer(sorry) ↔ P := by sorry` to
record an unresolved yes/no answer in the style of Formal Conjectures. This
exception is checked by `scripts/check_lean_placeholders.py`; ordinary `sorry`
and all `admit` uses remain forbidden.

## Source Layout

| Area | Purpose |
|------|---------|
| `Foundation/` | players, preferences, profile compatibility, argmax, ordered-group helpers, utility theory, lotteries, vNM axioms, and `CostM` |
| `Math/` | fixed-point theorems, simplex helpers, reusable discrete probability, linear algebra, linear programming, and minimax |
| `GameTheory/GameForm.lean`, `GameTheory/GameForm/` | stable aggregate plus representation-neutral deterministic, law-valued, and continuation-family semantics, with composable realization and functional/relational Nash-on-declared-roots transfer morphisms; representation-aware standard SPE remains in the EFG layer |
| `GameTheory/StrategicGame/` | strategic games, equilibrium, dominance, checkers, mixed strategies, ESS, IESDS, correlated-equilibrium foundations, potential games, and zero-sum games |
| `GameTheory/ExtensiveGame/` | Arena/history-based extensive games, finite tree frontends, observed information, execution, objectives, equilibrium, relations and compilers. Start with the conceptual and worked-example routes in `design/extensive_game.md`; use `design/efg-document-authority.md` to locate policy and `design/efg-public-api.md` to choose imports. `Interface.StructuralCore` is the narrow structural facade, `Interface.Core` is the broader Foundation Facade, Canonical/Frontend API growth is frozen, and carrier compatibility remains unfrozen while the documented universe/import regressions stay active. |
| `GameTheory/CoalitionalGame/` | transferable-utility games, the core, and Shapley-value infrastructure |
| `SocialChoice/` | social-choice vocabulary, voting theory, and fair division |
| `MarketDesign/Matching/` | matching markets and Gale-Shapley developments |
| `MechanismDesign/Auction/` | mechanism-design and auction infrastructure |
| `Examples/` | opt-in examples and executable regression targets |
| `OpenProblem/` | opt-in experimental open-problem interfaces |

Generic horizon/outcome-parametric continuation semantics and their
assumption-explicit evaluator-relative transfer theorem are owned by the
payoff-free `Observed.Controlled.Semantics` module. An arbitrary evaluator is
not operational EFG execution and receives no generic standard-SPE name.
`Observed.Semantics` preserves the state-payoff `ObservedGame` spelling only
as a downstream compatibility adapter; state payoffs are not an input to the
generic evaluator or theorem.
`ObservedGame.ofControlledObservedGame` attaches any caller-supplied state
payoff without rebuilding the observation carrier, and projecting the result
back is definitional.
The controlled hierarchy is classified by role in
[`design/efg-controlled-api.md`](design/efg-controlled-api.md); governance
forbids new flat `Observed.ControlledFoo` siblings and prevents payoff-aware
adapters from becoming canonical implementation dependencies.

## Design Choices

### Profiles are game-bound

For strategic games, a profile belongs to a specific game: `G.Profile`.
Foundation-level profile vocabulary exists only where it provides reusable
compatibility helpers.

### Extensive games use arenas

The extensive-form layer uses an arena and state-space model so infinite-state
and infinite-horizon games remain representable. Separate finite-tree modules
support backward induction and executable examples.
The four-record minimal carrier
`Arena → ControlledGame → ControlledDecisionGame → ControlledObservedGame` is
still under review and is not compatibility-frozen. The final observation
extension is optional for analyses that need only decision information and
strategies. Canonical/Frontend API growth is separately frozen, so new
capabilities remain in the knowledge blueprint or opt-in Experimental work
unless that policy is explicitly reopened. Changes to existing payoff,
probability, objective, recall, finiteness, root-selection, or
solution-concept boundaries still require a demonstrated representation
failure that cannot be handled by an external certificate, adapter, or
compiler.
Bijective player renamings use
`ControlledObservedGame.relabelPlayers`; this leaves Arena histories
definitionally unchanged and reindexes dependent strategy profiles without
placing player maps in the minimal record.

Common observed-game record literals should use the orthogonal presentation,
root, and chance constructors audited in
[`docs/design/observed-game-constructors.md`](design/observed-game-constructors.md).
These constructors deliberately do not infer movers, payoffs, public
disclosure, subgame lawfulness, or chance probabilities.
The finite `GameTree`, `StochasticGameTree`, `ZeroSumChance.GameTree`, and
`FiniteImperfectGame` roles and their canonical routes to
`ObservedChanceGame` are audited in
[`docs/design/efg-representation-compilation.md`](design/efg-representation-compilation.md).
The additive target architecture for finite, well-founded, almost-surely
terminating, and genuinely infinite EFGs, including path objectives and
logical winning conditions, is specified in
[`docs/design/efg-general-foundations.md`](design/efg-general-foundations.md)
and its continuations for
[`strategies and solutions`](design/efg-general-foundations-2-strategy.md) and
the implementation-oriented
[`Lean API notes`](design/efg-general-foundations-3-lean-api.md). Current
theorem gaps belong in focused boundary notes and staged knowledge nodes rather
than a second delivery roadmap.
Lifecycle, frontend/historical boundaries, root-import policy, and the complete
module register are maintained in
[`docs/design/efg-governance.md`](design/efg-governance.md) and
[`docs/design/efg-module-status.md`](design/efg-module-status.md).

Discrete stochastic execution uses executable `FiniteLaw` values with exact
rational weights. A separate measurable
kernel arena admits non-atomic one-step transition laws and receives an exact
embedding of the discrete layer. Its measurable action-policy interface
produces a normalized terminal-absorbing one-step kernel and recovers the
discrete policy step exactly. Finite iteration produces normalized endpoint
kernels and recovers every discrete `stateLawFrom` exactly. An
Ionescu--Tulcea construction supplies a normalized infinite discrete-event
state-path law whose coordinate marginals are exactly those endpoint laws.
A payoff-free `CompletePathLawSemantics` packages strategy-indexed full
history-path laws only when each law is a probability measure, is almost
surely a canonical terminal-absorbing legal play, and carries caller-supplied
bounded coordinate laws equal to its marginals. The discrete behavioral
adapter consumes a supplied complete law and certifies agreement with every
executable `FiniteLaw` prefix; the analytic-kernel adapter packages its
separately owned path measure. Local execution coherence remains a separate
certificate.
The exact ownership, facade, adapter direction, and unsupported claims for
the structural, finite-law, infinite discrete, analytic-kernel, and FOSG
regimes are governed by
[`docs/design/efg-semantic-universes.md`](design/efg-semantic-universes.md).
Executable finite definitions are the primary operational representation for
effective models. The general carrier and theorem domains remain unchanged.
Their analytic interpretations are connected by the separately governed
[`semantic compatibility contract`](design/efg-semantic-compatibility.md).
Together they form two execution/probability tracks over one shared structural
EFG layer; representation-neutral theory is not duplicated.
The executable layer owns values; analytic leaves retain the wider mathematical
semantics; named equality, approximation, or almost-everywhere theorems state
exactly what crosses the boundary. Analytic declarations are not lifecycle
legacy merely because a finite effective subdomain is executable.
A second policy interface permits time- and finite-state-prefix-dependent
action kernels and contains the stationary state-Markov executor exactly.
Analytic observed strategies live in a separate higher layer with
kernel-valued player laws, a fixed realized chance kernel, and an exact
embedding of the finite rational-law subcase. Constructive profile assembly uses
an explicit measurable player-tag space and measurable terminal/player role
sets; it does not infer ownership measurability or measurable selection.
Unilateral replacement is implemented by measurable singleton branching,
and finite-law profiles split and reassemble with exactly the same compiled
event policy. Measurable path utilities require explicit integrability;
uniformly bounded utilities are integrable for every admitted profile and
support constructive Nash comparison. Terminal payoff evaluation additionally
requires either an explicit finite-horizon termination certificate or
almost-sure eventual terminal absorption, avoiding any implicit payoff
assignment to nonterminating paths. In the latter case, bounded stopped
utility converges almost everywhere and in expectation to the explicitly
zero-guarded eventual terminal payoff. A fair repeat-or-stop regression has
unfinished mass exactly `2⁻ⁿ`, so it terminates almost surely while satisfying
no finite `TerminatesBy` certificate. Root-parameterized execution is exposed
in two deliberately separate forms. Canonical **absolute-prefix
continuation** encodes the complete dependent history as a joint state/action
event prefix, starts Ionescu--Tulcea execution at the history depth, and
tail-indexes the resulting future path. The older arbitrary-root executor is
retained as explicitly qualified **fresh-clock restart** semantics: it resets
the presentation's time index to zero and supplies no earlier event prefix.
Neither construction is identified with conditioning. A strict two-stage
time-dependent regression proves the distinction at the executed-path level:
the same latest state yields different Dirac recorded-action marginals and
therefore different future path probability measures under fresh time zero
and retained absolute time one. A separate finite deterministic regression
proves strict equilibrium refinement: one profile attains the uniform payoff
bound and is therefore Nash against every admitted deviation at the initial
history, while a certified deviation raises continuation payoff from zero to
one at a probability-zero off-path subgame, so the profile is not
absolute-prefix subgame perfect.
Conditional compatibility is exposed at its lawful boundary. Under an
explicit standard-Borel assumption on the shifted future event-path space,
the regular conditional shifted-path kernel agrees almost everywhere with
constructive continuation. The equality is pointwise at a finite prefix only
when that prefix is a nonzero marginal atom, where the usual normalized
joint-mass formula is valid. At a zero-mass prefix the normalized expression
cannot be the constructive probability law, so no canonical conditional
version is claimed there.
Fresh-restart compatibility is also explicit rather than automatic. At the
event level, comparison first replaces only absolute continuation coordinate
zero's retained incoming-action occurrence by the fresh initial marker; raw
event-path equality would generally be false for every nonempty history even
when all future behavior agrees. Normalized full-event compatibility implies
state-path compatibility, and state-path compatibility is equivalent to
equality of every finite state-prefix marginal. Fresh and absolute
bounded-utility designated-root Nash, subgame-perfection-on, and complete standard SPE are equivalent only when this state-law equality
holds for both the baseline profile and every admitted unilateral deviation.
The strict clock regression remains unequal even after the coordinate-zero
normalization.
A measurable splice now isolates the remaining proof obligation. It retains
the complete absolute prefix through the continuation time and attaches fresh
coordinates `1, 2, ...` afterward. Tail shifting and root-marker
normalization send the spliced probability law exactly back to the fresh
path law. Thus equality of the actual absolute trajectory with the spliced
trajectory is a sufficient full-event compatibility certificate, and it is
equivalent to equality of all complete finite absolute-prefix marginals.
`IsFreshRestartPartialStepCompatibleAt` now gives a local distributional
criterion: at every offset, the next spliced-fresh finite-prefix law must be
the current spliced law advanced by the actual absolute one-step
`partialTraj` kernel. Induction proves the full trajectory certificate and
therefore normalized event, state, expected-utility, designated-root Nash, subgame-perfection-on, and complete standard-SPE transfer.
This exact distributional recurrence is now implied by
`IsFreshRestartStepKernelCompatibleAt`: for almost every prefix under each
generated fresh finite-prefix law, one fresh step followed by finite splicing
must agree with finite splicing followed by the actual absolute-clock step.
The stronger pointwise variant is convenient for structural models, while
the almost-everywhere variant adds no constraint on generated-null prefix
sets. Both certificates lift through deviation-complete designated-root Nash, explicit subgame-perfection-on, and complete standard SPE, and the
strict clock model formally fails both.
A weaker structural alternative now quantifies pointwise only over finite
fresh prefixes whose coordinate zero is the canonical initial event.
Generality here requires care: that fixed-point predicate need not be
measurable on an arbitrary measurable event carrier. Rather than assert a
false concentration theorem, the library proves the fresh finite-prefix law
is invariant under canonical-root replacement and integrates the rooted
pointwise equality through that reset. The rooted certificate also lifts to
deviation-complete designated-root Nash, explicit subgame-perfection-on, and complete standard SPE and is formally refuted by the strict clock
model.
The rooted condition can now be checked one layer lower through
`IsFreshRestartRootedPathStepKernelCompatibleAt`, which compares the
primitive next-event `pathStepKernel` laws at matching fresh and spliced
prefixes. Deterministic one-event extension commutes with finite splicing,
and projection to the newest event proves the converse, so this primitive
condition is exactly equivalent to the rooted successor-`partialTraj`
condition. The strict clock regression locates its failure at offset zero.
`IsFreshRestartRootedActionKernelCompatibleAt` descends once more to the
behavioral action measure. Rooted matching proves the fresh and spliced
prefixes have the same latest state and hence the same terminal branch.
Nonterminal equality is preserved by the common recorded transition; the
converse follows by projecting each next event to its recorded action and
using measurable-embedding injectivity of `Sum.inr`. Thus the action,
primitive event-step, and rooted successor-prefix certificates are all
formally equivalent. The deviation-complete action form has direct designated-root Nash, subgame-perfection-on, and complete standard-SPE
entry points, and the strict clock example refutes it at offset zero.
A separate `IsFreshRestartRootedActionKernelCompatible` proposition
quantifies the same action rebasing law over every retained start and prefix.
It is deliberately root-uniform and therefore stronger than any one
root-scoped certificate. The observed and deviation-complete wrappers turn
that single structural premise into compatibility at arbitrary root
predicates, including the roots of any separately supplied lawful subgame
system; the strict clock policy directly refutes it.
Reusable sufficient constructors now factor a raw behavioral policy through
a fixed-codomain measurable `EventHistoryStatistic` and one common action
kernel. It is enough for the resulting action measures to be invariant
between every canonically rooted fresh prefix and its absolute splice;
literal equality of statistic values is a stronger convenient
specialization. The statistic converts exactly to the existing
`EventInformation` layer, and its induced information policy compiles back to
the original raw policy. Latest state is invariant, so every stationary
state-Markov policy obtains the certificate automatically. A statistic that
retains absolute clock together with latest state need not itself be
invariant, while a clock-ignoring action kernel still is. These are only
sufficient factorization theorems: no converse for arbitrary root-uniform
policies is asserted, and the strict clock policy cannot admit a
behaviorally invariant factorization.
The remaining fixed-codomain restriction is removed at the existing
`EventInformation` layer. `FreshRestartRebase` measurably transports
information at absolute time `start + offset` to the possibly different
information type at fresh time `offset`, may depend on the retained prefix,
and need not be invertible. A rooted-splice law for the transport together
with naturality of the time-indexed information action kernels implies the
same root-uniform certificate after compilation. A `Fin (time + 1)`
regression demonstrates genuinely changing information types: a stationary
policy is natural and compatible, while an absolute-clock-sensitive policy
has the same lawful rebase but fails both naturality and compiled
compatibility.

### Mixed strategies use `stdSimplex`

The strategic-game mixed layer builds on Mathlib's `stdSimplex`, with reusable
computational lemmas factored into `Math/Simplex.lean`.

### Fair division lives under social choice

Fair division lives under `SocialChoice/FairDivision/`. Indivisible and
divisible resource models share generic vocabulary while keeping specialized
theorem tracks.

## Documentation

- [`design/`](design) contains focused API design notes.
- [`research/`](research) contains selected durable rationale and proof routes.
- [`maintainers/`](maintainers) documents publishing workflows.
- [`knowledge/`](knowledge) is the editable source for the generated knowledge
  blueprint.

Completed execution plans and private work logs do not belong in the public
repository. Use GitHub Issues for actionable tasks and blueprint nodes for
broader mathematical gaps.

## Source References

Recurring sources are registered in
[`knowledge/mdblueprint.yml`](knowledge/mdblueprint.yml) with publisher links.
Do not commit textbook PDFs, scans, or OCR-derived material.
