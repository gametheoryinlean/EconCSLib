# Observed-game presentation constructors

This note records the boilerplate audit and the supported smart constructors
for `ObservedGame` and `ObservedChanceGame`. It is part of the
[extensive-game design](extensive_game.md); the public import policy remains
defined by [efg-public-api.md](efg-public-api.md).

## Audit

A mechanical field-label scan of `Examples/ExtensiveGame/`,
`GameTheory/ExtensiveGame/Compiler/`, and the FOSG sequentializer found 15
observed-presentation field groups in 14 files before the migrations in this
change. A raw `ObservedGame` literal commonly repeated observation,
information, and the former two root-selection fields. Twelve presentations
selected every complete history with the same two-line `True` predicate and
`trivial` initial proof. Root selection is no longer part of the record.

The repeated presentations were not all semantically interchangeable:

| Pattern | Repeated data | Correct treatment |
|---|---|---|
| Complete-history private observation and legacy all-history information, direct base actions | `Observation`, `observe`, `InfoState`, `infoObserve`, `infoAt`, `InfoAction`, `actionEquiv`, and their two laws | `historyInformation` |
| Complete-history observation with mover-indexed perfect information | history observation plus player-labeled decision-history subtypes | `decisionHistoryInformation` |
| Canonical complete information | decision-only information plus identity public projection | root-free `completeInformation` |
| Trivial public observation | `Unit`, two constant functions, compatibility by `rfl` | `PublicObservationPresentation.trivial` |
| All histories presentation-designated | `fun _ => True`, proof `trivial` | `ContinuationRootPresentation.allHistories` |
| Initial history only | equality with the empty history | `ContinuationRootPresentation.initialOnly` |
| Initial lawful subgame system | the same equality plus the whole-game lawfulness proof | `SubgameSystem.initialOnly` |
| Chance extension | an `observed` field plus a caller-defined `PMF` kernel | `ObservedChanceGame.withChanceKernel` |

The endpoint-observed `GameTree` compiler, imperfect-information compiler,
FOSG sequentializer, absent-minded-driver example, and sparse-player examples
retain hand-written structures. Their information types, public quotients,
action equivalences, or root predicates encode real model semantics rather
than constructor noise.

## Stable constructors

The following constructors are intentionally small and composable.

| Declaration | What it supplies | What remains explicit |
|---|---|---|
| `ExtensiveGame.ofArena` | reuses an `Arena`'s state, action, and transition fields | initial state, mover, payoff |
| `ObservedGame.historyInformation` | complete-history private observation and a legacy all-history information carrier; direct `Arena.Action` fibers | public projection; roots are external |
| `ObservedGame.decisionHistoryInformation` | complete-history private observation and exactly player-mover-labeled histories as information states | public projection, mover coherence; roots are external |
| `ObservedGame.completeInformation` | decision-history perfect information with the complete history also public | mover coherence; roots are external |
| `ObservedGame.ContinuationRootPresentation.initialOnly` | presentation metadata selecting only the empty history | observation and chance semantics |
| `ObservedGame.ContinuationRootPresentation.allHistories` | presentation metadata selecting every legal complete history | any standard-subgame lawfulness claim |
| `ObservedGame.SubgameSystem.initialOnly` | the smallest lawful system, containing only the whole game | completeness and additional lawful roots |
| `ObservedChanceGame.withChanceKernel` | attaches exactly the supplied normalized kernel | every chance law |
| `ObservedChanceGame.completeInformation` | root-free complete information plus the supplied discrete kernel | every chance law and external roots |

`Interface.Core` exposes the arena/game, public-projection, root, and
`ObservedGame` constructors. The chance constructors first appear through
`Interface.Execution.Finite`. This is enforced in
`Examples/ExtensiveGame/CoreImportBoundary.lean` and
`FiniteExecutionImportBoundary.lean`.

All data-only constructors above are reducible abbreviations. The legacy
constructor reuses complete-history instances definitionally. The canonical
constructor's `InfoState i` is a mover-equality subtype: `Finite` is inherited
from finite histories without a decidability premise, while constructing a
`Fintype` for the subtype additionally needs decidable membership. The
constructors do not add global instances or new typeclass premises to
`ObservedGame`.

For analytic execution, continue to use the existing
`ObservedGame.MeasurableHistoryModel.discrete` (or its observed-chance
compatibility spelling). It supplies top measurable spaces and discharges the
discrete transition, terminal-set, and singleton measurability obligations.
No duplicate measurable-presentation abstraction was introduced.

## Before and after

The two migrated examples previously used the following shape:

```lean
def observed : ObservedGame N U where
  base := base
  Observation := fun _ => History
  PublicObservation := Unit
  observe := fun _ history => history
  publicObserve := fun _ => ()
  publicOf := fun _ _ => ()
  observe_public := fun _ _ => rfl
  InfoState := fun _ => History
  infoObserve := fun _ history => history
  infoAt := fun history _ _ => history
  infoAt_observe := fun _ _ _ => rfl
  InfoAction := fun _ history => base.Action history.1
  actionEquiv := fun _ _ _ => Equiv.refl _
```

They now use:

```lean
def observed : ObservedGame N U :=
  ObservedGame.historyInformation base
    (ObservedGame.CompleteInformation.PublicObservationPresentation.trivial
      base)

def roots : observed.RootPresentation :=
  ObservedGame.ContinuationRootPresentation.allHistories base
```

Because the constructor is reducible, this replacement is definitionally the
same observation/information record, including the former `Unit` public
observation. Changing `roots` does not construct a different `ObservedGame`.
No isomorphism, cast, or downstream strategy conversion is required.

## Deliberately unsafe or semantic fields

The following data must not be inferred by a convenience constructor:

- `ExtensiveGame.ofArena` cannot infer `init`, `mover`, or `payoff`. A bare
  arena is not yet a game.
- `historyInformation` deliberately uses every complete history as the raw
  `InfoState` carrier. Strategies nevertheless range over `RepresentedInfo`,
  so histories where the player does not genuinely decide do not become
  coordinates. Prefer `decisionHistoryInformation` or the canonical
  `completeInformation` when a smaller raw carrier is useful for enumeration
  or external interchange.
- `completeInformation` excludes chance, other-player, and terminal
  occurrences from represented coordinates through `IsDecision`. A base
  carrier may retain a player label at a terminal state; it is semantically
  ignored. Standard frontends may still normalize terminal movers to `none`.
- `PublicObservationPresentation.trivial` intentionally hides all public
  history. `fullHistory` intentionally reveals all of it. Neither choice is a
  harmless implementation detail.
- `ContinuationRootPresentation.allHistories` is external presentation
  metadata only.
  It does not prove that all histories are lawful standard-subgame roots.
- `SubgameSystem.initialOnly` is lawful but conservative. It does not prove
  that no later lawful subgames exist.
- A `chanceKernel` is supplied by the model author. `PMF` enforces
  normalization, but the constructor cannot derive probabilities from mover
  or action data.
- `MeasurableHistoryModel.discrete` uses top measurable spaces. On
  uncountable carriers this does not by itself provide the standard-Borel or
  product-measurability facts required by stronger analytic results.
- `DecidableEq`, `Fintype`, and measurable structures are reused only when
  they already exist on the underlying history/action carriers. The
  constructor does not assert that a finite state type induces finitely many
  histories; cycles can produce infinitely many histories.

These boundaries are semantic and cannot be enforced solely by Lean's import
mechanism. Naming, docstrings, explicit constructor arguments, and the
separation between presentation roots and lawful `SubgameSystem`s are the
enforcement mechanism.
