# General EFG Foundations: Information, Strategies, and Solutions

This is the conceptual continuation of
[`efg-general-foundations.md`](efg-general-foundations.md). Section numbering
continues from that document. The Lean interface continues in
[`efg-general-foundations-3-lean-api.md`](efg-general-foundations-3-lean-api.md).

Status: target architecture. Existing Lean source remains authoritative until
each item is implemented and governance-registered.

## 7. Information and recall

The existing presentation already encodes the textbook common-action
requirement: `InfoAction i I` is transported by an equivalence to the concrete
legal action type at every history represented by `I`.

Retain the following distinction:

- `Observation i` is the current signal at every history;
- `InfoState i` is the acting player's complete decision-memory state;
- `infoObserve` forgets memory and returns the current signal.

`InfoState` is the raw information/memory carrier. `RepresentedInfo`, the
subtype witnessed at a genuine decision, is authoritative for strategy
measurability and information consistency.

Add reusable predicates rather than fields:

- `AllDecisionInfoRepresented`: every declared information state has a
  `DecisionInfoWitness`;
- `HasEventClockSignalPerfectRecall`: the per-transition signal sequence
  available to a player factors through its current `InfoState`;
- `HasEventClockPublicPerfectRecall`: the per-transition public-observation
  history factors through the current public state where required;
- `SignalTraceBuilder.HasPerfectRecall`: optional asynchronous trace recall
  when transitions may emit `none` as a silent event;
- finite strategy hypotheses quantify directly over `RepresentedInfo`.

The existing `HasPerfectRecall` remains the classical own-information and
own-action condition used by Kuhn's theorem. Signal recall is an independent
no-forgetting condition for private signals: it is neither substituted for
classic recall nor asserted to imply it. Both notions imply
no-absent-mindedness for their separate reasons. The signal proof uses the
explicit encoding law `signalHistory_length`: every legal action appends
exactly one signal coordinate. `RecallHierarchy.lean` contains payoff-free
regressions in all relevant directions: classic recall without public recall,
private-signal recall without public recall, public recall without
private-signal recall, and public recall without classic recall.

Unrepresented information states are allowed in the raw carrier and are
ignored by strategies. Full representation is required only when an external
format promises that every catalogued raw value occurs.

## 8. Strategy taxonomy

| Strategy | Intended type | Semantic role |
|---|---|---|
| Pure | one `InfoAction` at every `RepresentedInfo` | deterministic contingent plan |
| Behavioral | one local action law at every `RepresentedInfo` | fresh local randomization |
| Discrete mixed | `PMF` on pure strategies | countably supported ex-ante randomization |
| Analytic mixed | probability measure on a measurable pure-strategy space | non-discrete ex-ante randomization |
| Discrete general | `PMF` on behavioral strategies | countably supported random behavioral plan |
| Analytic general | probability measure on a measurable behavioral-strategy space | textbook general strategy in full generality |
| Quasi | a nonempty set of actions at each represented information coordinate | nondeterministic permission, not probability |

The canonical discrete names are `DiscreteGeneralStrategy` and
`DiscreteGeneralProfile`; the shorter former names were removed during
pre-stability rather than retained as compatibility aliases. New analytic
variants live in the analytic layer and
require explicit measurable structures. Do not claim that `PMF` represents
every mixed or general strategy on an infinite or continuous strategy space.

Kuhn results are realization theorems:

- under perfect recall, a mixed plan has a behavioral realization relative to
  the stated root and opponent semantics;
- under no absent-mindedness and finite decision information, independently
  pre-sampling a behavioral table realizes repeated behavioral execution;
- neither result is a literal isomorphism of raw strategy types;
- a root-independent behavioralization of an arbitrary correlated mixed plan
  must not be asserted without stronger hypotheses.

`BoundedCompleteHistorySemantics` now makes the preserved object explicit and
classifies both the strategic mode and chance semantics. Its realization map
commutes with every source unilateral update; reverse target-deviation
coverage is a separate predicate. The infinite counterpart,
`CompletePathLawSemantics`, compares the full path measure rather than only
finite marginals. A concrete mixed-to-behavioral equality for that maximal
infinite law remains a theorem track.

## 9. Solution concepts

Utility and winning semantics share strategies but have different solution
notions.

### 9.1 Utility games

- Nash compares utility at the initial root.
- Nash on continuations uses an explicit caller-selected
  `RootPresentation`.
- standard SPE quantifies over a complete lawful subgame system.
- sequential equilibrium additionally needs beliefs, Bayes consistency, and
  sequential rationality; it is a later assessment layer, not an
  `ObservedGame` field.

### 9.2 Logical games

Two predicates are required:

- `HasPathwiseWinningStrategy W i sigma` means every complete legal play
  locally compatible with `sigma` is in `W i`, regardless of whether the
  opponent coordinates can be generated by one information-consistent
  profile;
- `HasStrategicWinningStrategy hNoChance W i sigma` quantifies over all pure
  profiles extending `sigma`.

Pathwise winning plus `HasPureProfileExtension` implies profile-based winning.
The extension witness prevents a vacuous win when another player's strategy
type is empty. The converse requires the explicit
`EveryCompatiblePlayRealizableByPureProfile` hypothesis and may fail when an
opponent information state is revisited. The `WinningSemantics` regression
proves this failure.

Keep `IsTwoPlayerDetermined W` independent from `IsTotal W`. For arbitrary
player types use the descriptive `HasSomePathwiseWinningStrategy`; do not
overload the standard determinacy name. The first theorem track is two-player,
no-chance, perfect-information play; its finite-bound step is now proved:

```text
finite decision bound -> determined                    [proved]
Acc-certified prefix well-foundedness -> determined
closed/open winning condition -> Gale-Stewart determinacy
```

Arbitrary winning sets are not determined in ordinary set theory. Finite
imperfect-information games are not determined in general. Both boundaries
require negative regression examples.

For chance games distinguish:

- robust winning: quantify over every legal nature move;
- almost-everywhere winning under an arbitrary measure:
  `AEWinningUnder`;
- almost-sure winning: require `IsProbabilityMeasure` for the fixed law and
  winning-path measure one.

These predicates are not interchangeable.

## 10. Finite textbook EFG profile

Do not add a second canonical finite semantic record. Define a reusable
certificate over `ObservedChanceGame`:

```text
FiniteEFGHypotheses G
```

with, at minimum:

- a uniform structural length bound;
- finite legal action types on represented histories;
- finite player type when a theorem enumerates profiles;
- finite `RepresentedInfo` carriers for algorithms that enumerate strategy
  coordinates;
- decidable terminal and mover tests only for executable constructions.

Perfect recall, no chance, zero sum, total preferences, and decidable utility
comparison are separate theorem hypotheses.

Decision-mover coherence is not imposed on `ExtensiveGame`: execution ignores
the mover at a terminal state, and `IsDecision` prevents such an endpoint from
entering `RepresentedInfo`. Every represented coordinate is inhabited by
transporting the action in its decision witness through `actionEquiv`.

Finite state is neither necessary nor sufficient: a finite-state arena may
cycle, while an infinite ambient state type may have a finite reachable
unfolding. Algorithms should consume the finite reachable history tree
extracted from the certificate.

Existing `GameTree`, `StochasticGameTree`, and `FiniteImperfectGame` remain
frontends. Their compilers should produce the relevant certificate when their
source assumptions justify it.

## 11. Preservation contract

Every new compiler, embedding, or extraction states exactly which of the
following it preserves:

1. complete histories or only endpoints;
2. action occurrences and information states;
3. public and private observations;
4. chance laws;
5. complete-play or terminal-outcome laws;
6. unilateral deviations;
7. perfect recall;
8. designated roots or complete lawful subgames;
9. length/well-foundedness certificates;
10. winning conditions or utility interpretations.

Use `Hom`, realization, refinement, simulation, or coupling according to the
actual strength. Reserve `Iso` for bijective data and commuting semantic
diagrams.

The maintained relation-by-relation table is
[`efg-preservation-matrix.md`](efg-preservation-matrix.md).

## 12. References

- Maschler, M., Solan, E., and Zamir, S. *Game Theory*. Cambridge University
  Press, 2013, especially the finite extensive-form, information-set, and
  perfect-recall material reviewed on pp. 43, 54, and 231.
- Laraki, R., Renault, J., and Sorin, S. *Mathematical Foundations of Game
  Theory*. Springer, 2019, especially mixed, behavioral, and general
  strategies, perfect recall, Kuhn's theorem, and subgames on pp. 109-114.
- Hodges, W. and Vaananen, J. "Logic and Games." *Stanford Encyclopedia of
  Philosophy*, substantive revision 2024-12-12:
  <https://plato.stanford.edu/entries/logic-games/>.
