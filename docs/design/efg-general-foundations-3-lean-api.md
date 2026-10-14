# General EFG Foundations: Lean API Plan

This is the implementation continuation of
[`efg-general-foundations-2-strategy.md`](efg-general-foundations-2-strategy.md).
Section numbering continues from the foundation documents. Current gaps and
future proof targets live in focused boundary notes,
[`efg-mathematical-provenance.md`](efg-mathematical-provenance.md), and staged
knowledge nodes rather than a separate delivery roadmap.

Status: Phase A, the foundational Phase B/D carriers, and finite plus
structurally well-founded perfect-information logical determinacy are
implemented; later arbitrary infinite/topological determinacy and analytic
theorem modules remain target architecture. Names marked as
proposed may be adjusted during implementation. No listed theorem is
considered formalized until a placeholder-free Lean declaration exists.

Implemented through 2026-08-01:

- `Execution/CompletePlay.lean`;
- `Execution/Length.lean`;
- `Execution/Objective.lean`;
- `Observed/WellFormed.lean`;
- `Observed/Quasi.lean`;
- `Observed/General.lean`;
- `Winning/Basic.lean`;
- the determinacy predicate/hypothesis boundary and finite
  perfect-information two-player zero-sum theorem in
  `Winning/Determinacy.lean`;
- `Winning/Chance.lean`;
- `Interface/Objective.lean`;
- `Interface/Winning.lean`;
- `Interface/Winning/Stochastic.lean`;
- the exact deterministic stopped-execution complete-play bridge;
- the almost-everywhere discrete infinite path-law legality bridge;
- the structural finite-EFG to finite-Kuhn hypothesis adapter;
- finite-state looping and unbounded-height well-founded regressions.
- canonical decision-only complete-information strategy domains;
- root-prefix replay through `CompletePlayFromHistory.resume`;
- separate pathwise/profile-based winning predicates and their exact bridge;
- probability-certified almost-sure winning;
- explicit discrete-general strategy names;
- a payoff-free, normalized, almost-surely lawful complete-path carrier;
- discrete behavioral and analytic-kernel adapters to that common carrier;
- distinct same-game, cross-game functional, and coupling relations.

## 13. Module and import plan

New declarations should be placed at the lowest layer that can state them
honestly.

| Module | Lifecycle | Responsibility | Public exposure |
|---|---|---|---|
| `Basic.lean` | Canonical, implemented | payoff-free `ControlledGame`; state-payoff `ExtensiveGame` compatibility extension | `Interface.Core` |
| `Execution/CompletePlay.lean` | Canonical, implemented | measure-free terminal-absorbing legal plays and prefix/splice operations | `Interface.Core` |
| `Execution/Length.lean` | Canonical, implemented | uniform length and `Acc`-based well-foundedness certificates | `Interface.Core` |
| `Execution/Objective.lean` | Canonical, implemented | terminal histories and deterministic terminal/path outcomes | `Interface.Objective` |
| `Interface/Objective.lean` | Canonical, implemented | governed pre-stability measure-free objective facade | explicit opt-in |
| `Observed/WellFormed.lean` | Canonical, implemented | represented-information and finite-EFG hypothesis packages | `Interface.Core` |
| `Observed/Controlled.lean` | Canonical, implemented | payoff-free observations/information, bijective player/profile reindexing, and external root presentation | `Interface.Core` |
| `Observed/Controlled/Infrastructure.lean` | Canonical facade, implemented | declaration-free access to the focused infrastructure leaves | broad controlled infrastructure clients |
| `Observed/Controlled/Infrastructure/{Core,WellFormed,Subgame,Finite,Quasi,Recall}.lean` | Canonical, implemented | payoff-free controlled execution, general represented-information/mover coherence, lawful subgames, finite-EFG hypotheses, quasistrategies, and recall in separate owners | `Interface.Core` |
| `Observed/Controlled/Morphism.lean` | Canonical facade, implemented | declaration-free access to structural, lawful-subgame, and recall transport | broad relation clients |
| `Observed/Controlled/Morphism/Core.lean` | Canonical, implemented | payoff-free Hom/Iso, information refinement, strategy transport, root-presentation comparison, and Iso algebra | `Interface.Relations.Discrete` |
| `Observed/Controlled/Morphism/{Subgame,Recall}.lean` | Canonical, implemented | lawful-subgame transport and recall preservation/reflection | `Interface.Relations.Discrete` |
| `Observed/Controlled/Compat/Morphism.lean` | Internal adapter, implemented | payoff commuting square and legacy `ObservedGame.Iso` projection | compatibility consumers |
| `Observed/Controlled/Law/Discrete.lean` | Canonical, implemented | payoff-free discrete chance and bounded complete-history PMFs | `Interface.Execution.Finite` |
| `Observed/Controlled/Law/DiscretePath.lean` | Canonical adapter, implemented | actual PMF behavioral executor packaged as the common lawful path probability | `Interface.Execution.Infinite` |
| `Observed/Controlled/Law.lean` | Canonical, implemented | payoff-free normalized/lawful per-root path marginals, measurable interpretation hierarchy, execution coherence, and same/cross-game realizations | `Interface.Preservation`; add `Interface.Execution.Analytic` for analytic execution |
| `Observed/Controlled/Law/Analytic.lean` | Canonical adapter, implemented | actual measurable-kernel state/history path law packaged in the common carrier under explicit legality | `Interface.Execution.Analytic` |
| `Observed/FiniteUnfolding.lean` | Canonical, implemented | finite occurrence-sensitive carrier with strict structural, recall, root/subgame, chance, deviation, and bounded-law preservation | `Interface.Execution.Finite` |
| `Observed/SignalRecall.lean` | Internal adapter, implemented | legacy payoff-aware private/public recall names projected from `Controlled.Infrastructure` | downstream compatibility |
| `Observed/LawEquivalence.lean` | Canonical, implemented | bounded history/terminal/payoff-law hierarchy and concrete Kuhn realizations | `Interface.Equilibrium.Discrete` |
| `Observed/Quasi.lean` | Internal adapter, implemented | legacy payoff-aware quasistrategy names projected from `Controlled.Infrastructure` | downstream compatibility |
| `Observed/General.lean` | Canonical, implemented | discrete general-strategy carriers and embeddings | discrete equilibrium facade |
| `Simulation/Equilibrium/General.lean` | Internal | measurable mixed/general strategy laws and expected utility | analytic equilibrium facade |
| `Winning/Basic.lean` | Canonical, implemented | winning conditions, totality, exclusivity, prefix decisions, and strategy compatibility | `Interface.Objective` |
| `Winning/Topology.lean` | Canonical, implemented | finite agreement cylinders, prefix topology, open/closed/measurable objectives | `Interface.Objective` |
| `Winning/Determinacy.lean` | Canonical, finite and well-founded theorems implemented | determinacy predicates and finite/well-founded hypothesis packages; structurally well-founded perfect-information existence is proved, while arbitrary infinite Gale--Stewart existence remains out of scope | `Interface.Winning` |
| `Relations/Preservation.lean` | Canonical, implemented | formal preservation-matrix certificates and compiler-specific packages | `Interface.Preservation` |
| `Winning/Chance.lean` | Canonical, implemented for discrete path laws | almost-sure winning under a fixed stochastic law, separate from robust winning | `Interface.Winning.Stochastic` |
| `Interface/Winning.lean` | Canonical, implemented | governed pre-stability probability-free logical-game facade | explicit opt-in |
| `Interface/Winning/Stochastic.lean` | Canonical, implemented | discrete infinite almost-sure-winning facade | explicit opt-in |
`Winning` is justified as a new family because it records objective data and
solution concepts that neither utility-valued `ExtensiveGame` nor
representation-neutral `GameForm` can express without loss.

The initial root import should remain unchanged. `Interface.Objective` and
`Interface.Winning` are opt-in governed boundaries during pre-stability.
Analytic general strategies remain opt-in permanently unless a later
root-policy review decides otherwise.

Each implemented module must be added to `efg-module-status.md`, and the
governance count must be updated in the same change.

## 14. Schematic API

The following signatures communicate dependency boundaries; they are not
promised source names.

### 14.1 Complete play

```lean
def Arena.IsChildFrom
    (A : Arena) (start : A.State)
    (child parent : A.HistoryFrom start) : Prop := ...

structure Arena.CompletePlayFromHistory
    (A : Arena) {start : A.State}
    (current : A.HistoryFrom start) where
  historyAt : Nat -> A.HistoryFrom start
  historyAt_zero : historyAt 0 = current
  step :
    forall n,
      (A.IsTerminal (historyAt n).1 /\
          historyAt (n + 1) = historyAt n) \/
      A.IsChildFrom (historyAt (n + 1)) (historyAt n)

abbrev Arena.CompletePlayFrom (A : Arena) (start : A.State) :=
  A.CompletePlayFromHistory (Arena.HistoryFrom.nil A start)
```

Required initial lemmas:

- endpoint/history length is monotone along `at`;
- before termination, one coordinate adds exactly one action;
- after the first terminal coordinate, all coordinates are equal;
- a terminal finite history has a unique absorbing complete-play extension;
- `append` and absolute-prefix splice preserve legality;
- the discrete PMF executor is almost surely legal; an analytic observed
  adapter supplies the same proof explicitly when its stochastic transitions
  represent canonical deterministic-history extensions.

If a subtype over the existing trajectory type yields cleaner reuse, prefer
that subtype to duplicating path storage.

### 14.2 Structural certificates

```lean
def Arena.HasLengthBoundFrom
    (A : Arena) (start : A.State) (bound : Nat) : Prop := ...

def Arena.IsWellFoundedFrom
    (A : Arena) (start : A.State) : Prop :=
  Acc (A.IsChildFrom start) (Arena.HistoryFrom.nil A start)
```

The primary forms should accept an arbitrary current absolute history; the
root forms above are abbreviations. `HasLengthBoundFrom` should have a
computable Boolean checker only for an explicit finite frontend. The canonical
`Prop` does not require decidable equality or a finite state type.

### 14.3 Objectives

```lean
abbrev Arena.TerminalHistoryFrom (A : Arena) (start : A.State) :=
  {h : A.HistoryFrom start // A.IsTerminal h.1}

abbrev Arena.TerminalOutcome
    (A : Arena) (start : A.State) (O : Type*) :=
  A.TerminalHistoryFrom start -> O

abbrev Arena.PathOutcome
    (A : Arena) (start : A.State) (O : Type*) :=
  A.CompletePlayFrom start -> O

abbrev Arena.WinningCondition
    (A : Arena) (start : A.State) (N : Type*) :=
  N -> Set (A.CompletePlayFrom start)
```

`WinningCondition` is an abbreviation or data-only wrapper. Totality,
exclusivity, prefix persistence, measurability, and Borel complexity remain
separate predicates.

### 14.4 Information support

Reuse `ObservedGame.DecisionInfoWitness`:

```lean
def ObservedGame.AllDecisionInfoRepresented (G : ObservedGame N U) : Prop :=
  forall i information,
    Nonempty (G.DecisionInfoWitness i information)
```

`RepresentedInfo` is now the canonical strategy coordinate. Full raw
representation remains an optional certificate for source formats that need
it; finite certificates quantify over represented coordinates directly.

### 14.5 Winning strategies

For a pure profile and player `i`, define play compatibility by requiring the
profile's abstract choice at every `i`-controlled coordinate to realize the
concrete successor action. Then:

```lean
def HasPathwiseWinningStrategy
    (W : A.WinningCondition start N)
    (G : ObservedGame N U)
    (i : N) (strategy : G.PureStrategy i) : Prop :=
  forall play, IsCompatibleWithPlayerStrategy G i strategy play ->
    play in W i
```

Quantification over all other player and nature moves gives robust winning.
Almost-sure winning is defined separately from a generated probability law.

For imperfect information, the selected player's consistency is structural
because its strategy is indexed by `RepresentedInfo`. Opponent coordinates in an
arbitrary compatible path need not be jointly strategy-consistent. Therefore
the implemented API also provides `HasStrategicWinningStrategy`, quantifying
over no-chance pure profiles with a nonvacuous
`HasPureProfileExtension` witness, and uses
`EveryCompatiblePlayRealizableByPureProfile` for the converse bridge. No
theorem may silently replace either side by a history-indexed
perfect-information policy.

### 14.6 General and quasi strategies

Discrete:

```lean
abbrev ObservedGame.DiscreteGeneralStrategy
    (G : ObservedGame N U) (i : N) :=
  PMF (G.BehavioralStrategy i)

structure NonemptyActionSet (Action : Type*) where
  allowed : Set Action
  nonempty : allowed.Nonempty

def ObservedGame.QuasiStrategy (G : ObservedGame N U) (i : N) :=
  (I : G.InfoState i) -> NonemptyActionSet (G.InfoAction i I)
```

Analytic mixed/general strategies use probability measures only after the pure
or behavioral strategy spaces receive explicit measurable structures and the
evaluation map is proved measurable.

## 15. Core proof obligations

### 15.1 Complete-play bridge

For every existing executor:

1. the initial coordinate is the supplied current history;
2. every successor coordinate is a legal extension or terminal stutter;
3. terminal absorption is pointwise or almost everywhere as appropriate;
4. coordinate marginals agree with existing finite execution;
5. terminal time agrees with the existing first-terminal stopping time;
6. path objectives agree after the new subtype/pushforward.

This bridge prevents a second infinite-execution implementation.

### 15.2 Terminal-objective bridge

Prove:

- the base endpoint payoff induces a terminal outcome;
- stopped terminal evaluation agrees with that outcome on termination;
- a uniform length bound removes `Option` from bounded outcome laws at a
  sufficiently large fuel;
- `AETerminates` plus the existing boundedness/integrability assumptions
  recovers the current terminal-payoff convergence results;
- absolute-prefix restriction commutes with terminal and path evaluation.

### 15.3 Finite extraction

From finite branching plus `HasLengthBoundFrom bound`, construct a finite
reachable-history frontend and prove:

- every extracted node is one original complete history;
- every original history of length at most `bound` is represented;
- actions, mover, information, chance, and terminal outcome commute;
- pure and behavioral deviations are covered;
- lawful roots are preserved in the stated direction;
- extraction is not called an isomorphism if it discards ghost information or
  unreachable ambient states.

Implemented now: finiteness of exact/bounded history carriers, the
occurrence-sensitive finite carrier, `Fintype` state/action instances, a
strict payoff-free observed isomorphism, legal action/mover/observation/
information equalities, discrete chance pullback, pure and behavioral
strategy equivalences, unilateral-update commutation, external root and
lawful-subgame transport, terminal/path objective pullback, classic/private/
public recall equivalences, merge distinction, the structural length bound,
and exact bounded complete-history PMF pushforward for every behavioral
profile. Full infinite path-law transfer remains a separate theorem track.

### 15.4 Recall and strategy support

Prove:

- finite represented information, rather than finite raw `InfoState`, is the
  strategy-space hypothesis;
- every represented coordinate has a nonempty action fiber directly from its
  constructive decision witness and `actionEquiv`;
- signal perfect recall implies the intended current-observation no-forgetting
  law;
- existing perfect recall remains exactly the own-information/own-action
  condition;
- strict morphisms/refinements explicitly transport represented coordinates
  and their dependent action fibers.

Implemented now: payoff-free classic, private-signal, and public-signal
factorization certificates; classic and signal no-absent-mindedness theorems;
and executable non-implication regressions separating public recall from both
private-signal and classic recall. The signal-to-no-absent-mindedness proof
uses the proved one-coordinate-per-action length law rather than an implicit
time convention.
