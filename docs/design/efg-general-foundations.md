# General EFG Foundations

Status: target architecture with Phase A, the foundational part of Phase B,
and finite logical determinacy implemented through 2026-08-12.
`Execution.CompletePlay`, `Execution.Length`, `Execution.Objective`, and
`Interface.Objective` implement the measure-free play, structural termination,
and objective layers. `ControlledGame`, `ControlledDecisionGame`, and its
optional `ControlledObservedGame` extension carry payoff-free controlled
dynamics, decision information, and observations; `ExtensiveGame` is the
compatible state-payoff extension. `Observed.WellFormed`, `FiniteUnfolding`,
`Winning.Basic`, `Winning.Topology`, `Observed.Quasi`, and `Observed.General`
implement the finite-profile, finite occurrence unfolding, winning,
quasistrategy, and discrete-general carrier foundations. Finite and
structurally well-founded no-chance perfect-information two-player zero-sum
determinacy are proved; arbitrary infinite Gale--Stewart determinacy and
analytic general-strategy theorems remain targets. Discrete
infinite almost-sure winning is implemented separately from pathwise
robustness and requires a probability-measure certificate. The canonical
payoff-free complete-information constructor uses decision histories only;
full-history information remains a named compatibility constructor. On the
intentionally unconstrained base carrier, constructive `IsDecision` evidence
and `RepresentedInfo` keep player-labeled terminals and unused raw information
outside the strategy domain. `DecisionMoverCoherent` is only an optional
normalization certificate. Lean source is authoritative.

This document continues in
[`efg-general-foundations-2-strategy.md`](efg-general-foundations-2-strategy.md).

## 1. Decision

The canonical semantic lines are:

```text
Arena -> ControlledGame -> ControlledDecisionGame -> ControlledObservedGame
                       \-> objectives / winning conditions
                       \-> discrete or analytic execution

ControlledGame -> ExtensiveGame -> ObservedGame -> ObservedChanceGame
                     state-payoff compatibility
```

It is already more general than a finite textbook tree: states and actions may
be infinite, action types may depend on the current state, distinct histories
may reach the same state, information and chance may depend on the complete
history, and execution may be finite, countably infinite, or analytic.

The extension must therefore be additive. It introduces four orthogonal
families rather than a replacement EFG record:

```text
                                information / recall
                                         |
Arena + typed histories -> complete plays + objectives -> solution concepts
            |                            |
            +-- length certificates      +-- execution semantics
```

The base structures must not acquire `Fintype`, decidable equality,
well-foundedness, topology, measurability, a real-valued payoff requirement,
or determinacy assumptions.

## 2. Requirements from the literature

| Source | Requirement for this design |
|---|---|
| Maschler, Solan, and Zamir | Represent finite trees, player and chance nodes, information sets with one common abstract action menu, terminal outcomes, subgames, and perfect recall. |
| Laraki, Renault, and Sorin | Keep pure, mixed, behavioral, and general strategies distinct; state realization results rather than false strategy-space isomorphisms; support subgames and SPE. |
| SEP, "Logic and Games" | Support two-player win/lose games, finite and infinite plays, winning strategies, quasistrategies, totality, determinacy, finite length, well-founded play, and imperfect information. |

These requirements do not define one structure. In particular:

- a finite payoff EFG and an infinite logical game share dynamics and
  information, but not their objective semantics;
- a total game need not be determined;
- an imperfect-information game can be undetermined even when its length is
  two;
- a mixed strategy is a law on pure contingent plans, whereas a general
  strategy is a law on behavioral strategies;
- pathwise robustness may be strictly stronger than winning against
  information-consistent opponent profiles;
- a quasistrategy is a nonempty set of allowed actions, not a probability law.

## 3. Canonical factorization

The target stack has seven layers.

| Layer | Canonical responsibility | Assumptions excluded from the layer |
|---|---|---|
| Dynamics | `Arena`, states, dependent legal actions, transition | players, probability, finiteness |
| Occurrences | typed finite histories and complete legal plays | information, utility |
| Presentation | mover, observations, information states/actions, public information | root selection, termination, recall, equilibrium |
| Objective | terminal outcome, path outcome/utility, or winning condition | strategy, probability |
| Strategy | pure, behavioral, mixed, general, or quasi strategy | equilibrium |
| Execution | deterministic evaluation, PMF laws, or measurable path laws | preference comparisons |
| Solution | Nash, SPE, winning strategy, determinacy, sequential concepts | representation-specific syntax |

`GameForm`, `LawGameForm`, and `ContinuationGameForm` remain the
representation-neutral targets once an EFG has been evaluated. EFG-specific
notions such as information consistency and lawful subgames must be certified
before forgetting histories.

Continuation-root visibility is external data:
`ContinuationRootPresentation` selects analysis roots without changing the
identity of an observed game. `SubgameSystem` separately selects lawful roots,
and standard SPE consumes a `CompleteSubgameSystem`; an arbitrary visible-root
presentation is never promoted to standard subgames.

## 4. Dynamics and occurrences

### 4.1 Arena semantics

The existing conventions remain:

- `Action s` is the complete legal action type at `s`;
- `IsTerminal s` means `IsEmpty (Action s)`;
- `next s a` is total because `a` already proves legality;
- `mover s = none` denotes nature only when `s` is nonterminal;
- the mover and base payoff at a terminal state are semantically ignored.

Requiring `mover s = none` at terminal states would be a normalization
convention, not a mathematical well-formedness condition. A frontend may
normalize it, but the canonical carrier must not require it.

### 4.2 Histories, not endpoints

All information, objectives, and compilers use complete dependent histories.
An endpoint state is insufficient because:

- two action occurrences may merge into one state;
- observations and chance laws may be history-dependent;
- a terminal outcome may depend on the route taken;
- an infinite objective may inspect the action trace.

Endpoint-only semantics remain valid specialist frontends, never canonical
isomorphisms unless endpoint projection is proved injective on the relevant
fragment.

### 4.3 Complete legal play

`Arena.CompletePlayFromHistory current` is the implemented measure-free path
type, where
`current : HistoryFrom start`. Mathematically it is a sequence

```text
p : Nat -> HistoryFrom start
```

such that:

1. `p 0 = current`;
2. at a nonterminal coordinate, `p (n + 1)` is exactly one legal `snoc`
   extension of `p n`;
3. at a terminal coordinate, `p (n + 1) = p n`.

`CompletePlayFrom start` is the root abbreviation obtained by taking
`current` to be the empty history.

Thus every finite play has a unique terminal-absorbing infinite presentation,
while a genuinely infinite play never reaches a terminal history. The type is
purely structural: no countability, measurable space, policy, or probability
law is required.

The discrete infinite-history executor is proved almost surely supported on
this legality predicate. The analytic adapter into the same maximum path-law
carrier accepts the corresponding legality theorem explicitly, because a
general stochastic-state kernel need not be deterministic `Arena.next`.
Neither executor is reimplemented inside the objective layer.

When restricting a root path objective after an accumulated history,
`CompletePlayFromHistory.resume` replays the original prefix and preserves the
root clock. `splice` has a different role: it rebases an objective already
defined on absolute tails and starts its clock at the current history. The
API names these operations `PathOutcome.afterHistory` and
`PathOutcomeFromHistory.rebaseTailAt` so the distinction is visible.

## 5. Length and termination certificates

Four notions must remain distinct.

### 5.1 Structural finite length

`HasLengthBoundAt current B` says every legal continuation exactly `B` steps
from the current absolute history is terminal. `HasLengthBoundFrom A start B`
is its empty-history specialization. It implies there is no longer legal
continuation. The bound is uniform over every player choice and every nature
action.

This is the correct hypothesis for primitive recursion, finite enumeration,
backward induction, and executable solvers. It is stronger than almost-sure
termination.

### 5.2 Structural well-foundedness

Let `Child k h` mean that `k` is a one-action extension of `h`.
`IsWellFoundedAt current` is an `Acc Child` certificate at the current
absolute history; `IsWellFoundedFrom A start` specializes it to the empty
history.

This is constructive proof data for recursion and allows arbitrary branching
and no uniform natural-number height. It implies that every complete legal
play eventually reaches a terminal history.

The converse from "there is no infinite branch" to `Acc Child` is
choice-sensitive constructively and must not be exposed as an unconditional
definitional equivalence.

### 5.3 Objective finite decision

A logical winning condition may already decide a winner at a finite prefix
even if the arena continues. Therefore define separately:

- `DecidesAt W i h`: every complete play extending `h` is won by `i`;
- `IsDecidedBy W B`: every play reaches some `DecidesAt` prefix by `B`;
- `IsPrefixWellFounded W`: every play reaches some `DecidesAt` prefix.

These are objective properties. They coincide with structural termination
only for the explicit embedding in which terminal histories decide the
winner.

For recursion, also define an `Acc` certificate on the relation between
undecided histories. Semantic eventual prefix decision and this constructive
certificate are not definitionally identified.

### 5.4 Probabilistic termination

`AETerminates` remains a property of one generated path law, hence of a game,
profile, root, and chance model. It does not imply structural
well-foundedness: zero-probability nonterminating branches may remain.

The implication ladder to prove is:

```text
uniform structural bound
        -> structural well-foundedness
        -> termination of every legal play
        -> a.s. termination under every supported path law
```

No reverse implication is valid without additional hypotheses.

## 6. Outcome and objective layer

The existing `ExtensiveGame.payoff : State -> N -> U` remains a convenient
state-based terminal-payoff embedding. General semantics must additionally
support the following history-sensitive objectives.

### 6.1 Terminal outcomes

For an arena rooted at `start`, define:

```text
TerminalHistory := {h : HistoryFrom start // IsTerminal h.1}
TerminalOutcome O := TerminalHistory -> O
```

Keeping `O` separate from utility permits one game form to be interpreted by
different preferences. The current base payoff embeds by taking
`O = N -> U` and reading the endpoint state.

### 6.2 Complete-path outcomes

Define a general deterministic path objective

```text
PathOutcome O := CompletePlayFrom start -> O
```

and utility interpretations `O -> N -> V`. Discounted reward, limsup payoff,
mean payoff, parity conditions, and terminal outcomes all become
specializations.

Measurability, integrability, boundedness, discounting, and order assumptions
belong to the evaluator or theorem consuming the objective. They do not belong
to `PathOutcome`.

### 6.3 Winning conditions

The most general measure-free winning condition is:

```text
WinningCondition N := N -> Set (CompletePlayFrom start)
```

Store only the winning sets. Define external predicates:

- `IsExclusive`: no complete play is won by two distinct players;
- `IsTotal`: every complete play is won by at least one player;
- `IsTwoPlayerZeroSum`: exactly one of the two players wins every play.

`DecidesAt W i h` is defined by containment of the cylinder generated by `h`
in `W i`. An optional `PrefixDecision` certificate records an explicit set of
finite winning histories and proves soundness, persistence under extension,
and any completeness needed by a theorem. This captures the SEP presentation
without restricting arbitrary infinite objectives to prefix-determined ones.

Terminal win/lose games embed into winning conditions through terminal
absorption. Conversely, a two-player winning condition embeds into utilities
`1/0` only for payoff comparison; the winning-condition API remains primary
for determinacy proofs.

### 6.4 Continuation restriction

Restricting a path objective at a history must splice the absolute prefix onto
the future play. It must use the existing absolute-prefix continuation
semantics, not fresh-clock restart. This matters for accumulated rewards,
time-dependent objectives, and winning sets that inspect the earlier path.
