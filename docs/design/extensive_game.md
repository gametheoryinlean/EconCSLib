# Extensive Games — Reading Guide and Architecture

This is the short entry point for EconCSLib's extensive-game framework. It
explains how the main concepts fit together and gives a concrete route into the
existing examples. It is not an API inventory. Use
[`efg-public-api.md`](efg-public-api.md) to choose imports and
[`efg-document-authority.md`](efg-document-authority.md) to locate the
authoritative policy or theorem-boundary document.

EconCSLib supports two complementary representations:

- finite inductive trees for structural recursion, backward induction, and
  executable finite examples;
- history-indexed controlled games for imperfect information, chance,
  behavioral and mixed strategies, continuation semantics, and representation
  transfer.

The first representation is the shortest route for a finite perfect-information
game. The second is the canonical semantic route when information, observations,
or stochastic execution matter.

## 1. Conceptual route

Read the canonical history-indexed design in this order:

```text
Arena
  pure states, dependent legal actions, and transitions
    ↓
ControlledGame
  initial state and player/non-player control
    ↓
ControlledDecisionGame
  decision information, represented coordinates, and information actions
    ├── pure/behavioral/mixed strategies
    ├── perfect recall and Kuhn realization
    └── lawful subgames and continuation systems
    ↓ optional
ControlledObservedGame
  private observations, public observations, and their projections

Orthogonal semantic layers attach only when needed:
  chance law ─ termination/objective ─ execution law ─ equilibrium
```

Each step answers one modeling question:

| Layer | Question answered | Deliberately absent |
|---|---|---|
| `Arena` | How can play move? | players, chance, payoff, information |
| `ControlledGame` | Who controls a state? | a probability law for non-player states |
| `ControlledDecisionGame` | What does a moving player know and what can they choose? | private/public signal histories, objectives |
| `ControlledObservedGame` | What does each player currently observe, and what is public? | recall, finiteness, termination, equilibrium |
| semantic certificates | Under which law, objective, horizon, and recall assumptions is a theorem stated? | hidden strengthening of the carrier |

This order is a mental model, not a requirement to construct every record by
hand. In particular, strategy coordinates come from represented decision
information, not from the optional observation layer.

### State and occurrence convention

`Arena` is a compact transition system: mover, available actions, and the next
state are state-indexed. Complete typed histories are occurrence-sensitive, so
two distinct paths remain distinct even when they reach the same compact state.
If control or legal actions genuinely depend on the path rather than the compact
state, put the required memory into the state or use an occurrence-based
frontend/compiler. Do not infer node equality from endpoint equality.

### Chance convention

`ControlledGame.mover s = none` means only that no strategic player controls
`s`. It does not define a chance distribution. A stochastic presentation must
supply its chance law explicitly. This keeps deterministic structure, discrete
PMF execution, and analytic kernels from being conflated.

## 2. Getting-started route

Start from a concrete finite representation, then inspect the canonical layers
only as the example needs them.

### Finite perfect information

Use the inductive `GameTree` track when the game is structurally finite, has
perfect information, and has no chance node in the source syntax.

```text
GameTree
  → backward-induction value and policy
  → occurrence-sensitive observed compiler
  → pure Nash and standard pure SPE
```

The canonical compiler is
[`GameTreeOccurrenceObserved.lean`](../../EconCSLib/GameTheory/ExtensiveGame/Compiler/GameTreeOccurrenceObserved.lean).
Its occurrence presentation is preferred when equal subtree values could make
an endpoint compiler identify distinct nodes. Detailed finite-tree signatures
remain in [`extensive_game-2-reference.md`](extensive_game-2-reference.md).

### Finite imperfect information

Read
[`FiniteImperfectCompilation.lean`](../../EconCSLib/Examples/ExtensiveGame/FiniteImperfectCompilation.lean)
as the first worked example. It shows:

1. compact finite game data;
2. a nontrivial information set shared by two decision states;
3. local compiler well-formedness obligations;
4. compilation to the canonical observed EFG;
5. occurrence-sensitive information and perfect-recall checks.

This route lets a new user see a complete model before learning every low-level
carrier field.

### Finite recall and mixed/behavioral realization

After the compilation example, read
[`RootScopedKuhn.lean`](../../EconCSLib/Examples/ExtensiveGame/RootScopedKuhn.lean).
It demonstrates perfect recall, mixed and behavioral profiles, bounded law
realization, deviation coverage, and why the construction is scoped to a
selected continuation root.

### Representation edge cases

Use these examples only after the main route:

- [`FiniteEFGWellFormedness.lean`](../../EconCSLib/Examples/ExtensiveGame/FiniteEFGWellFormedness.lean)
  shows why ghost information values and terminal mover labels create no strategy coordinates.
- [`OccurrenceNonIso.lean`](../../EconCSLib/Examples/ExtensiveGame/OccurrenceNonIso.lean)
  distinguishes endpoint equality from occurrence equality.
- [`RecallHierarchy.lean`](../../EconCSLib/Examples/ExtensiveGame/RecallHierarchy.lean)
  separates classical, private-signal, and public-signal recall.

## 3. Choosing the semantic branch

After the common structural and decision layers, choose only the semantics the
theorem needs:

| Need | Start here |
|---|---|
| structure, represented strategies, recall, lawful subgames | `Interface.StructuralCore` or `Interface.Core` |
| bounded deterministic or PMF execution | `Interface.Execution.Finite` |
| infinite paths generated by discrete PMF policies | `Interface.Execution.Infinite` |
| measurable or non-atomic kernels | `Interface.Execution.Analytic` |
| discrete Kuhn and equilibrium results | `Interface.Equilibrium.Discrete` |
| measurable continuation equilibrium | `Interface.Equilibrium.Analytic` |
| finite frontends and compilers | `Interface.Compilation.Discrete` |

This table is a reading aid. The governed import contract and the exact
responsibility of every facade are in
[`efg-public-api.md`](efg-public-api.md). The structural, finite-PMF,
infinite-discrete, analytic, and FOSG execution regimes and their allowed
adapter directions are separated in
[`efg-semantic-universes.md`](efg-semantic-universes.md).

## 4. Mathematical boundaries

- `GameTree` backward induction and the occurrence compiler supply the finite
  perfect-information route to pure SPE.
- Observed-EFG Kuhn results compare induced laws under finite perfect recall;
  mixed and behavioral strategy types are not claimed to be isomorphic.
- Standard SPE quantifies over a complete lawful subgame system. Predicates on
  caller-selected roots are conservative variants and are not silently called
  standard SPE.
- Sequential equilibrium and arbitrary-measure pure-strategy realization are
  outside this release; their prototype interfaces are not included.
- Countably supported infinite-prefix realization and arbitrary-measure
  strategy laws have explicit boundaries; finite marginal equality is not
  promoted to an infinite path-law theorem without the missing bridge.

For exact hypotheses and remaining gaps, use
[`efg-mathematical-provenance.md`](efg-mathematical-provenance.md),
[`efg-preservation-matrix.md`](efg-preservation-matrix.md), and the focused
Kuhn and determinacy scope notes.

## 5. Documentation map

| Task | Document |
|---|---|
| understand the conceptual layers or follow a first example | this guide |
| choose a supported import | [`efg-public-api.md`](efg-public-api.md) |
| locate declaration ownership | [`efg-module-status.md`](efg-module-status.md) |
| understand the controlled hierarchy | [`efg-controlled-api.md`](efg-controlled-api.md) |
| review API-growth and dependency policy | [`efg-minimal-core-freeze.md`](efg-minimal-core-freeze.md), [`efg-governance.md`](efg-governance.md) |
| compare frontend representations and compilers | [`efg-representation-compilation.md`](efg-representation-compilation.md) |
| check preservation strength | [`efg-preservation-matrix.md`](efg-preservation-matrix.md) |
| check literature translation or theorem gaps | [`efg-mathematical-provenance.md`](efg-mathematical-provenance.md) |
| migrate an old path or declaration | [`efg-api-migration.md`](efg-api-migration.md) |

API growth is frozen. Improve discoverability through this guide, module
docstrings, existing examples, and links to the current owners—not by adding a
new facade, wrapper, alias, or duplicate theorem.
