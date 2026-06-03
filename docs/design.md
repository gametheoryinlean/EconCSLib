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
| `Math/` | fixed-point theorems, simplex helpers, linear algebra, linear programming, and minimax |
| `GameTheory/StrategicGame/` | strategic games, equilibrium, dominance, checkers, mixed strategies, ESS, IESDS, correlated-equilibrium foundations, potential games, and zero-sum games |
| `GameTheory/ExtensiveGame/` | Arena-based games, strategies, plays, subgames, finite trees, backward induction, SPE, normal-form reduction, imperfect information, and stochastic trees |
| `GameTheory/CoalitionalGame/` | transferable-utility games, the core, and Shapley-value infrastructure |
| `SocialChoice/` | social-choice vocabulary, voting theory, and fair division |
| `MarketDesign/Matching/` | matching markets and Gale-Shapley developments |
| `MechanismDesign/Auction/` | mechanism-design and auction infrastructure |
| `Examples/` | opt-in examples and executable regression targets |
| `OpenProblem/` | opt-in experimental open-problem interfaces |

## Design Choices

### Profiles are game-bound

For strategic games, a profile belongs to a specific game: `G.Profile`.
Foundation-level profile vocabulary exists only where it provides reusable
compatibility helpers.

### Extensive games use arenas

The extensive-form layer uses an arena and state-space model so infinite-state
and infinite-horizon games remain representable. Separate finite-tree modules
support backward induction and executable examples.

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
