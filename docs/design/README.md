# EconCSLib Design Documentation

This is the entry point for EconCSLib's design documentation. It frames the
**overall design** and links out to the **per-module design notes**.

Two reading levels:

- **Overall design** — project-wide architecture, layering rules, and
  contribution guidelines. One authoritative document:
  [`../design.md`](../design.md). Read this first.
- **Per-module design notes** — how each module's Lean API is actually built:
  what the data structures are, where each typeclass assumption enters, and why
  the module is layered the way it is. Each module is a flat group of files in
  this directory: a `<module>.md` index plus numbered `<module>-NN-*.md` topic
  files (below).

The split mirrors the difference between *rules* and *worked application of the
rules*. `../design.md` states the principles once; each module's notes show
those principles in action on that module's concrete types.

## Overall architecture at a glance

```
Foundation/   — shared vocabulary (players, profiles, preferences, utility, CostM)
Math/         — reusable mathematics (fixed-point, LP duality, minimax, simplex)
   ▲
   │  applications import Foundation + Math; the reverse is forbidden
   │
GameTheory/, SocialChoice/, MarketDesign/, MechanismDesign/  — domain modules
```

Three cross-cutting principles recur in every module's notes (full statements
in [`../design.md`](../design.md) §2, §4):

1. **Bourbaki discipline** — structures hold data, zero typeclass constraints;
   `[Fintype]`/`[DecidableEq]`/order/algebra are attached at the theorem or
   definition that needs them.
2. **Two-layer `Prop` / `Bool`** — every decidable `IsX : Prop` gets a
   computable mirror `isX : Bool` plus a soundness bridge `isX_iff`.
3. **Minimal assumptions, then step up** — definitions sit at the weakest
   hypotheses; only the theorems that need arithmetic move to an ordered field.

Each per-module note set carries a "minimal assumptions" column so you can see
exactly where every constraint enters.

## Per-module design notes

| Module | Source | Design notes | Status |
|--------|--------|-------------|--------|
| Strategic games | `GameTheory/StrategicGame/` | [`strategic_game.md`](strategic_game.md) | Available |
| Extensive games | `GameTheory/ExtensiveGame/` | [`efg-document-authority.md`](efg-document-authority.md), [`extensive_game.md`](extensive_game.md) | Available |
| Coalitional games | `GameTheory/CoalitionalGame/` | — | Planned |
| Social choice (voting, fair division) | `SocialChoice/` | — | Planned |
| Matching | `MarketDesign/Matching/` | — | Planned |
| Mechanism design (auctions) | `MechanismDesign/` | — | Planned |
| Foundation vocabulary | `Foundation/` | — | Planned |
| Reusable mathematics | `Math/` | — | Planned |

The remaining rows show where additional focused notes can be added as APIs
stabilize.

For EFG work, start with the conceptual route and finite worked-example route
in [`extensive_game.md`](extensive_game.md). Use the
[`authority and claim inventory`](efg-document-authority.md) only when locating
the owner of an import, policy, preservation claim, or research boundary. In
particular, `Interface.StructuralCore` is the exact narrow structural import,
`Interface.Core` is the broader Foundation Facade, API growth is frozen, and
their compatibility freeze is currently deferred.

For the whole-EFG computation migration, see the
[file plan](efg-file-plan.md) and [complete file inventory](efg-file-plan-inventory.md).
They distinguish implemented landing modules from remaining extraction or
consumer-migration work and retain the existing architecture, lifecycle and
proof authorities.
For the retained main-library noncomputable declarations, the
[strict feasibility analysis](efg-library-computability.md) and
[58-item ledger](efg-library-computability-declarations.md) distinguish exact
signature replacements, effective representations, and numerical evaluation.
The [algorithm opportunity audit](efg-algorithm-opportunity-audit.md) marks
existing and missing finite algorithms, computable infinite observables,
certified approximations, semidecision procedures, and mathematical
obstructions. The
[algorithm implementation ledger](efg-algorithm-implementation-ledger.md)
records each method, effective input contract, owner, correctness target, and
implementation stage.
The [two-track representation contract](efg-semantic-compatibility.md) governs
how executable definitions relate to those analytic semantics. Analytic
definitions are not described as legacy merely because an effective subdomain
has an algorithm.

## What a module note set should contain

Follow the strategic-game set as the template:

- One main file `<module>.md` that *is* the design notes, not a thin index: the
  overview, the design principles as they apply to *this* module, a module map,
  and as much of the API walkthrough as fits. Keep a file under ~300 lines.
- Split into numbered continuation files (`<module>-2-*.md`, `<module>-3-*.md`,
  flat in this directory) **only** when the main file would overflow that
  budget; each continuation covers a coherent run of sections and links back to
  the main file. Don't pre-split a module that fits in one file.
- Sections numbered `§1, §2, …` continuously across the files so cross-references
  read the same regardless of which file a section landed in.
- Tables with columns **name / minimal assumptions / meaning**, plus prose
  explaining *why* each assumption exists.
- Signatures abbreviated for readability; the source file stays authoritative.

## Conventions

- Reference labels follow the repo: `[MSZ X.Y]` = Maschler/Solan/Zamir,
  *Game Theory* (Cambridge, 2013); `[AGT Ch.Z]` = Nisan/Roughgarden/Tardos/
  Vazirani.
- These notes are the *API* layer. The *textbook* layer (per-concept math + Lean
  nodes) lives in [`docs/knowledge/`](../knowledge). Dated decisions live in
  [`../research/design_decisions.md`](../research/design_decisions.md).
