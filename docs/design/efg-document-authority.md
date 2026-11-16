# EFG documentation authority and claim inventory

This note is the navigation contract for EFG documentation. It does not
override Lean or restate volatile module tables. When two documents appear to
disagree, use this authority order:

1. Lean source for declarations and proofs.
2. [`efg-minimal-core-freeze.md`](efg-minimal-core-freeze.md) for API-growth
   policy, freeze readiness, and the active carrier regressions.
3. [`efg-governance.md`](efg-governance.md) and
   `scripts/check_efg_governance.py` for enforceable architecture and facade
   closures.
4. [`efg-module-status.md`](efg-module-status.md) for module lifecycle.
5. [`efg-public-api.md`](efg-public-api.md) for user-facing imports.
6. Focused notes for mathematical rationale and theorem boundaries.
7. Migration and history documents for dated transitions only.

## Claim inventory

| Document | Claim class | Authority |
|---|---|---|
| `docs/design.md` EFG row | project-level summary | Links to this inventory; owns no EFG detail |
| `efg-document-authority.md` | authority order, claim inventory and task routes | Authoritative documentation navigation contract |
| [`extensive_game.md`](extensive_game.md) | conceptual route, worked-example route and short architecture overview | User entry point only; Lean and the focused authorities below own details |
| [`efg-minimal-core-freeze.md`](efg-minimal-core-freeze.md) | API-growth policy, freeze readiness, candidate carrier boundary, active carrier regressions | Authoritative for freeze state |
| [`efg-governance.md`](efg-governance.md) | dependency direction, exact facade closures, placement and root policy | Authoritative with its checker |
| [`efg-module-status.md`](efg-module-status.md) | complete module census, lifecycle, responsibility and recommended facade | Authoritative lifecycle register; checker verifies source parity and totals |
| [`efg-public-api.md`](efg-public-api.md) | import choice and the semantics promised by each facade | Authoritative user import guide; closure counts are links to governance |
| [`efg-controlled-api.md`](efg-controlled-api.md) | controlled hierarchy navigation and responsibility rationale | Focused ownership guide; Lean and governance decide actual owners/edges |
| [`efg-semantic-universes.md`](efg-semantic-universes.md) | execution-regime ownership, common path-law boundary, and adapter direction | Authoritative semantic-regime contract; checker enforces import consequences and Lean proves preservation |
| [`efg-semantic-compatibility.md`](efg-semantic-compatibility.md) | two-track executable/analytic ownership, route selection, compatibility evidence, and migration terminology | Authoritative two-track representation contract; checker enforces algorithm owners, bridge direction, and source shape, while Lean proves each equality or bound |
| [`efg-preservation-matrix.md`](efg-preservation-matrix.md) | relation strengths and proved preservation coverage | Focused mathematical review ledger; Lean decides proof status |
| [`efg-mathematical-provenance.md`](efg-mathematical-provenance.md) | literature-to-Lean hypothesis translation and gaps | Focused provenance ledger |
| [`efg-infinite-kuhn-boundary.md`](efg-infinite-kuhn-boundary.md) | finite-history versus infinite-path Kuhn boundary | Focused mathematical rationale |
| [`efg-determinacy-scope.md`](efg-determinacy-scope.md) | logical, well-founded, topological and stochastic determinacy scopes | Focused mathematical rationale |
| [`efg-representation-compilation.md`](efg-representation-compilation.md) | frontend choice and compiler preservation boundary | Focused representation guide |
| [`efg-general-foundations.md`](efg-general-foundations.md) and its strategy/API continuations | long-form rationale and proposed generality | Focused design notes; not lifecycle or proof authority |
| [`efg-api-migration.md`](efg-api-migration.md) | completed path/name transitions and downstream recipes | Migration history only |
| [`efg-computability-migration.md`](efg-computability-migration.md) | ordered prompts for executable EFG operations and review of retained analytic definitions | Operational migration workflow; Lean and the checker own live status |
| [`efg-computability-search.md`](efg-computability-search.md), [strict library analysis](efg-library-computability.md), its [declaration ledger](efg-library-computability-declarations.md), the [algorithm opportunity audit](efg-algorithm-opportunity-audit.md), and the [algorithm implementation ledger](efg-algorithm-implementation-ledger.md) | implementation searches, explicit representation changes, finite and infinite algorithm opportunities, methods, owners, staged status, and bounded computability evidence | Feasibility reviews and implementation tracking; Lean source and checked equalities decide actual completion; failed compilation alone is not an impossibility theorem |
| [`efg-proof-audit.md`](efg-proof-audit.md) | proof-dependency gate, reviewed finite semantics, and mathematical namespace ownership | Focused proof-trust and semantic review; Lean determines the actual statements |
| [`efg-finite-computation-prompts.md`](efg-finite-computation-prompts.md) | ordered tasks for finite algorithms and their analytic correspondence proofs | Prospective implementation prompts; not a completion record or API-growth exception |
| [`efg-file-plan.md`](efg-file-plan.md) and its [file inventory](efg-file-plan-inventory.md) | whole-EFG file responsibilities, implemented and remaining extraction destinations, consumer migration and validation stages | Current file plan and exact source snapshot; planning labels do not change lifecycle, imports, API-growth policy or proof status |
| [`efg-minimal-core-structure-audit.md`](efg-minimal-core-structure-audit.md) | findings that motivated the current architecture | Historical audit; live state is delegated to freeze, governance and lifecycle authorities |

The constructor audit in
[`observed-game-constructors.md`](observed-game-constructors.md) and the API
reference continuation in
[`extensive_game-2-reference.md`](extensive_game-2-reference.md) are adjacent
focused notes rather than `efg-*.md` files; the same authority order applies.

## Repeated-claim routing

| Repeated claim | Single current home | Other documents should do this |
|---|---|---|
| API growth or carrier compatibility is frozen or deferred | `efg-minimal-core-freeze.md` | Link to the decision; do not infer source compatibility from “Canonical” or from the growth freeze |
| Exact facade/root closure counts | `efg-governance.md` plus checker constants | Link to the governed table; do not copy it |
| Number and lifecycle of modules | `efg-module-status.md` plus checker source-parity check | Link to the register; do not copy its status totals |
| Which import a user should choose | `efg-public-api.md` | Link to the relevant row |
| Which module owns a declaration | Lean source; module status summarizes responsibility | Link to the source/module row |
| Which execution regime owns a model and how it reaches the common path-law layer | `efg-semantic-universes.md` | Use native, adapter-backed, compiler-backed, or open; do not call separate producers one universal executor |
| How an executable result relates to a general analytic declaration | `efg-semantic-compatibility.md` | State the effective input contract and cite an exact equality, certified bound, or almost-everywhere theorem; do not call the analytic declaration legacy |
| Preservation strength | Lean theorem plus `efg-preservation-matrix.md` | Never upgrade a missing field by prose |
| Literature interpretation | `efg-mathematical-provenance.md` and focused notes | Record representation translations and gaps explicitly |
| Removed or renamed APIs | `efg-api-migration.md` or `docs/HISTORY.md` | Do not present dated transitions as current architecture |

## Task routes

- New reader: follow the conceptual route, then the finite imperfect-information
  worked example in [`extensive_game.md`](extensive_game.md).
- User choosing an import: read [`efg-public-api.md`](efg-public-api.md) after
  selecting the required semantic branch.
- Contributor locating ownership: consult
  [`efg-module-status.md`](efg-module-status.md), then the defining Lean
  module; for the controlled family also use
  [`efg-controlled-api.md`](efg-controlled-api.md).
- Reviewer checking mathematics: start with
  [`efg-mathematical-provenance.md`](efg-mathematical-provenance.md) and
  [`efg-semantic-universes.md`](efg-semantic-universes.md), then use
  [`efg-preservation-matrix.md`](efg-preservation-matrix.md) and inspect the
  cited Lean declarations.
- Maintainer changing a facade or lifecycle state: read
  [`efg-minimal-core-freeze.md`](efg-minimal-core-freeze.md),
  [`efg-governance.md`](efg-governance.md), and
  [`efg-module-status.md`](efg-module-status.md), then run the governance and
  full module checks.
- Maintainer reviewing computability: follow the completed workflow and live
  boundary in [`efg-computability-migration.md`](efg-computability-migration.md).
  Apply the ownership and evidence rules in
  [`efg-semantic-compatibility.md`](efg-semantic-compatibility.md).
  For the retained library declarations, consult the
  [strict feasibility analysis](efg-library-computability.md) and its
  [per-declaration ledger](efg-library-computability-declarations.md), then use
  the [algorithm opportunity audit](efg-algorithm-opportunity-audit.md) to
  distinguish finite algorithms, infinite online representations, certified
  approximation, and mathematical obstructions. Track methods and staged
  implementation in the
  [algorithm implementation ledger](efg-algorithm-implementation-ledger.md).
  Keep finite operations executable and retain individually justified analytic
  definitions in the full audit. Classification supplements the identity
  ratchet; a reduction does not authorize an automatic baseline update.
- Researcher selecting an open generality task: use the focused boundary notes,
  [`efg-mathematical-provenance.md`](efg-mathematical-provenance.md), and the
  staged nodes under `docs/knowledge/staged/extensive_game/`. A staged target is
  not a formal theorem until the cited Lean declaration exists.
