# EconCSLib AI Agent Guide

EconCSLib is a Lean 4 library and knowledge base for computational economics,
built on Mathlib. This file is supplemental guidance for coding agents. Use
repository-relative paths throughout.

## Fast Start

1. Inspect the worktree:

   ```bash
   git status --short --branch
   ```

2. Read [`README.md`](README.md) and [`docs/design.md`](docs/design.md). For a
   focused task, inspect the target file, imports, and neighboring modules.

3. For Lean changes, fetch the Mathlib cache if needed and build:

   ```bash
   lake exe cache get
   lake build
   lake build EconCSLib.Examples
   ```

4. For knowledge-base changes, read
   [`docs/maintainers/knowledge-blueprint.md`](docs/maintainers/knowledge-blueprint.md)
   and the nearest `topics.md` catalog under `docs/knowledge/`.

Do not discard existing worktree changes. Do not recreate the old root
`blueprint/` directory: generated blueprint output is not committed here.

## Repository Map

### Lean source

- `EconCSLib.lean`: stable aggregate import.
- `EconCSLib/Foundation/`: shared vocabulary and helpers.
- `EconCSLib/Math/`: reusable mathematics with no EconCS domain dependency.
- `EconCSLib/GameTheory/`: strategic, extensive, and coalitional games.
- `EconCSLib/SocialChoice/`: social choice, voting, and fair division.
- `EconCSLib/MarketDesign/Matching/`: matching markets and Gale-Shapley.
- `EconCSLib/MechanismDesign/Auction/`: mechanisms and auctions.
- `EconCSLib/Examples/`: opt-in worked examples and regression targets.
- `EconCSLib/OpenProblem/`: opt-in experimental open-problem interfaces.

Examples and open-problem interfaces must not be imported by `EconCSLib.lean`.

### Documentation and tooling

- `docs/design.md`: project-level architecture and contribution guide.
- `docs/design/`: focused API notes.
- `docs/research/`: curated mathematical rationale and proof-route notes.
- `docs/maintainers/`: reproducible publishing workflows.
- `docs/knowledge/`: editable source for the generated knowledge blueprint.
- `docs/knowledge/mdblueprint.yml`: blueprint configuration, topic registry,
  source registry, Lean repository mapping, and KaTeX macros.
- `docs/knowledge/nodes/`: older accepted-style knowledge nodes retained for
  compatibility.
- `docs/knowledge/staged/`: reviewable mathematical content awaiting promotion.
- `scripts/check_knowledge_references.py`: rejects provenance material in
  scholarly `## References` sections.
- `scripts/publish_blueprint.py`: manual blueprint build-and-publish wrapper.
- `scripts/build_api_docs.py`: local API-documentation wrapper.
- `docbuild/`: nested Lake project for API-reference generation.

Do not commit textbook PDFs, scans, OCR-derived content, or generated sites.

## Lean Architecture

The dependency direction is:

```text
Foundation/   Math/
      \       /
       domain modules
            |
         Examples/
```

- Keep structures lean: add finiteness, decidability, order, topology, and
  algebraic assumptions where they are needed.
- Keep `Math/` independent of EconCS domain modules.
- Search Mathlib before introducing custom abstractions.
- Prefer targeted imports over `import Mathlib` where the replacement is clear.
- Follow nearby source files and Mathlib naming conventions.
- Register intended stable modules in `EconCSLib.lean`.

## Source Documentation

Every Lean module should have an accurate module docstring describing its
purpose, main declarations, notable design choices, and sources where
appropriate. Add concise declaration docstrings for exported definitions,
structures, instances, and substantive theorems. Routine proof helpers only
need comments when their role is not clear from the code.

Use explicit reference labels such as `[MSZ 2.18]`, `[AGT Ch.1]`, or
`[MFoGT Thm 2.3.1]`. Prefer literature-standard variable names when they
improve readability.

## Placeholder Policy

Lean source under `EconCSLib/` must not contain ordinary `sorry` or `admit`.
Open-problem theorems under `EconCSLib/OpenProblem/` may use only the scoped
`answer(sorry) ↔ P := by sorry` pattern.

When a mathematical target is not ready for implementation:

- record it as a knowledge-blueprint node or GitHub issue;
- link Lean modules and declarations only when they exist;
- mark blueprint proof verification as a gap;
- do not add a deferred Lean theorem declaration merely to reserve an API.

## Knowledge Blueprint

The knowledge blueprint is generated from Markdown under `docs/knowledge/`.

### Authoring workflow

- `docs/knowledge/nodes/` contains older accepted-style nodes retained for
  compatibility.
- `docs/knowledge/staged/` contains public, reviewable mathematical nodes that
  have not yet been promoted.
- New extraction work normally goes under `staged/`.

The distinction is workflow metadata, not a public-versus-private boundary.

### Node authoring

- Use one mathematical concept per file.
- Follow sibling files and the nearest `topics.md` catalog.
- Use stable `id`, `title`, `kind`, `status`, `verification`, and topic
  metadata.
- Use `uses` only for real mathematical dependencies.
- Link Lean declarations only when they exist.
- For `kind: proof-plan`, use `target` and `plan_status`; do not duplicate the
  target in `uses`.
- Include a visible `## References` section for source-backed nodes.
- Put PRs, issues, commits, and migration notes under `## Provenance` or
  `## Implementation Notes`, not `## References`.
- Register recurring sources in `docs/knowledge/mdblueprint.yml` with lawful
  external links. Do not add local redistributed source files.

## Verification

Run checks from the repository root and scale them to the files changed.

### Lean changes

```bash
lake build
lake build EconCSLib.Examples
python3 scripts/check_lean_placeholders.py EconCSLib
```

The placeholder checker must pass.

### Knowledge-base changes

```bash
python3 -m unittest tests/test_check_knowledge_references.py
python3 scripts/check_knowledge_references.py docs/knowledge
mdblueprint-check docs/knowledge --lean-root .
```

To preview generated output:

```bash
mdblueprint-publish docs/knowledge /tmp/EconCSLib-main-mdblueprint-site
```

### API-documentation changes

When changing `docbuild/`, `.github/workflows/docs.yml`, or API-doc tooling,
read [`docs/maintainers/api-docs.md`](docs/maintainers/api-docs.md) and run:

```bash
python3 scripts/build_api_docs.py
```

### All changes

```bash
git diff --check
```

## CI Workflows

- `.github/workflows/build.yml`: builds the stable library and examples,
  rejects disallowed Lean placeholders, and checks diff whitespace.
- `.github/workflows/blueprint.yml`: validates the blueprint on pull requests
  and deploys the generated site only from `main`.
- `.github/workflows/docs.yml`: builds and deploys API reference output from
  `main`.

## Working Safely

- Inspect `git status --short --branch` before editing and before handoff.
- Preserve user changes and unrelated modifications.
- Do not use destructive Git commands unless the task explicitly requires
  them.
- Inspect imports and sibling files before changing an API.
- Do not claim a blueprint proof gap is formally proved merely because its
  natural-language statement is present.

## Further Reading

- [`README.md`](README.md)
- [`docs/design.md`](docs/design.md)
- [`docs/design/README.md`](docs/design/README.md)
- [`docs/maintainers/knowledge-blueprint.md`](docs/maintainers/knowledge-blueprint.md)
- [`docs/maintainers/api-docs.md`](docs/maintainers/api-docs.md)
- [`docs/maintainers/initial-public-release.md`](docs/maintainers/initial-public-release.md)
- [`docs/HISTORY.md`](docs/HISTORY.md)
