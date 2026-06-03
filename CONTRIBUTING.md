# Contributing To EconCSLib

Contributions are welcome. EconCSLib is an initial public release with limited
coverage, so focused improvements to definitions, proofs, documentation, and
blueprint nodes are all useful.

## Before Starting

- Read [`README.md`](README.md) and [`docs/design.md`](docs/design.md).
- Browse existing [issues](https://github.com/gametheoryinlean/EconCSLib/issues)
  before filing or implementing a task.
- Use [Discussions](https://github.com/gametheoryinlean/EconCSLib/discussions)
  for broad mathematical or architectural proposals.
- For knowledge-base work, read
  [`docs/maintainers/knowledge-blueprint.md`](docs/maintainers/knowledge-blueprint.md).

## Development

Keep changes focused and follow nearby Lean style. Add public stable modules to
`EconCSLib.lean`; keep examples and experimental open-problem interfaces opt-in.
Do not add textbook PDFs, scans, OCR output, generated documentation sites, or
ordinary Lean placeholders. Open-problem theorems may use the scoped
`answer(sorry) ↔ P := by sorry` pattern under `EconCSLib/OpenProblem/`.

Run the relevant checks before opening a pull request:

```bash
lake exe cache get
lake build
lake build EconCSLib.Examples
python3 scripts/check_lean_placeholders.py EconCSLib
git diff --check
```

For blueprint changes, also run:

```bash
python3 -m unittest tests/test_check_knowledge_references.py
python3 scripts/check_knowledge_references.py docs/knowledge
mdblueprint-check docs/knowledge --lean-root .
```

The placeholder checker must pass.

## Pull Requests

Explain the mathematical intent, identify the modules or blueprint nodes
affected, and report the checks you ran. Keep unrelated refactors separate.

## Licensing

By submitting a contribution, you agree that it is licensed under the
repository's [Apache License 2.0](LICENSE).

## Conduct

Participation is governed by the [Code of Conduct](CODE_OF_CONDUCT.md).
