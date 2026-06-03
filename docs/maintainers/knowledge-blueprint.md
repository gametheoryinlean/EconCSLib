# Knowledge Blueprint

EconCSLib includes a natural-language knowledge blueprint cross-linked to Lean
source.

- **Live site:** <https://gametheoryinlean.github.io/blueprint/>
- **Editable source:** [`docs/knowledge/`](../knowledge)
- **Generator:** [`gametheoryinlean/mdblueprint`](https://github.com/gametheoryinlean/mdblueprint)
- **Generated output repository:** `gametheoryinlean/blueprint`

Generated HTML is not committed to EconCSLib.

## Public Authoring Workflow

The knowledge source deliberately has two authoring areas:

- `docs/knowledge/nodes/` contains older accepted-style nodes retained for
  compatibility.
- `docs/knowledge/staged/` contains public, reviewable mathematical nodes
  awaiting promotion.

New extraction work normally goes under `staged/`. Staged nodes are not private
drafts: they are part of the visible mathematical roadmap.

Use `docs/knowledge/mdblueprint.yml` and the nearest `topics.md` catalog as the
authoritative topic registry. Keep one mathematical concept per file. Link Lean
modules and declarations only when they exist. Record unimplemented theorem
targets as proof gaps without creating placeholder Lean declarations.

## References

Source-backed nodes include a visible `## References` section with precise
locators. Register recurring sources in `docs/knowledge/mdblueprint.yml` using
publisher or DOI links. Do not commit textbook PDFs, scans, or OCR output.

Use `## Provenance` or `## Implementation Notes`, not `## References`, for
issues, pull requests, commits, and migration notes.

## Local Validation

Install `mdblueprint` from its public repository, then run from the EconCSLib
root:

```bash
lake build
lake build EconCSLib.Examples
python3 scripts/check_lean_placeholders.py EconCSLib
python3 -m unittest tests/test_check_knowledge_references.py
python3 scripts/check_knowledge_references.py docs/knowledge
mdblueprint-check docs/knowledge --lean-root .
git diff --check
```

The placeholder checker must pass.

To build a preview:

```bash
mdblueprint-publish docs/knowledge /tmp/EconCSLib-main-mdblueprint-site
```

To mirror the publishing wrapper locally:

```bash
python3 scripts/publish_blueprint.py --no-push
```

## CI

`.github/workflows/blueprint.yml` validates pull requests without repository
secrets. On pushes to `main`, it also generates the static site, checks rendered
pages, and deploys to `gametheoryinlean/blueprint`.

Deployment credentials are configured outside the repository.
