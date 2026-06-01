# API Documentation Pipeline

EconCSLib publishes a generated Lean API reference.

- **Live site:** <https://gametheoryinlean.github.io/econcslib_doc/>
- **Generator:** [`gametheoryinlean/docgen`](https://github.com/gametheoryinlean/docgen)
- **Build project:** [`docbuild/`](../../docbuild)
- **Generated output repository:** `gametheoryinlean/econcslib_doc`

Generated HTML is not committed to EconCSLib.

## Design

The `docgen` fork emits HTML only for EconCSLib modules and rewrites references
to Mathlib or Lean-core declarations to the official
[Mathlib documentation](https://leanprover-community.github.io/mathlib4_docs/).
This keeps the generated site small while preserving navigable external links.

`docbuild/` is a nested Lake project. Its toolchain must match the main
repository toolchain, and its shared package directory reuses the main
Mathlib cache.

## Local Build

Build the library first:

```bash
lake exe cache get
lake build
```

Then use the convenience wrapper:

```bash
python3 scripts/build_api_docs.py
python3 scripts/build_api_docs.py --serve 8000
```

Or run the underlying commands:

```bash
cd docbuild
MATHLIB_NO_CACHE_ON_UPDATE=1 lake update doc-gen4
LEAN_ABORT_ON_PANIC=1 lake build EconCSLib:docs
```

Output is written to `docbuild/.lake/build/doc/`.

## Deployment

`.github/workflows/docs.yml` builds and deploys API documentation on pushes to
`main` and on manual workflow runs. The local wrapper can mirror deployment:

```bash
python3 scripts/build_api_docs.py --deploy --no-push
python3 scripts/build_api_docs.py --deploy
```

Deployment credentials and account-specific maintenance procedures are
configured outside this repository.
