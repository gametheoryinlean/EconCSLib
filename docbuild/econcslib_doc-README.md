# EconCSLib API documentation

Auto-generated API documentation for [**EconCSLib**](https://github.com/gametheoryinlean/EconCSLib),
a Lean 4 formal library for game theory and computational economics.

**Live site:** https://gametheoryinlean.github.io/econcslib_doc/

## How this is built

The HTML is produced by [`doc-gen4`](https://github.com/gametheoryinlean/docgen)
(the `external-linking-v4.30.0` branch of the `gametheoryinlean/docgen` fork).
That branch generates pages **only for EconCSLib's own modules**; every reference
to Mathlib or the Lean core resolves to the official
[mathlib4 documentation site](https://leanprover-community.github.io/mathlib4_docs/)
instead of being regenerated here. This keeps the output small (~10 MB) and the
build fast.

> Note: the external links target Mathlib's latest published docs, while
> EconCSLib pins Mathlib `v4.30.0`. Declarations renamed or removed upstream
> after that point may produce stale links.

## Do not edit by hand

This repository's contents are **overwritten** on every documentation build by
the `Deploy API docs` workflow in the
[EconCSLib](https://github.com/gametheoryinlean/EconCSLib) repository. Edit the
Lean sources there, not this repo.
