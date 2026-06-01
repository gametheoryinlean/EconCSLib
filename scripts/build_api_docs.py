#!/usr/bin/env python3
"""build_api_docs.py — build (and optionally publish) the EconCSLib API docs.

Mirrors the steps in ``.github/workflows/docs.yml`` for local use. The docs are
produced by ``doc-gen4`` via the nested ``docbuild/`` project, which pulls the
``external-linking-v4.30.0`` branch of the ``gametheoryinlean/docgen`` fork and
emits HTML only for EconCSLib's own modules (Mathlib / Lean-core references link
out to the hosted mathlib4_docs site). See ``docs/maintainers/api-docs.md`` for the full
design.

Default flow:

  1. ``lake update doc-gen4``        (in docbuild/, clones doc-gen4 + its deps)
  2. ``lake build EconCSLib:docs``   (in docbuild/, generates the HTML)
  3. print the output dir (docbuild/.lake/build/doc)

With ``--deploy`` it additionally clones ``gametheoryinlean/econcslib_doc``,
syncs the output in (plus the repo README and ``.nojekyll``), commits, and
pushes to ``main`` — the same site that GitHub Pages serves.

Examples
--------
``scripts/build_api_docs.py``
    Build the docs locally; print the output directory.

``scripts/build_api_docs.py --serve 8000``
    Build, then serve the output over HTTP at http://localhost:8000/ (required
    because the browser Same-Origin Policy breaks file:// docs).

``scripts/build_api_docs.py --no-update``
    Skip ``lake update doc-gen4`` (faster on a warm checkout).

``scripts/build_api_docs.py --deploy``
    Build, then publish to gametheoryinlean/econcslib_doc (pushes to main).

``scripts/build_api_docs.py --deploy --no-push``
    Build + stage the publish dir but do not push; prints the dir.

Requirements
------------
EconCSLib must build first (``lake exe cache get && lake build`` at the repo
root) so the ``.olean``s exist; ``docbuild`` reuses them via the shared package
cache. Pushing uses the ambient ssh agent / keys (same as ``git push origin``).
"""

from __future__ import annotations

import argparse
import os
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

# Project repo root (this file lives in <repo>/scripts/)
REPO_ROOT = Path(__file__).resolve().parent.parent
DOCBUILD = REPO_ROOT / "docbuild"
DOC_OUT = DOCBUILD / ".lake" / "build" / "doc"
DOC_REPO_REMOTE = "git@github.com:gametheoryinlean/econcslib_doc.git"
DOC_REPO_BRANCH = "main"
ECONCS_REPO = "gametheoryinlean/EconCSLib"
README_SRC = DOCBUILD / "econcslib_doc-README.md"


def run(
    cmd: list,
    *,
    cwd: Path | None = None,
    env: dict | None = None,
    check: bool = True,
) -> int:
    """Run a subprocess, streaming output. Returns the exit code."""
    printable = " ".join(str(c) for c in cmd)
    where = f"  (cwd={cwd})" if cwd else ""
    print(f"\n$ {printable}{where}", flush=True)
    merged_env = {**os.environ, **env} if env else None
    r = subprocess.run(cmd, cwd=cwd, env=merged_env)
    if check and r.returncode != 0:
        sys.exit(f"command failed (exit {r.returncode}): {printable}")
    return r.returncode


def current_sha() -> str:
    r = subprocess.run(
        ["git", "rev-parse", "HEAD"],
        cwd=REPO_ROOT, capture_output=True, text=True, check=True,
    )
    return r.stdout.strip()


# ---------------- step impls ----------------


def step_build(*, do_update: bool, cache_get: bool, clean: bool = True) -> None:
    """Steps 1-2: resolve doc-gen4 and generate the HTML in docbuild/."""
    if not DOCBUILD.is_dir():
        sys.exit(f"docbuild/ not found at {DOCBUILD}")

    if cache_get:
        run(["lake", "exe", "cache", "get"], cwd=REPO_ROOT)
        run(["lake", "build"], cwd=REPO_ROOT)

    if do_update:
        # MATHLIB_NO_CACHE_ON_UPDATE mirrors the workflow / doc-gen4 README.
        run(
            ["lake", "update", "doc-gen4"],
            cwd=DOCBUILD,
            env={"MATHLIB_NO_CACHE_ON_UPDATE": "1"},
        )

    if clean:
        # Purge the doc cache so doc-gen4 regenerates HTML from the *current*
        # oleans. Without this, lake can "Replay" a stale `:docs` target — the
        # per-module `doc-data/*.trace` files don't always invalidate when the
        # upstream oleans change — silently publishing outdated docs while
        # `--deploy` reports "no changes". See issue tracker.
        doc_build = DOCBUILD / ".lake" / "build"
        for stale in ("doc", "doc-data", "doc-manifest.json"):
            target = doc_build / stale
            if target.is_dir():
                shutil.rmtree(target, ignore_errors=True)
            elif target.exists():
                target.unlink()
        print("[clean] purged stale doc cache (doc / doc-data / doc-manifest.json)")

    run(
        ["lake", "build", "EconCSLib:docs"],
        cwd=DOCBUILD,
        env={"LEAN_ABORT_ON_PANIC": "1"},
    )

    if not (DOC_OUT / "index.html").exists():
        sys.exit(f"build finished but {DOC_OUT / 'index.html'} is missing")

    pages = len(list(DOC_OUT.glob("EconCSLib/**/*.html"))) + 1  # + EconCSLib.html
    print(f"\n[ok] docs built at {DOC_OUT}  ({pages} EconCSLib pages)")


def step_serve(port: int) -> None:
    """Serve the output over HTTP (blocks until Ctrl-C)."""
    print(f"\n[serve] http://localhost:{port}/  (Ctrl-C to stop)")
    run(["python3", "-m", "http.server", str(port)], cwd=DOC_OUT)


def step_deploy(source_sha: str, *, dry_run: bool) -> None:
    """Sync the output into a clone of econcslib_doc, commit, and push main."""
    if not (DOC_OUT / "index.html").exists():
        sys.exit(f"nothing to deploy: {DOC_OUT} is empty (run a build first)")

    publish_dir = Path(tempfile.mkdtemp(prefix="econcslib-doc-publish-"))
    print(f"[deploy] working dir: {publish_dir}")

    run(["git", "clone", "--depth", "1", "--branch", DOC_REPO_BRANCH,
         DOC_REPO_REMOTE, str(publish_dir)])

    run(["rsync", "-a", "--delete", "--exclude", ".git",
         f"{DOC_OUT}/", f"{publish_dir}/"])

    # Keep the human-facing README + disable Jekyll, matching the CI deploy.
    if README_SRC.exists():
        shutil.copyfile(README_SRC, publish_dir / "README.md")
    (publish_dir / ".nojekyll").touch()

    run(["git", "add", "-A"], cwd=publish_dir)
    no_changes = subprocess.run(
        ["git", "diff", "--cached", "--quiet"], cwd=publish_dir,
    ).returncode == 0
    if no_changes:
        print("[ok] no doc changes to publish.")
        shutil.rmtree(publish_dir, ignore_errors=True)
        return

    subject = f"docs: deploy from EconCSLib {source_sha}"
    body = f"Source: https://github.com/{ECONCS_REPO}/commit/{source_sha}"
    run(["git", "commit", "-m", subject, "-m", body], cwd=publish_dir)

    if dry_run:
        print(f"\n[dry-run] would push to {DOC_REPO_REMOTE} {DOC_REPO_BRANCH}")
        print(f"[dry-run] publish dir kept at: {publish_dir}")
        return

    run(["git", "push", "origin", DOC_REPO_BRANCH], cwd=publish_dir)
    print(f"[ok] published to {DOC_REPO_REMOTE} {DOC_REPO_BRANCH}")
    print("     live at https://gametheoryinlean.github.io/econcslib_doc/")
    shutil.rmtree(publish_dir, ignore_errors=True)


# ---------------- orchestration ----------------


def main() -> None:
    p = argparse.ArgumentParser(
        description="Build (and optionally publish) the EconCSLib API docs "
                    "(mirror of CI workflow).",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=__doc__,
    )
    p.add_argument("--no-update", action="store_true",
                   help="skip `lake update doc-gen4` (faster on a warm checkout)")
    p.add_argument("--cache-get", action="store_true",
                   help="run `lake exe cache get && lake build` at the repo root "
                        "first (ensures the library oleans are current)")
    p.add_argument("--no-build", action="store_true",
                   help="skip the build; act on the existing output dir "
                        "(use with --serve or --deploy)")
    p.add_argument("--no-clean", action="store_true",
                   help="do not purge the doc cache before building "
                        "(faster, but risks publishing a stale `:docs` replay)")
    p.add_argument("--serve", nargs="?", type=int, const=8000, metavar="PORT",
                   help="serve the output over HTTP after building "
                        "(default port 8000)")
    p.add_argument("--deploy", action="store_true",
                   help="publish the output to gametheoryinlean/econcslib_doc")
    p.add_argument("--no-push", action="store_true",
                   help="with --deploy: stage the publish dir but do not push")
    args = p.parse_args()

    print(f"[cfg] repo root   = {REPO_ROOT}")
    print(f"[cfg] docbuild    = {DOCBUILD}")
    print(f"[cfg] output dir  = {DOC_OUT}")
    print(f"[cfg] doc repo    = {DOC_REPO_REMOTE} ({DOC_REPO_BRANCH})")

    if not args.no_build:
        step_build(do_update=not args.no_update, cache_get=args.cache_get,
                   clean=not args.no_clean)
    elif not (DOC_OUT / "index.html").exists():
        sys.exit(f"--no-build was set but no docs at {DOC_OUT}")

    if args.deploy:
        step_deploy(current_sha(), dry_run=args.no_push)

    if args.serve is not None:
        step_serve(args.serve)  # blocks last

    print("\n[done]")


if __name__ == "__main__":
    main()
