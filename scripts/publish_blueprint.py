#!/usr/bin/env python3
"""publish_blueprint.py — manually rebuild and publish the EconCSLib blueprint.

Mirrors the steps in ``.github/workflows/blueprint.yml`` for local use.

Default flow:

  1. ``scripts/check_knowledge_references.py docs/knowledge``
  2. ``mdblueprint-check docs/knowledge --lean-root .``
  3. ``mdblueprint-publish docs/knowledge <site>``  (cleans <site> first)
  4. assert required artifacts present (``graph_topics.json``,
     ``dep_graph_document.html``, ``graph.html``, topic subgraphs, node
     payloads)
  5. ``mdblueprint-render-check <site> --timeout-ms 60000``  (skippable)
  6. clone ``git@github.com:gametheoryinlean/blueprint.git`` branch
     ``gh-pages`` (or create orphan branch if absent), rsync site over,
     commit + push.

Examples
--------
``scripts/publish_blueprint.py``
    Full build + publish (will push to the blueprint repo).

``scripts/publish_blueprint.py --no-push``
    Build + commit to a temp publish dir but do not push; prints the dir.

``scripts/publish_blueprint.py --render-check``
    Also run the (slow, Playwright-based) render check. Off by default.

``scripts/publish_blueprint.py --no-rebuild --site-dir /tmp/EconCSLib-main-mdblueprint-site``
    Skip steps 1-5; only sync an existing site to the blueprint repo.

Environment
-----------
Requires the ``mdblueprint-*`` commands on ``PATH``. Pass
``--mdblueprint-home`` to use a local checkout with its virtual environment at
``<home>/.venv``. Publishing uses the ambient SSH agent or keys.
"""

from __future__ import annotations

import argparse
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

# Project repo root (this file lives in <repo>/scripts/)
REPO_ROOT = Path(__file__).resolve().parent.parent
DEFAULT_SITE_DIR = Path("/tmp/EconCSLib-main-mdblueprint-site")
BLUEPRINT_REMOTE = "git@github.com:gametheoryinlean/blueprint.git"
BLUEPRINT_BRANCH = "gh-pages"
ECONCS_REPO = "gametheoryinlean/EconCSLib"


def run(cmd: list, *, cwd: Path | None = None, check: bool = True) -> int:
    """Run a subprocess, streaming output. Returns the exit code."""
    printable = " ".join(str(c) for c in cmd)
    where = f"  (cwd={cwd})" if cwd else ""
    print(f"\n$ {printable}{where}", flush=True)
    r = subprocess.run(cmd, cwd=cwd)
    if check and r.returncode != 0:
        sys.exit(f"command failed (exit {r.returncode}): {printable}")
    return r.returncode


def mdblueprint_bin(mdblueprint_home: Path | None, name: str) -> str:
    """Resolve an mdblueprint command from an explicit venv or PATH."""
    if mdblueprint_home is not None:
        path = mdblueprint_home / ".venv" / "bin" / name
        if not path.is_file():
            sys.exit(f"{name} not found at {path}")
        return str(path)

    path = shutil.which(name)
    if path is None:
        sys.exit(f"{name} not found on PATH (or pass --mdblueprint-home)")
    return path


# ---------------- step impls ----------------


def step_check(mdblueprint_home: Path | None, knowledge_root: Path) -> None:
    """Steps 1-2: knowledge reference + mdblueprint structural check."""
    refs = REPO_ROOT / "scripts" / "check_knowledge_references.py"
    if refs.exists():
        run([sys.executable, str(refs), str(knowledge_root)], cwd=REPO_ROOT)
    else:
        print(f"[skip] {refs} not present in this checkout")
    run(
        [mdblueprint_bin(mdblueprint_home, "mdblueprint-check"), str(knowledge_root),
         "--lean-root", str(REPO_ROOT)],
        cwd=REPO_ROOT,
    )


def step_publish(mdblueprint_home: Path | None, knowledge_root: Path, site_dir: Path) -> None:
    """Step 3: rebuild the static site at site_dir."""
    if site_dir.exists():
        print(f"[clean] removing existing {site_dir}")
        shutil.rmtree(site_dir)
    site_dir.parent.mkdir(parents=True, exist_ok=True)
    run(
        [mdblueprint_bin(mdblueprint_home, "mdblueprint-publish"),
         str(knowledge_root), str(site_dir)],
        cwd=REPO_ROOT,
    )
    (site_dir / ".nojekyll").touch()


def step_verify_artifacts(site_dir: Path) -> None:
    """Step 4: required-file assertions matching the workflow."""
    required = [
        site_dir / "graph_topics.json",
        site_dir / "dep_graph_document.html",
        site_dir / "graph.html",
    ]
    missing = [str(p) for p in required if not p.exists()]
    if missing:
        sys.exit("missing required artifacts:\n  " + "\n  ".join(missing))

    topic_subgraphs = list((site_dir / "subgraphs" / "topics").glob("*.json"))
    node_payloads = list((site_dir / "node_payloads").glob("*.json"))
    if not topic_subgraphs:
        sys.exit("no topic subgraphs generated under subgraphs/topics/")
    if not node_payloads:
        sys.exit("no node payloads generated under node_payloads/")
    print(
        f"[ok] artifacts present"
        f" | topic subgraphs={len(topic_subgraphs)}"
        f" | node payloads={len(node_payloads)}"
    )


def step_render_check(mdblueprint_home: Path | None, site_dir: Path, timeout_ms: int) -> None:
    """Step 5: Playwright-based render check."""
    if mdblueprint_home is not None:
        bin_path = mdblueprint_home / ".venv" / "bin" / "mdblueprint-render-check"
        if not bin_path.exists():
            print(f"[skip] {bin_path} not installed (install playwright if needed)")
            return
        command = str(bin_path)
    else:
        command = shutil.which("mdblueprint-render-check")
    if command is None:
        print("[skip] mdblueprint-render-check not installed (install playwright if needed)")
        return
    run([command, str(site_dir), "--timeout-ms", str(timeout_ms)],
        cwd=REPO_ROOT)


def step_publish_to_remote(site_dir: Path, source_sha: str,
                            *, dry_run: bool) -> None:
    """Step 6: rsync site into a clone of the blueprint repo + commit + push."""
    publish_dir = Path(tempfile.mkdtemp(prefix="econcs-blueprint-publish-"))
    print(f"[publish] working dir: {publish_dir}")

    branch_exists = subprocess.run(
        ["git", "ls-remote", "--exit-code", "--heads",
         BLUEPRINT_REMOTE, BLUEPRINT_BRANCH],
        capture_output=True,
    ).returncode == 0

    if branch_exists:
        run(["git", "clone", "--depth", "1", "--branch", BLUEPRINT_BRANCH,
             BLUEPRINT_REMOTE, str(publish_dir)])
    else:
        run(["git", "clone", "--depth", "1",
             BLUEPRINT_REMOTE, str(publish_dir)])
        run(["git", "checkout", "--orphan", BLUEPRINT_BRANCH], cwd=publish_dir)
        run(["git", "rm", "-rf", "."], cwd=publish_dir, check=False)

    run(["rsync", "-a", "--delete", "--exclude", ".git",
         f"{site_dir}/", f"{publish_dir}/"])

    run(["git", "add", "-A"], cwd=publish_dir)
    no_changes = subprocess.run(
        ["git", "diff", "--cached", "--quiet"], cwd=publish_dir,
    ).returncode == 0
    if no_changes:
        print("[ok] no blueprint changes to publish.")
        shutil.rmtree(publish_dir, ignore_errors=True)
        return

    subject = f"Build blueprint from EconCSLib {source_sha}"
    body = f"Source: https://github.com/{ECONCS_REPO}/commit/{source_sha}"
    run(["git", "commit", "-m", subject, "-m", body], cwd=publish_dir)

    if dry_run:
        print(f"\n[dry-run] would push to {BLUEPRINT_REMOTE} {BLUEPRINT_BRANCH}")
        print(f"[dry-run] publish dir kept at: {publish_dir}")
        return

    run(["git", "push", "origin", BLUEPRINT_BRANCH], cwd=publish_dir)
    print(f"[ok] published to {BLUEPRINT_REMOTE} {BLUEPRINT_BRANCH}")
    shutil.rmtree(publish_dir, ignore_errors=True)


# ---------------- orchestration ----------------


def current_sha() -> str:
    r = subprocess.run(
        ["git", "rev-parse", "HEAD"],
        cwd=REPO_ROOT, capture_output=True, text=True, check=True,
    )
    return r.stdout.strip()


def main() -> None:
    p = argparse.ArgumentParser(
        description="Manual blueprint rebuild + publish (mirror of CI workflow).",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=__doc__,
    )
    p.add_argument("--mdblueprint-home", type=Path,
                   help="optional local mdblueprint checkout with .venv/")
    p.add_argument("--knowledge-root", type=Path,
                   default=REPO_ROOT / "docs" / "knowledge",
                   help="knowledge directory (default: docs/knowledge)")
    p.add_argument("--site-dir", type=Path, default=DEFAULT_SITE_DIR,
                   help=f"static site output dir (default: {DEFAULT_SITE_DIR})")
    p.add_argument("--render-timeout-ms", type=int, default=60000,
                   help="render-check timeout in ms (default: 60000)")
    p.add_argument("--no-check", action="store_true",
                   help="skip knowledge ref + mdblueprint-check steps")
    p.add_argument("--render-check", action="store_true",
                   help="run Playwright render check (slow; off by default)")
    p.add_argument("--no-rebuild", action="store_true",
                   help="reuse existing --site-dir; skip check/publish/verify/render")
    p.add_argument("--no-push", action="store_true",
                   help="build + commit to a local temp dir; skip git push")
    args = p.parse_args()

    knowledge_root = args.knowledge_root.resolve()
    site_dir = args.site_dir.resolve()

    print(f"[cfg] repo root      = {REPO_ROOT}")
    print(f"[cfg] mdblueprint    = {args.mdblueprint_home or 'PATH'}")
    print(f"[cfg] knowledge root = {knowledge_root}")
    print(f"[cfg] site dir       = {site_dir}")
    print(f"[cfg] blueprint repo = {BLUEPRINT_REMOTE} ({BLUEPRINT_BRANCH})")

    if not args.no_rebuild:
        if not args.no_check:
            step_check(args.mdblueprint_home, knowledge_root)
        step_publish(args.mdblueprint_home, knowledge_root, site_dir)
        step_verify_artifacts(site_dir)
        if args.render_check:
            step_render_check(args.mdblueprint_home, site_dir, args.render_timeout_ms)
    else:
        if not site_dir.is_dir():
            sys.exit(f"--no-rebuild was set but site dir does not exist: {site_dir}")
        print(f"[skip] reusing existing site at {site_dir}")

    step_publish_to_remote(site_dir, current_sha(), dry_run=args.no_push)
    print("\n[done]")


if __name__ == "__main__":
    main()
