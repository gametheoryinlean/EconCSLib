#!/usr/bin/env python3
"""Build every governed EFG, GameForm, and direct probability-support module.

The lifecycle table in ``docs/design/efg-module-status.md`` is the only
hand-maintained module list.  Before invoking Lake, this script checks that
the table and the governed source tree are exact mirrors.  A successful run
therefore asks Lake to elaborate every registered module rather than relying
on whichever modules happen to be reachable from the root aggregate.

With ``--fresh``, only generated ``.olean`` files for the registered modules
and explicitly governed removed paths are removed before the build. This mode
is intended for CI and audits that must demonstrate fresh coverage rather
than inherit stale project artifacts.
"""

from __future__ import annotations

import argparse
from pathlib import Path
import subprocess
import sys

from check_efg_governance import (
    REMOVED_MODULE_PATHS,
    in_scope_modules,
    read_status_rows,
)


ROOT = Path(__file__).resolve().parents[1]
REGISTER = ROOT / "docs/design/efg-module-status.md"


def artifact_path(root: Path, module: str) -> Path:
    """Return Lake's project-local ``.olean`` path for ``module``."""

    return (
        root
        / ".lake/build/lib/lean"
        / Path(*module.split(".")).with_suffix(".olean")
    )


def governed_modules(root: Path) -> tuple[list[str], list[str]]:
    """Read the single lifecycle register and check exact source coverage."""

    register = root / REGISTER.relative_to(ROOT)
    rows, errors = read_status_rows(register)
    scoped = in_scope_modules(root)
    registered = set(rows)
    for module in sorted(scoped - registered):
        errors.append(f"{register}: missing module row for {module}")
    for module in sorted(registered - scoped):
        errors.append(f"{register}: row has no in-scope source module: {module}")
    return sorted(registered), errors


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--root",
        type=Path,
        default=ROOT,
        help="repository root (defaults to this script's parent repository)",
    )
    parser.add_argument(
        "--lake",
        default="lake",
        help="Lake executable (default: lake)",
    )
    parser.add_argument(
        "--fresh",
        action="store_true",
        help=(
            "remove registered and governed-obsolete project .olean files "
            "before building, then require every registered artifact to be "
            "recreated"
        ),
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    root = args.root.resolve()
    modules, errors = governed_modules(root)
    if errors:
        for error in errors:
            print(f"EFG all-module build error: {error}", file=sys.stderr)
        return 2

    artifacts = {module: artifact_path(root, module) for module in modules}
    removed_registered = 0
    removed_obsolete = 0
    if args.fresh:
        build_root = (root / ".lake/build/lib/lean").resolve()
        obsolete_artifacts = {
            module: artifact_path(root, module)
            for module in REMOVED_MODULE_PATHS
        }
        for artifact in [*artifacts.values(), *obsolete_artifacts.values()]:
            resolved = artifact.resolve()
            if not resolved.is_relative_to(build_root):
                print(
                    f"EFG all-module build error: unsafe artifact path {artifact}",
                    file=sys.stderr,
                )
                return 2
            if artifact.is_file():
                artifact.unlink()
                if artifact in artifacts.values():
                    removed_registered += 1
                else:
                    removed_obsolete += 1

    command = [args.lake, "build", *(f"+{module}" for module in modules)]
    print(
        f"Building {len(modules)} governed modules"
        + (
            " after removing "
            f"{removed_registered} registered and {removed_obsolete} obsolete "
            ".olean files"
            if args.fresh
            else ""
        )
        + "."
    )
    completed = subprocess.run(command, cwd=root, check=False)
    if completed.returncode != 0:
        return completed.returncode

    missing = [
        module
        for module, artifact in artifacts.items()
        if not artifact.is_file() or artifact.stat().st_size == 0
    ]
    if missing:
        print(
            "EFG all-module build error: Lake succeeded but these registered "
            "modules have no nonempty .olean:",
            file=sys.stderr,
        )
        for module in missing:
            print(f"  {module}", file=sys.stderr)
        return 1

    print(
        f"EFG all-module build passed: {len(modules)} registered modules, "
        f"{len(artifacts)} nonempty .olean artifacts."
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
