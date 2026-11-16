#!/usr/bin/env python3
"""Reject growth of the governed Canonical/Frontend EFG API surface.

This source-level guard is intentionally narrower than a source-compatibility
checker. It snapshots explicit public declarations owned by registered
Canonical and Frontend modules, plus the module paths themselves. Internal and
Experimental implementation may continue to evolve behind the governed
facades.
"""

from __future__ import annotations

import argparse
from collections import Counter
from dataclasses import dataclass
import json
from pathlib import Path
import re
import sys

try:
    from check_efg_governance import strip_lean_comments_and_strings
    from report_efg_declaration_usage import read_module_register
except ModuleNotFoundError:
    from scripts.check_efg_governance import strip_lean_comments_and_strings
    from scripts.report_efg_declaration_usage import read_module_register


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_BASELINE = ROOT / "scripts/efg_api_growth_baseline.json"
FROZEN_LIFECYCLES = ("Canonical", "Frontend")
SCHEMA_VERSION = 1

DECL_RE = re.compile(
    r"^[ \t]*"
    r"(?P<prefix>(?:(?:private|protected|noncomputable|unsafe|partial|local)"
    r"[ \t]+)*)"
    r"(?P<kind>abbrev|def|opaque|theorem|lemma|structure|class|inductive)"
    r"[ \t\r\n]+"
    r"(?P<name>[^\s(:\[\{]+)",
    re.MULTILINE,
)
INSTANCE_RE = re.compile(
    r"^[ \t]*"
    r"(?P<prefix>(?:(?:private|protected|noncomputable|unsafe|partial|local|scoped)"
    r"[ \t]+)*)"
    r"instance(?P<header>.*?)(?:[ \t]+where|[ \t]*:=)",
    re.MULTILINE | re.DOTALL,
)


@dataclass(frozen=True, order=True)
class SurfaceEntry:
    lifecycle: str
    module: str
    kind: str
    name: str


def public_surface_entries(
    module: str,
    lifecycle: str,
    source: str,
) -> Counter[SurfaceEntry]:
    """Return explicit public declarations in one registered source module."""

    source = strip_lean_comments_and_strings(source)
    entries: Counter[SurfaceEntry] = Counter()
    for match in DECL_RE.finditer(source):
        modifiers = match.group("prefix").split()
        if "private" in modifiers or "local" in modifiers:
            continue
        entries[
            SurfaceEntry(
                lifecycle=lifecycle,
                module=module,
                kind=match.group("kind"),
                name=match.group("name"),
            )
        ] += 1

    for match in INSTANCE_RE.finditer(source):
        modifiers = match.group("prefix").split()
        if "private" in modifiers or "local" in modifiers:
            continue
        header = re.sub(r"\s+", " ", match.group("header").strip())
        entries[
            SurfaceEntry(
                lifecycle=lifecycle,
                module=module,
                kind="instance",
                name=header or "<anonymous>",
            )
        ] += 1
    return entries


def current_snapshot() -> tuple[list[str], Counter[SurfaceEntry]]:
    modules: list[str] = []
    entries: Counter[SurfaceEntry] = Counter()
    for module, lifecycle, path in read_module_register():
        if lifecycle not in FROZEN_LIFECYCLES:
            continue
        modules.append(module)
        entries.update(
            public_surface_entries(
                module,
                lifecycle,
                path.read_text(encoding="utf-8"),
            )
        )
    return sorted(modules), entries


def snapshot_json(
    modules: list[str],
    entries: Counter[SurfaceEntry],
) -> str:
    records = [
        "\t".join(
            (entry.lifecycle, entry.module, entry.kind, entry.name)
        )
        for entry, count in sorted(entries.items())
        for _occurrence in range(count)
    ]
    payload = {
        "schema": SCHEMA_VERSION,
        "frozen_lifecycles": list(FROZEN_LIFECYCLES),
        "modules": modules,
        "declarations": records,
    }
    return json.dumps(payload, ensure_ascii=False, indent=2) + "\n"


def load_snapshot(
    path: Path,
) -> tuple[list[str], Counter[SurfaceEntry]]:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if payload.get("schema") != SCHEMA_VERSION:
        raise ValueError(
            f"unsupported API-growth baseline schema: {payload.get('schema')}"
        )
    if tuple(payload.get("frozen_lifecycles", ())) != FROZEN_LIFECYCLES:
        raise ValueError("API-growth baseline lifecycle set does not match policy")

    modules = payload.get("modules")
    declarations = payload.get("declarations")
    if not isinstance(modules, list) or not isinstance(declarations, list):
        raise ValueError("API-growth baseline has invalid modules/declarations")

    entries: Counter[SurfaceEntry] = Counter()
    for record in declarations:
        try:
            lifecycle, module, kind, name = record.split("\t", 3)
            entry = SurfaceEntry(
                lifecycle=lifecycle,
                module=module,
                kind=kind,
                name=name,
            )
        except (AttributeError, TypeError, ValueError) as error:
            raise ValueError(
                f"invalid API-growth declaration record: {record!r}"
            ) from error
        entries[entry] += 1
    return modules, entries


def api_growth(
    baseline_modules: list[str],
    baseline_entries: Counter[SurfaceEntry],
    current_modules: list[str],
    current_entries: Counter[SurfaceEntry],
) -> tuple[list[str], Counter[SurfaceEntry]]:
    new_modules = sorted(set(current_modules) - set(baseline_modules))
    return new_modules, current_entries - baseline_entries


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--baseline",
        type=Path,
        default=DEFAULT_BASELINE,
        help="checked API-growth snapshot",
    )
    parser.add_argument(
        "--update-baseline",
        action="store_true",
        help="replace the snapshot with the current reviewed surface",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    baseline = args.baseline
    if not baseline.is_absolute():
        baseline = ROOT / baseline

    try:
        current_modules, current_entries = current_snapshot()
        if args.update_baseline:
            baseline.parent.mkdir(parents=True, exist_ok=True)
            baseline.write_text(
                snapshot_json(current_modules, current_entries),
                encoding="utf-8",
            )
            print(
                f"Wrote EFG API-growth baseline: {len(current_modules)} modules, "
                f"{sum(current_entries.values())} explicit public declarations "
                f"to {baseline}"
            )
            return 0

        baseline_modules, baseline_entries = load_snapshot(baseline)
    except (OSError, ValueError, json.JSONDecodeError) as error:
        print(f"EFG API-growth check error: {error}", file=sys.stderr)
        return 2

    new_modules, added_entries = api_growth(
        baseline_modules,
        baseline_entries,
        current_modules,
        current_entries,
    )
    removed_modules = sorted(set(baseline_modules) - set(current_modules))
    removed_entries = baseline_entries - current_entries

    if new_modules:
        print("New Canonical/Frontend modules after the API-growth freeze:")
        for module in new_modules:
            print(f"  {module}")
    if added_entries:
        print("New explicit Canonical/Frontend declarations after the freeze:")
        for entry, count in sorted(added_entries.items()):
            suffix = f" ×{count}" if count > 1 else ""
            print(
                f"  {entry.module}: {entry.kind} {entry.name}{suffix}"
            )

    print(
        "EFG API-growth check: "
        f"{len(current_modules)} governed modules, "
        f"{sum(current_entries.values())} explicit public declarations, "
        f"{len(new_modules)} new modules, "
        f"{sum(added_entries.values())} added declarations, "
        f"{len(removed_modules)} removed modules, "
        f"{sum(removed_entries.values())} removed declarations"
    )
    if new_modules or added_entries:
        print(
            "The Canonical/Frontend API-growth freeze forbids additions. "
            "Do not update the baseline without an explicit policy decision.",
            file=sys.stderr,
        )
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
