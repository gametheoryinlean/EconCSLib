#!/usr/bin/env python3
"""Check that knowledge-node References sections cite literature, not GitHub provenance."""

from __future__ import annotations

import argparse
import re
import sys
from dataclasses import dataclass
from pathlib import Path


FORBIDDEN_PATTERNS = (
    re.compile(r"https?://(?:www\.)?github\.com/", re.IGNORECASE),
    re.compile(r"\bPR\s*#?\d+\b", re.IGNORECASE),
    re.compile(r"\bpull request\s*#?\d+\b", re.IGNORECASE),
    re.compile(r"\bissue\s*#?\d+\b", re.IGNORECASE),
    re.compile(r"\bpull/\d+\b", re.IGNORECASE),
    re.compile(r"\bissues/\d+\b", re.IGNORECASE),
    re.compile(r"\bcommit\s+[0-9a-f]{7,40}\b", re.IGNORECASE),
    re.compile(r"\bleanblueprint\b", re.IGNORECASE),
    re.compile(r"\bblueprint/src\b", re.IGNORECASE),
    re.compile(r"\bold blueprint\b", re.IGNORECASE),
)

HEADING_RE = re.compile(r"^(#{1,6})\s+(.+?)\s*$")


@dataclass(frozen=True)
class Diagnostic:
    path: Path
    line: int
    text: str


def _reference_lines(text: str) -> list[tuple[int, str]]:
    """Return lines that occur inside any Markdown `## References` section."""
    in_references = False
    result: list[tuple[int, str]] = []
    for line_number, line in enumerate(text.splitlines(), start=1):
        heading = HEADING_RE.match(line)
        if heading is not None:
            level = len(heading.group(1))
            title = heading.group(2).strip().lower()
            if level <= 2:
                in_references = title == "references"
            continue

        if in_references:
            result.append((line_number, line))
    return result


def check_file(path: Path) -> list[Diagnostic]:
    text = path.read_text(encoding="utf-8")
    diagnostics: list[Diagnostic] = []
    for line_number, line in _reference_lines(text):
        if any(pattern.search(line) for pattern in FORBIDDEN_PATTERNS):
            diagnostics.append(Diagnostic(path=path, line=line_number, text=line.strip()))
    return diagnostics


def check_path(path: Path) -> list[Diagnostic]:
    if path.is_file():
        paths = [path]
    else:
        paths = sorted(path.rglob("*.md"))

    diagnostics: list[Diagnostic] = []
    for md_path in paths:
        diagnostics.extend(check_file(md_path))
    return diagnostics


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Reject GitHub/provenance links inside Markdown ## References sections."
    )
    parser.add_argument("paths", nargs="+", type=Path)
    args = parser.parse_args(argv)

    diagnostics: list[Diagnostic] = []
    for path in args.paths:
        diagnostics.extend(check_path(path))

    for diagnostic in diagnostics:
        print(f"{diagnostic.path}:{diagnostic.line}: {diagnostic.text}")

    return 1 if diagnostics else 0


if __name__ == "__main__":
    sys.exit(main())
