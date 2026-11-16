#!/usr/bin/env python3
"""Report heuristic consumers of registered EFG theorem declarations.

This is an API-triage report, not a dead-code oracle.  Lean declarations can
be legitimate public endpoints even when no declaration in this repository
uses them.  The report therefore keeps zero-indegree, documentation, example,
test, privacy, and lifecycle evidence separate.
"""

from __future__ import annotations

import argparse
from collections import Counter, defaultdict
from dataclasses import dataclass
from pathlib import Path
import re
import sys

try:
    from check_efg_governance import strip_lean_comments_and_strings
except ModuleNotFoundError:
    from scripts.check_efg_governance import strip_lean_comments_and_strings


ROOT = Path(__file__).resolve().parents[1]
REGISTER = ROOT / "docs/design/efg-module-status.md"
LIFECYCLES = (
    "Canonical",
    "Frontend",
    "Historical",
    "Compatibility",
    "Experimental",
    "Internal",
)
MODULE_ROW_RE = re.compile(
    r"^\| `(?P<module>EconCSLib[^`]+)` \| "
    r"(?P<lifecycle>"
    + "|".join(LIFECYCLES)
    + r") \|",
    re.MULTILINE,
)
DECL_RE = re.compile(
    r"^[ \t]*(?P<prefix>(?:(?:private|protected|noncomputable)[ \t]+)*)"
    r"(?P<kind>theorem|lemma)[ \t\r\n]+"
    r"(?P<name>[^\s(:\[\{]+)",
    re.MULTILINE,
)
TOKEN_RE = re.compile(r"[^\W\d][\w']*", re.UNICODE)
PRIVATE_ROUTE_MARKERS = (
    "_viaContinuationFamily",
    "_viaInformationRefinement",
    "_viaContinuationSimulation",
)
PUBLIC_ENDPOINT_LIFECYCLES = ("Canonical", "Frontend")
# Current conservative ceiling for public declarations that lack repository
# evidence for their endpoint role. This is not permission to delete any
# declaration: textual indegree cannot decide mathematical endpoint value.
MAX_UNCLASSIFIED_PUBLIC_REVIEW = 0
TRAILING_ATTRIBUTE_RE = re.compile(
    r"@\[(?P<attributes>[^\]]*)\]\s*$",
    re.MULTILINE,
)
GUARDED_COMMAND_RE = re.compile(
    r"^[ \t]*#guard_msgs\b[^\n]*\n"
    r".*?(?=^[ \t]*\n|\Z)",
    re.MULTILINE | re.DOTALL,
)
IMPORT_LINE_RE = re.compile(r"^[ \t]*import\b[^\n]*$", re.MULTILINE)


@dataclass(frozen=True)
class Declaration:
    module: str
    lifecycle: str
    path: Path
    kind: str
    name: str
    line: int
    is_private: bool
    has_simp_attribute: bool
    has_doc_comment: bool


@dataclass(frozen=True)
class Usage:
    declaration: Declaration
    source_references: int
    example_references: int
    facade_contract_references: int
    documentation_references: int
    test_references: int

    @property
    def zero_indegree(self) -> bool:
        return self.source_references == 0

    @property
    def has_endpoint_evidence(self) -> bool:
        return (
            self.documentation_references
            + self.example_references
            + self.facade_contract_references
            + self.test_references
        ) > 0

    @property
    def review_class(self) -> str:
        """Deterministic first-pass role; never an automatic deletion rule."""

        if not self.zero_indegree:
            return "source-used"
        if self.declaration.is_private or self.declaration.lifecycle == "Internal":
            return "proof-helper-only"
        if self.declaration.lifecycle == "Historical":
            return "historical-only"
        if self.declaration.has_simp_attribute:
            return "simp-normalization-api"
        if (
            ".Compiler." in self.declaration.module
            or ".FOSG." in self.declaration.module
        ):
            return "compiler-preservation-endpoint"
        if self.facade_contract_references:
            return "facade-contract-declaration"
        if self.has_endpoint_evidence:
            return "intentional-public-endpoint"
        if self.declaration.has_doc_comment:
            return "source-documented-public-endpoint"
        if self.declaration.lifecycle in PUBLIC_ENDPOINT_LIFECYCLES:
            return "unclassified-public-endpoint"
        return "lifecycle-review"


def module_path(module: str) -> Path:
    parts = module.split(".")
    if parts[0] != "EconCSLib":
        raise ValueError(f"unsupported module outside EconCSLib: {module}")
    return ROOT.joinpath(*parts).with_suffix(".lean")


def read_module_register() -> list[tuple[str, str, Path]]:
    text = REGISTER.read_text(encoding="utf-8")
    rows: list[tuple[str, str, Path]] = []
    seen: set[str] = set()
    for match in MODULE_ROW_RE.finditer(text):
        module = match.group("module")
        lifecycle = match.group("lifecycle")
        if module in seen:
            raise ValueError(f"duplicate lifecycle row: {module}")
        seen.add(module)
        path = module_path(module)
        if not path.is_file():
            raise FileNotFoundError(
                f"registered module has no source file: {module} ({path})"
            )
        rows.append((module, lifecycle, path))
    if not rows:
        raise ValueError(f"no module rows found in {REGISTER}")
    return rows


def declarations(
    rows: list[tuple[str, str, Path]],
) -> tuple[list[Declaration], Counter[str]]:
    found: list[Declaration] = []
    declaration_names: Counter[str] = Counter()
    for module, lifecycle, path in rows:
        text = path.read_text(encoding="utf-8")
        for match in DECL_RE.finditer(text):
            name = match.group("name")
            prefix = match.group("prefix").split()
            has_doc_comment, attributes = declaration_leading_metadata(
                text, match.start()
            )
            found.append(
                Declaration(
                    module=module,
                    lifecycle=lifecycle,
                    path=path,
                    kind=match.group("kind"),
                    name=name,
                    line=text.count("\n", 0, match.start()) + 1,
                    is_private="private" in prefix,
                    has_simp_attribute=any(
                        re.search(r"\bsimp\b", attribute) is not None
                        for attribute in attributes
                    ),
                    has_doc_comment=has_doc_comment,
                )
            )
            declaration_names[name.rsplit(".", 1)[-1]] += 1
    return found, declaration_names


def token_counts(paths: list[Path]) -> Counter[str]:
    counts: Counter[str] = Counter()
    for path in paths:
        if path.is_file():
            counts.update(TOKEN_RE.findall(path.read_text(encoding="utf-8")))
    return counts


def declaration_leading_metadata(
    text: str, declaration_start: int
) -> tuple[bool, list[str]]:
    """Return adjacent doc-comment and attribute evidence for a declaration."""

    prefix = text[:declaration_start].rstrip()
    attributes: list[str] = []
    while attribute_match := TRAILING_ATTRIBUTE_RE.search(prefix):
        attributes.append(attribute_match.group("attributes"))
        prefix = prefix[: attribute_match.start()].rstrip()
    if not prefix.endswith("-/"):
        return False, attributes
    comment_start = prefix.rfind("/-")
    has_doc_comment = (
        comment_start >= 0
        and prefix.startswith("/--", comment_start)
    )
    return has_doc_comment, attributes


def facade_contract_token_counts(paths: list[Path]) -> Counter[str]:
    """Count positive boundary witnesses, excluding imports and negative guards.

    Import-boundary files use `#guard_msgs` to assert that a name is absent.
    Such an occurrence is evidence against facade exposure, not evidence that
    the declaration is a positive facade contract.
    """

    counts: Counter[str] = Counter()
    for path in paths:
        if not path.is_file():
            continue
        text = path.read_text(encoding="utf-8")
        text = strip_lean_comments_and_strings(text)
        text = GUARDED_COMMAND_RE.sub("", text)
        text = IMPORT_LINE_RE.sub("", text)
        counts.update(TOKEN_RE.findall(text))
    return counts


def repository_usage(
    rows: list[tuple[str, str, Path]],
    found: list[Declaration],
    declaration_names: Counter[str],
) -> list[Usage]:
    registered_paths = [path for _module, _lifecycle, path in rows]
    source_counts = token_counts(registered_paths)
    all_example_paths = sorted((ROOT / "EconCSLib/Examples").rglob("*.lean"))
    facade_contract_paths = [
        path for path in all_example_paths if path.name.endswith("ImportBoundary.lean")
    ]
    example_counts = token_counts(
        [path for path in all_example_paths if path not in facade_contract_paths]
    )
    facade_contract_counts = facade_contract_token_counts(facade_contract_paths)
    documentation_counts = token_counts(sorted((ROOT / "docs").rglob("*.md")))
    test_counts = token_counts(
        sorted((ROOT / "tests").rglob("*.py"))
        + sorted((ROOT / "scripts").rglob("*.py"))
    )

    usage: list[Usage] = []
    for declaration in found:
        name = declaration.name.rsplit(".", 1)[-1]
        usage.append(
            Usage(
                declaration=declaration,
                source_references=max(
                    0, source_counts[name] - declaration_names[name]
                ),
                example_references=example_counts[name],
                facade_contract_references=facade_contract_counts[name],
                documentation_references=documentation_counts[name],
                test_references=test_counts[name],
            )
        )
    return usage


def public_route_regressions(usage: list[Usage]) -> list[Declaration]:
    return [
        item.declaration
        for item in usage
        if not item.declaration.is_private
        and item.declaration.lifecycle != "Internal"
        and any(marker in item.declaration.name for marker in PRIVATE_ROUTE_MARKERS)
    ]


def rel(path: Path) -> str:
    return path.relative_to(ROOT).as_posix()


def render_report(usage: list[Usage]) -> str:
    by_lifecycle: dict[str, list[Usage]] = defaultdict(list)
    for item in usage:
        by_lifecycle[item.declaration.lifecycle].append(item)

    lines = [
        "# EFG Declaration Usage Report",
        "",
        "Generated by `scripts/report_efg_declaration_usage.py` from the",
        "lifecycle register and the current source tree.",
        "",
        "> This is a conservative textual dependency report, not a deletion",
        "> list. A zero-indegree theorem may be an intentional public endpoint.",
        "> Short-name collisions can only hide candidates; they do not create",
        "> false zero-indegree findings.",
        "",
        "## Summary",
        "",
        "| Lifecycle | Theorems/lemmas | Zero source indegree | Intentional endpoint | Source-doc endpoint | `[simp]`/normalization | Facade contract | Compiler preservation | Proof helper | Historical only | Unclassified public review |",
        "|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|",
    ]
    for lifecycle in LIFECYCLES:
        items = by_lifecycle.get(lifecycle, [])
        lines.append(
            f"| {lifecycle} | {len(items)} | "
            f"{sum(item.zero_indegree for item in items)} | "
            f"{sum(item.review_class == 'intentional-public-endpoint' for item in items)} | "
            f"{sum(item.review_class == 'source-documented-public-endpoint' for item in items)} | "
            f"{sum(item.review_class == 'simp-normalization-api' for item in items)} | "
            f"{sum(item.review_class == 'facade-contract-declaration' for item in items)} | "
            f"{sum(item.review_class == 'compiler-preservation-endpoint' for item in items)} | "
            f"{sum(item.review_class == 'proof-helper-only' for item in items)} | "
            f"{sum(item.review_class == 'historical-only' for item in items)} | "
            f"{sum(item.review_class == 'unclassified-public-endpoint' for item in items)} |"
        )

    zero_items = sorted(
        (item for item in usage if item.zero_indegree),
        key=lambda item: (
            LIFECYCLES.index(item.declaration.lifecycle),
            item.declaration.module,
            item.declaration.line,
        ),
    )
    lines.extend(
        [
            "",
            "## Zero-source-indegree declarations",
            "",
            "| Review class | Lifecycle | Visibility | Declaration | Owner | Docs | Examples | Positive facade checks | Tests |",
            "|---|---|---|---|---|---:|---:|---:|---:|",
        ]
    )
    for item in zero_items:
        declaration = item.declaration
        visibility = "private" if declaration.is_private else "name-resolvable"
        owner = f"`{rel(declaration.path)}:{declaration.line}`"
        lines.append(
            f"| {item.review_class} | {declaration.lifecycle} | {visibility} | "
            f"`{declaration.name}` | {owner} | "
            f"{item.documentation_references} | {item.example_references} | "
            f"{item.facade_contract_references} | "
            f"{item.test_references} |"
        )

    lines.extend(
        [
            "",
            "## Triage rule",
            "",
            "A declaration is a deletion or privatization candidate only after",
            "confirming that it has no source consumer, documentation role,",
            "example/test role, or intended public-endpoint role. Lifecycle",
            "policy remains authoritative. `unclassified-public-endpoint` is",
            "only the residual manual-review bucket after the listed syntactic",
            "and repository-evidence classes; it does not mean the declaration",
            "is dead code. Source docstrings count as explicit endpoint evidence,",
            "while names occurring only in negative `#guard_msgs` checks do not.",
            "In particular, no theorem may be deleted solely from this textual",
            "report.",
            "",
        ]
    )
    return "\n".join(lines)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--output",
        type=Path,
        help="write the Markdown report to this path; stdout gets a summary",
    )
    parser.add_argument(
        "--check",
        action="store_true",
        help=(
            "fail on a public route-regression leak or growth of the "
            "unclassified-public review queue"
        ),
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    try:
        rows = read_module_register()
        found, declaration_names = declarations(rows)
        usage = repository_usage(rows, found, declaration_names)
    except (OSError, ValueError) as error:
        print(f"EFG declaration report error: {error}", file=sys.stderr)
        return 2

    report = render_report(usage)
    zero_count = sum(item.zero_indegree for item in usage)
    unclassified_public_count = sum(
        item.review_class == "unclassified-public-endpoint" for item in usage
    )
    route_leaks = public_route_regressions(usage)

    if args.output:
        output = args.output
        if not output.is_absolute():
            output = ROOT / output
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_text(report, encoding="utf-8")
        print(f"Wrote {output}")
    else:
        print(report)

    print(
        f"EFG declaration usage: {len(rows)} modules, {len(usage)} "
        f"theorems/lemmas, {zero_count} zero-source-indegree candidates, "
        f"{unclassified_public_count} unclassified-public-review candidates"
    )
    if route_leaks:
        print(
            "Public route-regression declarations must be private or Internal:",
            file=sys.stderr,
        )
        for declaration in route_leaks:
            print(
                f"  {rel(declaration.path)}:{declaration.line}: "
                f"{declaration.name}",
                file=sys.stderr,
            )
    unclassified_public_growth = (
        unclassified_public_count > MAX_UNCLASSIFIED_PUBLIC_REVIEW
    )
    if unclassified_public_growth:
        print(
            "Unclassified-public review queue grew beyond the "
            f"{MAX_UNCLASSIFIED_PUBLIC_REVIEW} baseline: "
            f"{unclassified_public_count}",
            file=sys.stderr,
        )
    if args.check and (route_leaks or unclassified_public_growth):
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
