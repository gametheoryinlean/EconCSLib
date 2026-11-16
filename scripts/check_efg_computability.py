#!/usr/bin/env python3
"""Audit every EFG noncomputable identity and enforce its reviewed boundary.

The checked baseline is a temporary declaration-identity ratchet, not an
allowance policy.  The current sorted set of module/declaration pairs must be
a subset of the baseline. Analytic definitions remain counted and require
individual source evidence; protected executable operations must stay clear.

Unlike a text search, the audit asks Lean's elaborated environment via
``Lean.isNoncomputable``.  It therefore also sees declarations inherited from
a ``noncomputable section`` and declarations whose noncomputability is not
spelled at their own source line.
"""

from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
import tempfile


ROOT = Path(__file__).resolve().parents[1]
EFG_ROOT = ROOT / "EconCSLib/GameTheory/ExtensiveGame"
EXAMPLES_ROOT = ROOT / "EconCSLib/Examples/ExtensiveGame"
FINITE_LAW_ROOT = ROOT / "EconCSLib/Math/Probability/FiniteLaw"
EFFECTIVE_PROBABILITY_ROOT = ROOT / "EconCSLib/Math/Probability/Effective"
DEFAULT_BASELINE = ROOT / "scripts/efg_computability_baseline.json"
DEFAULT_CLASSIFICATION = ROOT / "scripts/efg_computability_classification.json"
SCHEMA_VERSION = 2
MARKER = "__EFG_NONCOMPUTABLE__"
AUDIT_LINE_RE = re.compile(
    rf"^{MARKER}\t(?P<module>[^\t]+)\t(?P<declaration>.+)$",
    re.MULTILINE,
)


def module_name(path: Path) -> str:
    """Convert one repository Lean path to its importable module name."""

    return ".".join(path.relative_to(ROOT).with_suffix("").parts)


def audited_modules() -> list[str]:
    """Return probability owners, EFG, and extensive-game example modules."""

    paths = list(EFG_ROOT.rglob("*.lean"))
    paths.append(ROOT / "EconCSLib/Math/Probability/FiniteLaw.lean")
    paths.extend(FINITE_LAW_ROOT.rglob("*.lean"))
    paths.append(ROOT / "EconCSLib/Math/Probability/Effective.lean")
    paths.extend(EFFECTIVE_PROBABILITY_ROOT.rglob("*.lean"))
    paths.extend(EXAMPLES_ROOT.rglob("*.lean"))
    return sorted({module_name(path) for path in paths})


def render_audit_source(modules: list[str]) -> str:
    """Generate a Lean command that prints audited noncomputable constants."""

    imports = "\n".join(f"import {module}" for module in modules)
    names = ",\n    ".join(f"`{module}" for module in modules)
    return f"""{imports}
import Lean.Elab.Command

open Lean Elab Command

elab "#print_efg_noncomputable" : command => do
  let env ← getEnv
  let auditedModules : Array Name := #[
    {names}
  ]
  for (declaration, _) in env.constants.toList do
    if Lean.isNoncomputable env declaration then
      match env.getModuleIdxFor? declaration with
      | none => pure ()
      | some moduleIndex =>
          let owner := (env.header.modules[moduleIndex]!).module
          if auditedModules.contains owner then
            liftIO <| IO.println
              s!"{MARKER}\\t{{owner}}\\t{{declaration}}"

#print_efg_noncomputable
"""


def parse_audit_output(output: str) -> list[tuple[str, str]]:
    """Parse the stable marker lines printed by the generated Lean command."""

    return sorted(
        (match.group("module"), match.group("declaration"))
        for match in AUDIT_LINE_RE.finditer(output)
    )


def counts_by_module(
    entries: list[tuple[str, str]],
) -> Counter[str]:
    return Counter(module for module, _declaration in entries)


def declaration_changes(
    baseline: list[tuple[str, str]], current: list[tuple[str, str]]
) -> tuple[list[tuple[str, str]], list[tuple[str, str]]]:
    """Return declarations added to and removed from the checked identity set."""

    baseline_set = set(baseline)
    current_set = set(current)
    return (
        sorted(current_set - baseline_set),
        sorted(baseline_set - current_set),
    )


def run_command(command: list[str]) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        command,
        cwd=ROOT,
        check=False,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
    )


def ensure_audit_build(modules: list[str], build: bool) -> None:
    """Verify Lake's dependency traces before querying the environment.

    Rehashing also detects changed dependencies whose mtimes were preserved.
    --no-build rejects stale/missing artifacts without silently trusting them.
    """

    command = ["lake", "--rehash"]
    if not build:
        command.append("--no-build")
    result = run_command([*command, "build", *modules])
    if result.returncode != 0:
        print(result.stdout, end="", file=sys.stderr)
        raise RuntimeError(
            "failed to build modules for the EFG audit" if build else
            "stale or missing audit artifacts; rerun without --skip-build"
        )


def query_environment(source: str, prefix: str) -> str:
    """Elaborate an audit command against the verified repository artifacts."""

    audit_path: Path | None = None
    try:
        with tempfile.NamedTemporaryFile(
            mode="w",
            encoding="utf-8",
            prefix=prefix,
            suffix=".lean",
            dir=ROOT,
            delete=False,
        ) as audit_file:
            audit_file.write(source)
            audit_path = Path(audit_file.name)

        result = run_command(["lake", "env", "lean", str(audit_path)])
        if result.returncode != 0:
            print(result.stdout, end="", file=sys.stderr)
            raise RuntimeError("Lean environment audit failed")
        return result.stdout
    finally:
        if audit_path is not None:
            audit_path.unlink(missing_ok=True)


def run_audit(modules: list[str], build: bool) -> list[tuple[str, str]]:
    """Query noncomputable identities after checking artifact freshness."""

    ensure_audit_build(modules, build)
    return parse_audit_output(
        query_environment(render_audit_source(modules), "EfgComputabilityAudit_")
    )


def load_baseline(path: Path) -> list[tuple[str, str]]:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if payload.get("schema") != SCHEMA_VERSION:
        raise ValueError(
            f"unsupported EFG computability baseline schema: "
            f"{payload.get('schema')}"
        )
    raw_entries = payload.get("noncomputable_declarations")
    if not isinstance(raw_entries, list) or not all(
        isinstance(entry, list)
        and len(entry) == 2
        and all(isinstance(value, str) and value for value in entry)
        for entry in raw_entries
    ):
        raise ValueError("invalid EFG computability baseline declarations")
    entries = [(entry[0], entry[1]) for entry in raw_entries]
    if entries != sorted(set(entries)):
        raise ValueError(
            "EFG computability baseline declarations must be sorted and unique"
        )
    return entries


def write_baseline(path: Path, entries: list[tuple[str, str]]) -> None:
    entries = sorted(set(entries))
    payload = {
        "schema": SCHEMA_VERSION,
        "policy": (
            "current module/declaration identities must be a subset; "
            "executable boundaries stay clear; retained analytic identities "
            "require separate review"
        ),
        "noncomputable_declarations": entries,
    }
    path.write_text(
        json.dumps(payload, ensure_ascii=False, indent=2) + "\n",
        encoding="utf-8",
    )


def source_evidence_error(evidence: dict) -> str | None:
    """Check a reviewed source span (or whole regression file) by content."""

    raw_path = evidence.get("path")
    if not isinstance(raw_path, str) or not raw_path:
        return "evidence requires a repository-relative source path"
    path = Path(raw_path)
    if path.is_absolute() or ".." in path.parts or not path.parts:
        return "evidence requires a repository-relative source path"
    source = ROOT / path
    if not source.is_file():
        return f"missing evidence source: {path}"
    text = source.read_text(encoding="utf-8")
    if "line" in evidence or "end_line" in evidence:
        lines = text.splitlines()
        start, end = evidence.get("line"), evidence.get("end_line")
        if not (
            type(start) is int and type(end) is int
            and 1 <= start <= end <= len(lines)
        ):
            return f"invalid evidence range: {path}"
        text = "\n".join(lines[start - 1:end])
    digest = hashlib.sha256(text.encode("utf-8")).hexdigest()
    if evidence.get("sha256") != digest:
        return f"changed review evidence: {path}; inspect and renew the review"
    return None


def load_classification(path: Path) -> dict:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(payload, dict) or payload.get("schema") != 1:
        raise ValueError("unsupported EFG computability classification schema")
    for field in (
        "declarations", "zero_modules", "protected_declarations",
        "external_data_interfaces", "execution_regressions",
    ):
        if not isinstance(payload.get(field), list):
            raise ValueError(f"classification requires a {field} list")
    return payload


def review_violations(
    payload: dict, entries: list[tuple[str, str]], modules: list[str]
) -> list[str]:
    """Review coverage supplements, but never replaces, the identity ratchet."""

    errors = []
    reviewed = {}
    treatments = {
        "analytic_definition": ("analytic_semantics", "retain_analytic"),
        "dependency_propagation": ("analytic_semantics", "retain_analytic"),
        "proof_generated_helper": ("proof_only", "retain_proof_helper"),
    }
    for record in payload["declarations"]:
        if not isinstance(record, dict) or not all(
            isinstance(record.get(key), str) and record[key].strip()
            for key in ("module", "declaration")
        ):
            errors.append("invalid classified declaration identity")
            continue
        identity = (record["module"], record["declaration"])
        label = " :: ".join(identity)
        if identity in reviewed:
            errors.append(f"duplicate classification: {label}")
        reviewed[identity] = record
        category = record.get("category")
        if (
            record.get("review_status") != "reviewed"
            or not isinstance(category, str)
            or treatments.get(category) !=
            (record.get("scope"), record.get("decision"))
        ):
            errors.append(f"unresolved executable operation or review: {label}")
        for field in (
            "reason", "runtime_role", "mathematical_guarantees", "elaborated_type",
        ):
            if not isinstance(record.get(field), str) or not record[field].strip():
                errors.append(f"unexplained {field}: {label}")
        dependencies = record.get("dependencies")
        if not isinstance(dependencies, list) or not all(
            isinstance(dep, str) and dep for dep in dependencies
        ):
            errors.append(f"missing dependency review: {label}")
        evidence = record.get("evidence")
        if not isinstance(evidence, list) or not evidence:
            errors.append(f"missing source evidence: {label}")
            continue
        for item in evidence:
            if not isinstance(item, dict):
                errors.append(f"invalid source evidence: {label}")
                continue
            if (
                item.get("path") != record["module"].replace(".", "/") + ".lean"
                or item.get("declaration") != record["declaration"]
                or "line" not in item or "end_line" not in item
            ):
                errors.append(f"source evidence does not identify its owner: {label}")
            error = source_evidence_error(item)
            if error:
                errors.append(f"{label}: {error}")

    current = set(entries)
    for identity in sorted(current - reviewed.keys()):
        errors.append(f"missing classification: {' :: '.join(identity)}")
    for identity in sorted(reviewed.keys() - current):
        errors.append(f"classification no longer in audit: {' :: '.join(identity)}")

    zero_modules = payload["zero_modules"]
    if not all(isinstance(module, str) for module in zero_modules):
        errors.append("invalid protected zero-module list")
        zero_modules = []
    if zero_modules != sorted(set(zero_modules)):
        errors.append("protected zero modules must be sorted and unique")
    for module in sorted(set(zero_modules) - set(modules)):
        errors.append(f"protected module missing from audit: {module}")
    protected = set()
    for identity in payload["protected_declarations"]:
        if not (
            isinstance(identity, list) and len(identity) == 2
            and all(isinstance(part, str) and part for part in identity)
        ):
            errors.append("invalid protected declaration identity")
            continue
        protected.add(tuple(identity))
    for identity in entries:
        if identity[0] in zero_modules or identity in protected:
            errors.append(f"protected executable boundary regressed: {' :: '.join(identity)}")

    for field in ("external_data_interfaces", "execution_regressions"):
        for record in payload[field]:
            if not isinstance(record, dict):
                errors.append(f"invalid {field} record")
                continue
            if field == "external_data_interfaces" and not all(
                isinstance(record.get(key), str) and record[key].strip()
                for key in ("module", "declaration")
            ):
                errors.append("external interface requires its exact identity")
            explanation = "requirements" if field == "external_data_interfaces" else "checks"
            if not isinstance(record.get(explanation), str) or not record[explanation].strip():
                errors.append(f"unexplained {field} record")
            evidence = record.get("evidence")
            if not isinstance(evidence, dict):
                errors.append(f"missing {field} source evidence")
            elif error := source_evidence_error(evidence):
                errors.append(error)
    return errors


def print_review_summary(payload: dict, entries: list[tuple[str, str]]) -> None:
    categories = Counter(record["category"] for record in payload["declarations"])
    unresolved = sum(
        record.get("scope") not in {"analytic_semantics", "proof_only"}
        or record.get("review_status") != "reviewed"
        for record in payload["declarations"]
    )
    print(
        f"Reviewed total: {len(entries)}; analytic definitions: "
        f"{categories['analytic_definition']}; analytic dependency propagation: "
        f"{categories['dependency_propagation']}; proof-generated helpers: "
        f"{categories['proof_generated_helper']}; unresolved executable/review items: "
        f"{unresolved}."
    )
    print(
        f"Protected boundaries: {len(payload['zero_modules'])} zero modules, "
        f"{len(payload['protected_declarations'])} cleared identities; "
        f"{len(payload['execution_regressions'])} execution regression sources."
    )
    print("External mathematical data (not law-construction algorithms):")
    for record in payload["external_data_interfaces"]:
        print(f"  {record['declaration']}: {record['requirements']}")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--classification",
        type=Path,
        default=DEFAULT_CLASSIFICATION,
        help="per-declaration review and protected execution boundary",
    )
    parser.add_argument(
        "--baseline",
        type=Path,
        default=DEFAULT_BASELINE,
        help="checked declaration-identity noncomputability ratchet",
    )
    parser.add_argument(
        "--update-baseline",
        action="store_true",
        help="remove reviewed declarations from the identity ratchet",
    )
    parser.add_argument(
        "--skip-build",
        action="store_true",
        help="audit existing oleans only after Lake verifies fresh dependency traces",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    baseline_path = args.baseline
    if not baseline_path.is_absolute():
        baseline_path = ROOT / baseline_path

    try:
        modules = audited_modules()
        entries = run_audit(modules, build=not args.skip_build)
        baseline = load_baseline(baseline_path)
    except (OSError, ValueError, json.JSONDecodeError, RuntimeError) as error:
        print(f"EFG computability check error: {error}", file=sys.stderr)
        return 2

    additions, removals = declaration_changes(baseline, entries)
    if additions:
        print("EFG noncomputability ratchet violations:")
        for module, declaration in additions:
            print(f"  new: {module} :: {declaration}")
        print(
            "Noncomputable declaration identities may only be removed. "
            "The baseline cannot be updated to admit additions or swaps.",
            file=sys.stderr,
        )
        return 1

    current = counts_by_module(entries)
    try:
        classification_path = args.classification
        if not classification_path.is_absolute():
            classification_path = ROOT / classification_path
        classification = load_classification(classification_path)
        errors = review_violations(classification, entries, modules)
    except (OSError, ValueError, json.JSONDecodeError) as error:
        print(f"EFG classification error: {error}", file=sys.stderr)
        return 2
    if errors:
        print("EFG computability review violations:", file=sys.stderr)
        for error in errors:
            print(f"  {error}", file=sys.stderr)
        return 1
    print_review_summary(classification, entries)
    if args.update_baseline:
        write_baseline(baseline_path, entries)
        print(
            "Wrote reduced EFG computability baseline: "
            f"{len(entries)} declarations in {len(current)} modules; "
            f"removed {len(removals)} identities."
        )
        return 0

    print(
        "EFG computability check: "
        f"{len(entries)} noncomputable declarations in "
        f"{len(current)} modules; removed {len(removals)} baseline identities."
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
