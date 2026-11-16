#!/usr/bin/env python3
"""Reject nonstandard axiom dependencies in finite-law and EFG declarations.

The audit traverses elaborated declarations, including generated and private
ones, and follows dependencies outside the audited modules. Only propext,
Quot.sound, and Classical.choice are allowed. In particular, native_decide
axioms and sorryAx do not qualify as kernel-checkable proof evidence here.
This checks proof dependencies, not whether a statement models its prose.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import re
import sys

if __package__:
    from . import check_efg_computability as environment
else:
    import check_efg_computability as environment


MARKER = "__EFG_AXIOM_DEPENDENCY__"
COUNTS_MARKER = "__EFG_AXIOM_COUNTS__"


def render_audit_source(modules: list[str]) -> str:
    """Emit a dependency audit using Lean's collectAxioms traversal."""

    imports = "\n".join(f"import {module}" for module in modules)
    names = ",\n    ".join(f"`{module}" for module in modules)
    return f"""{imports}
import Lean

open Lean Elab Command

elab "#audit_efg_axioms" : command => do
  let env ← getEnv
  let owners : Array Name := #[
    {names}
  ]
  let allowed : Array Name := #[`propext, `Quot.sound, `Classical.choice]
  let mut count := 0
  for (declaration, _) in env.constants.toList do
    if let some moduleIndex := env.getModuleIdxFor? declaration then
      let owner := (env.header.modules[moduleIndex]!).module
      if owners.contains owner then
        count := count + 1
        for axiomName in ← Lean.collectAxioms declaration do
          unless allowed.contains axiomName do
            liftIO <| IO.println
              s!"{MARKER}\\t{{owner}}\\t{{declaration}}\\t{{axiomName}}"
  liftIO <| IO.println s!"{COUNTS_MARKER}\\t{{owners.size}}\\t{{count}}"

#audit_efg_axioms
"""


def parse_audit_output(output: str) -> dict:
    """Require a complete audit summary; missing output must not pass."""

    summaries = re.findall(
        rf"^{COUNTS_MARKER}\t(\d+)\t(\d+)$", output, re.MULTILINE
    )
    if len(summaries) != 1 or not all(int(n) > 0 for n in summaries[0]):
        raise ValueError("missing or empty Lean axiom audit summary")
    violations = sorted(set(re.findall(
        rf"^{MARKER}\t([^\t\n]+)\t([^\t\n]+)\t([^\t\n]+)$",
        output, re.MULTILINE,
    )))
    return {
        "schema": 1,
        "module_count": int(summaries[0][0]),
        "declaration_count": int(summaries[0][1]),
        "violations": [
            {"module": owner, "declaration": declaration, "axiom": axiom}
            for owner, declaration, axiom in violations
        ],
    }


def run_audit(modules: list[str], build: bool) -> dict:
    environment.ensure_audit_build(modules, build)
    report = parse_audit_output(environment.query_environment(
        render_audit_source(modules), "EfgAxiomAudit_"
    ))
    if report["module_count"] != len(modules):
        raise ValueError("Lean axiom audit module count mismatch")
    return report


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--skip-build", action="store_true",
        help="require fresh existing artifacts instead of building them",
    )
    parser.add_argument("--json", type=Path, help="write the full audit result")
    args = parser.parse_args()
    try:
        report = run_audit(environment.audited_modules(), not args.skip_build)
        if args.json:
            args.json.write_text(json.dumps(report, indent=2) + "\n")
    except (OSError, RuntimeError, ValueError) as error:
        print(f"EFG axiom audit failed: {error}", file=sys.stderr)
        return 1
    for violation in report["violations"]:
        print(
            f"{violation['module']}: {violation['declaration']} "
            f"depends on forbidden axiom {violation['axiom']}",
            file=sys.stderr,
        )
    print(
        f"EFG axiom audit: {report['declaration_count']} declarations in "
        f"{report['module_count']} modules; "
        f"{len(report['violations'])} forbidden axiom dependencies"
    )
    return 1 if report["violations"] else 0


if __name__ == "__main__":
    sys.exit(main())
