import io
import json
import os
import sys
import unittest
from contextlib import contextmanager, redirect_stderr, redirect_stdout
from pathlib import Path
from tempfile import TemporaryDirectory
from unittest.mock import patch

from scripts.check_efg_computability import (
    MARKER,
    DEFAULT_CLASSIFICATION,
    ROOT,
    audited_modules,
    declaration_changes,
    load_baseline,
    main,
    module_name,
    parse_audit_output,
    render_audit_source,
    review_violations,
    run_audit,
    run_command,
    write_baseline,
)


@contextmanager
def lean_fixture_project():
    """Use real Lake traces without adding audit fixtures to the library."""

    with TemporaryDirectory() as directory:
        project = Path(directory)
        (project / "lean-toolchain").write_text((ROOT / "lean-toolchain").read_text())
        (project / "lakefile.toml").write_text(
            'name = "efg_audit_fixture"\n'
            'version = "0.1.0"\n\n[[lean_lib]]\nname = "Fixture"\n'
        )
        (project / "Fixture.lean").write_text(
            (ROOT / "tests/fixtures/EfgComputabilityNoncomputable.lean").read_text()
        )
        with patch("scripts.check_efg_computability.ROOT", project):
            yield project


class EFGComputabilityTest(unittest.TestCase):
    def test_module_name_uses_repository_relative_import_path(self):
        path = Path(
            "EconCSLib/GameTheory/ExtensiveGame/Execution/Objective.lean"
        ).resolve()

        self.assertEqual(
            module_name(path),
            "EconCSLib.GameTheory.ExtensiveGame.Execution.Objective",
        )

    def test_audit_parser_ignores_unmarked_lean_output(self):
        output = (
            "build warning\n"
            f"{MARKER}\tEconCSLib.One\tArena.first\n"
            "other output\n"
            f"{MARKER}\tEconCSLib.Two\tGame.second\n"
        )

        self.assertEqual(
            parse_audit_output(output),
            [
                ("EconCSLib.One", "Arena.first"),
                ("EconCSLib.Two", "Game.second"),
            ],
        )

    def test_ratchet_accepts_a_strict_identity_subset(self):
        baseline = [
            ("EconCSLib.One", "Arena.first"),
            ("EconCSLib.One", "Arena.second"),
            ("EconCSLib.Two", "Game.third"),
        ]

        self.assertEqual(
            declaration_changes(
                baseline,
                [
                    ("EconCSLib.One", "Arena.first"),
                    ("EconCSLib.Two", "Game.third"),
                ],
            ),
            ([], [("EconCSLib.One", "Arena.second")]),
        )

    def test_ratchet_rejects_same_count_declaration_replacement(self):
        baseline = [
            ("EconCSLib.One", "Arena.first"),
            ("EconCSLib.One", "Arena.second"),
        ]

        self.assertEqual(
            declaration_changes(
                baseline,
                [
                    ("EconCSLib.One", "Arena.first"),
                    ("EconCSLib.One", "Arena.replacement"),
                ],
            ),
            (
                [("EconCSLib.One", "Arena.replacement")],
                [("EconCSLib.One", "Arena.second")],
            ),
        )

    def test_ratchet_rejects_declaration_in_new_module(self):
        self.assertEqual(
            declaration_changes(
                [("EconCSLib.One", "Arena.first")],
                [
                    ("EconCSLib.New", "Game.newDeclaration"),
                    ("EconCSLib.One", "Arena.first"),
                ],
            ),
            ([("EconCSLib.New", "Game.newDeclaration")], []),
        )

    def test_update_baseline_refuses_growth_and_preserves_file(self):
        baseline = [("EconCSLib.One", "Arena.first")]
        current = baseline + [("EconCSLib.One", "Arena.second")]
        with TemporaryDirectory() as directory:
            baseline_path = Path(directory) / "baseline.json"
            write_baseline(baseline_path, baseline)
            argv = [
                "check_efg_computability.py",
                "--baseline",
                str(baseline_path),
                "--update-baseline",
                "--skip-build",
            ]
            with (
                patch.object(sys, "argv", argv),
                patch(
                    "scripts.check_efg_computability.audited_modules",
                    return_value=["EconCSLib.One"],
                ),
                patch(
                    "scripts.check_efg_computability.run_audit",
                    return_value=current,
                ),
                redirect_stdout(io.StringIO()),
                redirect_stderr(io.StringIO()),
            ):
                self.assertEqual(main(), 1)

            self.assertEqual(load_baseline(baseline_path), baseline)

    def test_every_extensive_game_example_is_audited(self):
        modules = set(audited_modules())
        self.assertIn(
            "EconCSLib.Examples.ExtensiveGame.InfiniteSPEBoundary",
            modules,
        )
        self.assertIn(
            "EconCSLib.Examples.ExtensiveGame.RootImportBoundary",
            modules,
        )

    def test_effective_probability_owners_and_semantics_are_audited(self):
        modules = set(audited_modules())
        effective = {
            module
            for module in modules
            if module == "EconCSLib.Math.Probability.Effective"
            or module.startswith("EconCSLib.Math.Probability.Effective.")
        }
        self.assertEqual(
            effective,
            {
                "EconCSLib.Math.Probability.Effective",
                "EconCSLib.Math.Probability.Effective.Analytic",
                "EconCSLib.Math.Probability.Effective.Core",
                "EconCSLib.Math.Probability.Effective.Enclosure",
                "EconCSLib.Math.Probability.Effective.Semantics",
                "EconCSLib.Math.Probability.Effective.Uniform",
                "EconCSLib.Math.Probability.Effective.UniformSemantics",
            },
        )

    def test_effective_review_matches_per_declaration_metadata(self):
        payload = json.loads(DEFAULT_CLASSIFICATION.read_text(encoding="utf-8"))
        review = payload["effective_implementation_review"]
        recorded = {
            record["implementation_search"]["id"]
            for record in payload["declarations"]
            if "effective_implementation" in record
        }
        summarized = set(review["pre_a19_original_identities"]) | set(
            review["a19_original_identities"]
        )

        self.assertEqual(recorded, summarized)
        self.assertEqual(review["covered_original_identities"], len(recorded))
        self.assertEqual(review["audited_modules"], len(audited_modules()))
        self.assertEqual(review["new_noncomputable_declarations"], 0)

    def test_generated_audit_uses_lean_environment_attribute(self):
        source = render_audit_source(["EconCSLib.Example"])

        self.assertIn("import EconCSLib.Example", source)
        self.assertIn("Lean.isNoncomputable env declaration", source)
        self.assertIn("env.getModuleIdxFor? declaration", source)

    def test_lean_environment_reports_fixture_noncomputable_declaration(self):
        with lean_fixture_project() as project:
            self.assertIn(
                (
                    "Fixture",
                    "EFGComputabilityNoncomputable.selectedNat",
                ),
                run_audit(["Fixture"], build=True),
            )
            with TemporaryDirectory() as directory:
                baseline_path = Path(directory) / "baseline.json"
                write_baseline(baseline_path, [])
                argv = [
                    "check_efg_computability.py",
                    "--baseline",
                    str(baseline_path),
                    "--skip-build",
                ]
                output = io.StringIO()
                with (
                    patch.object(sys, "argv", argv),
                    patch(
                        "scripts.check_efg_computability.audited_modules",
                        return_value=["Fixture"],
                    ),
                    redirect_stdout(output),
                    redirect_stderr(output),
                ):
                    self.assertEqual(main(), 1)
                self.assertIn(
                    "new: Fixture :: "
                    "EFGComputabilityNoncomputable.selectedNat",
                    output.getvalue(),
                )

            # A data producer cannot hide a noncomputable dependency by omitting
            # its own marker, even when the dependency came from a proof helper.
            wrapper = project / "Executable.lean"
            wrapper.write_text(
                "import Fixture\n"
                "def protectedRun : Nat := EFGComputabilityNoncomputable.selectedNat\n"
            )
            result = run_command(["lake", "env", "lean", str(wrapper)])
            self.assertNotEqual(result.returncode, 0, result.stdout)
            self.assertIn("failed to compile definition", result.stdout)
            self.assertIn("selectedNat", result.stdout)

    def test_skip_build_rejects_changed_dependency_even_with_preserved_mtime(self):
        with lean_fixture_project() as project:
            dependency = project / "Fixture/Dependency.lean"
            dependency.parent.mkdir()
            dependency.write_text("def dependencyValue : Nat := 0\n")
            (project / "Fixture.lean").write_text(
                "import Fixture.Dependency\ndef fixtureValue : Nat := dependencyValue\n"
            )
            self.assertEqual(run_audit(["Fixture"], build=True), [])
            old = dependency.stat()
            dependency.write_text("def dependencyValue : Nat := 1\n")
            os.utime(dependency, ns=(old.st_atime_ns, old.st_mtime_ns))
            with redirect_stderr(io.StringIO()), self.assertRaisesRegex(
                RuntimeError, "stale or missing"
            ):
                run_audit(["Fixture"], build=False)
            self.assertEqual(run_audit(["Fixture"], build=True), [])
            (project / ".lake/build/lib/lean/Fixture.olean").unlink()
            with redirect_stderr(io.StringIO()), self.assertRaisesRegex(
                RuntimeError, "stale or missing"
            ):
                run_audit(["Fixture"], build=False)

    def reviewed_example(self):
        """Use a real reviewed analytic declaration and its real source evidence."""

        ledger = json.loads(DEFAULT_CLASSIFICATION.read_text())
        record = next(
            item for item in ledger["declarations"]
            if item["category"] == "analytic_definition"
        )
        payload = {
            "schema": 1, "declarations": [record], "zero_modules": [],
            "protected_declarations": [], "external_data_interfaces": [],
            "execution_regressions": [],
        }
        return payload, (record["module"], record["declaration"])

    def run_review(self, payload, identity):
        with TemporaryDirectory() as directory:
            baseline = Path(directory) / "baseline.json"
            classification = Path(directory) / "classification.json"
            write_baseline(baseline, [identity])
            classification.write_text(json.dumps(payload))
            output = io.StringIO()
            with (
                patch.object(sys, "argv", [
                    "check_efg_computability.py", "--baseline", str(baseline),
                    "--classification", str(classification), "--skip-build",
                ]),
                patch("scripts.check_efg_computability.audited_modules",
                      return_value=[identity[0]]),
                patch("scripts.check_efg_computability.run_audit",
                      return_value=[identity]),
                redirect_stdout(output), redirect_stderr(output),
            ):
                return main(), output.getvalue()

    def test_missing_review_fails_even_for_an_existing_baseline_identity(self):
        payload, identity = self.reviewed_example()
        payload["declarations"] = []
        result, output = self.run_review(payload, identity)
        self.assertEqual(result, 1, output)
        self.assertIn("missing classification", output)

    def test_retained_analytic_declaration_is_still_counted(self):
        payload, identity = self.reviewed_example()
        result, output = self.run_review(payload, identity)
        self.assertEqual(result, 0, output)
        self.assertIn("1 noncomputable declarations", output)
        self.assertIn("analytic definitions: 1", output)

    def test_classification_cannot_readmit_a_cleared_baseline_identity(self):
        payload, identity = self.reviewed_example()
        payload["protected_declarations"] = [list(identity)]
        result, output = self.run_review(payload, identity)
        self.assertEqual(result, 1, output)
        self.assertIn("protected executable boundary regressed", output)

    def test_changed_reviewed_body_requires_new_evidence(self):
        payload, identity = self.reviewed_example()
        evidence = payload["declarations"][0]["evidence"][0]
        relative = Path(evidence["path"])
        original = (ROOT / relative).read_text()
        with TemporaryDirectory() as directory:
            project = Path(directory)
            source = project / relative
            source.parent.mkdir(parents=True)
            source.write_text(original)
            with patch("scripts.check_efg_computability.ROOT", project):
                self.assertEqual(review_violations(payload, [identity], [identity[0]]), [])
                lines = original.splitlines()
                lines[evidence["end_line"] - 1] += " -- changed implementation"
                source.write_text("\n".join(lines) + "\n")
                errors = review_violations(payload, [identity], [identity[0]])
                self.assertTrue(any("changed review evidence" in error for error in errors))


if __name__ == "__main__":
    unittest.main()
