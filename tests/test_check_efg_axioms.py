import unittest

from scripts.check_efg_axioms import parse_audit_output, run_audit
from tests.test_check_efg_computability import lean_fixture_project


class EFGAxiomTest(unittest.TestCase):
    def test_missing_audit_summary_fails_closed(self):
        with self.assertRaises(ValueError):
            parse_audit_output("Lean warning\n")

    def test_standard_classical_proof_is_allowed(self):
        with lean_fixture_project() as project:
            (project / "Fixture.lean").write_text(
                "theorem excludedMiddle (p : Prop) : p ∨ ¬p := Classical.em p\n"
            )
            report = run_audit(["Fixture"], build=True)
            self.assertEqual(report["module_count"], 1)
            self.assertGreater(report["declaration_count"], 0)
            self.assertEqual(report["violations"], [])

    def test_transitive_external_axiom_and_native_proof_are_rejected(self):
        with lean_fixture_project() as project:
            (project / "Fixture").mkdir()
            (project / "Fixture/Assumption.lean").write_text(
                "axiom extraAssumption : False\n"
                "theorem externalWrapper : False := extraAssumption\n"
            )
            (project / "Fixture.lean").write_text(
                "import Fixture.Assumption\n"
                "import Std.Tactic\n"
                "namespace AxiomFixture\n"
                "private theorem hidden : False := externalWrapper\n"
                "theorem exported : 0 = 1 := hidden.elim\n"
                "theorem computed : (1 : Nat) + 1 = 2 := by native_decide\n"
                "theorem downstream : (1 : Nat) + 1 = 2 := computed\n"
                "theorem missing : False := by sorry\n"
                "end AxiomFixture\n"
            )
            violations = run_audit(["Fixture"], build=True)["violations"]
            exported = next(v for v in violations
                            if v["declaration"] == "AxiomFixture.exported")
            self.assertEqual(exported["axiom"], "extraAssumption")
            self.assertTrue(any("hidden" in v["declaration"] for v in violations))
            downstream = next(v for v in violations
                              if v["declaration"] == "AxiomFixture.downstream")
            self.assertIn("native_decide", downstream["axiom"])
            self.assertTrue(any(v["declaration"] == "AxiomFixture.missing"
                                and v["axiom"] == "sorryAx" for v in violations))
            self.assertTrue(all(v["module"] == "Fixture" for v in violations))


if __name__ == "__main__":
    unittest.main()
