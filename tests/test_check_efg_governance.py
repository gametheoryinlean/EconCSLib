import unittest
from pathlib import Path
from tempfile import TemporaryDirectory

from scripts.check_efg_governance import (
    EXPECTED_EFFECTIVE_AGGREGATE_IMPORTS,
    FROZEN_MINIMAL_CORE_STRUCTURES,
    controlled_carrier_universe_mapping_is_valid,
    documentation_link_errors,
    documented_large_efg_modules,
    frozen_structure_digest,
    large_efg_line_band,
    semantic_compatibility_source_is_valid,
)


class EFGGovernanceTest(unittest.TestCase):
    START = r"^structure Arena where\s*$"
    END = r"^namespace Arena\s*$"

    def test_minimal_core_compatibility_freeze_is_deferred(self):
        self.assertEqual(FROZEN_MINIMAL_CORE_STRUCTURES, {})

    def test_effective_probability_aggregates_keep_pure_and_analytic_split(self):
        self.assertEqual(
            EXPECTED_EFFECTIVE_AGGREGATE_IMPORTS[
                "EconCSLib.Math.Probability.Effective"
            ],
            {
                "EconCSLib.Math.Probability.Effective.Enclosure",
                "EconCSLib.Math.Probability.Effective.Core",
                "EconCSLib.Math.Probability.Effective.Uniform",
            },
        )
        self.assertEqual(
            EXPECTED_EFFECTIVE_AGGREGATE_IMPORTS[
                "EconCSLib.Math.Probability.Effective.Analytic"
            ],
            {
                "EconCSLib.Math.Probability.Effective",
                "EconCSLib.Math.Probability.Effective.Semantics",
                "EconCSLib.Math.Probability.Effective.UniformSemantics",
            },
        )

    def test_frozen_structure_digest_ignores_comments_and_whitespace(self):
        compact = """\
structure Arena where
  State : Type*
  Action : State → Type*
  next : (s : State) → Action s → State
namespace Arena
"""
        documented = """\
/-- Carrier documentation may evolve. -/
structure Arena where
  /-- State documentation may evolve too. -/
  State   : Type*

  Action : State → Type*
  next :
    (s : State) → Action s → State

namespace Arena
"""

        self.assertEqual(
            frozen_structure_digest(compact, self.START, self.END),
            frozen_structure_digest(documented, self.START, self.END),
        )

    def test_frozen_structure_digest_detects_field_change(self):
        frozen = """\
structure Arena where
  State : Type*
  Action : State → Type*
  next : (s : State) → Action s → State
namespace Arena
"""
        changed = """\
structure Arena where
  State : Type*
  Action : State → Type*
  next : (s : State) → Action s → State
  payoff : State → Nat
namespace Arena
"""

        self.assertNotEqual(
            frozen_structure_digest(frozen, self.START, self.END),
            frozen_structure_digest(changed, self.START, self.END),
        )

    def test_frozen_structure_digest_rejects_missing_boundary(self):
        source = "structure RenamedArena where\n  State : Type*\n"

        self.assertIsNone(
            frozen_structure_digest(source, self.START, self.END)
        )

    def test_controlled_carrier_universe_mapping_keeps_action_and_state_separate(
        self,
    ):
        valid = """\
structure ControlledDecisionGame (N : Type uN) where
  base : ControlledGame.{uN, uA, uS} N
  InfoState : N → Type uI
  InfoAction : (i : N) → InfoState i → Type uA
structure ControlledObservedGame (N : Type uN)
    extends ControlledDecisionGame.{uN, uA, uS, uI} N where
  Observation : N → Type uO
"""
        state_tied = """\
structure ControlledDecisionGame (N : Type uN) where
  base : ControlledGame.{uN, uS, uA} N
  InfoState : N → Type uI
  InfoAction : (i : N) → InfoState i → Type uA
structure ControlledObservedGame (N : Type uN)
    extends ControlledDecisionGame.{uN, uA, uS, uI} N where
  Observation : N → Type uO
"""
        observed_swapped = """\
structure ControlledDecisionGame (N : Type uN) where
  base : ControlledGame.{uN, uA, uS} N
  InfoState : N → Type uI
  InfoAction : (i : N) → InfoState i → Type uA
structure ControlledObservedGame (N : Type uN)
    extends ControlledDecisionGame.{uN, uS, uA, uI} N where
  Observation : N → Type uO
"""

        self.assertTrue(
            controlled_carrier_universe_mapping_is_valid(valid)
        )
        self.assertFalse(
            controlled_carrier_universe_mapping_is_valid(state_tied)
        )
        self.assertFalse(
            controlled_carrier_universe_mapping_is_valid(observed_swapped)
        )

    def test_large_efg_line_bands_are_stable(self):
        self.assertEqual(large_efg_line_band(800), "800-999")
        self.assertEqual(large_efg_line_band(999), "800-999")
        self.assertEqual(large_efg_line_band(1000), "1000-1199")
        self.assertEqual(large_efg_line_band(1200), "1200+")
        with self.assertRaises(ValueError):
            large_efg_line_band(799)

    def test_large_file_audit_parser_reports_duplicate_module(self):
        source = """\
| Module | Line band | Decision |
|---|---:|---|
| `EconCSLib.GameTheory.ExtensiveGame.Observed.Game` | `800-999` | Keep |
| `EconCSLib.GameTheory.ExtensiveGame.Observed.Game` | `800-999` | Keep |
"""

        rows, duplicates = documented_large_efg_modules(source)

        self.assertEqual(
            rows,
            {
                "EconCSLib.GameTheory.ExtensiveGame.Observed.Game":
                    "800-999"
            },
        )
        self.assertEqual(
            duplicates,
            {"EconCSLib.GameTheory.ExtensiveGame.Observed.Game"},
        )

    def test_documentation_link_check_accepts_existing_relative_target(self):
        with TemporaryDirectory() as directory:
            root = Path(directory)
            source = root / "source.md"
            target = root / "target.md"
            source.write_text("[target](target.md#section)\n", encoding="utf-8")
            target.write_text("# Section\n", encoding="utf-8")

            self.assertEqual(documentation_link_errors([source]), [])

    def test_documentation_link_check_rejects_missing_relative_target(self):
        with TemporaryDirectory() as directory:
            source = Path(directory) / "source.md"
            source.write_text("[missing](missing.md)\n", encoding="utf-8")

            self.assertEqual(
                documentation_link_errors([source]),
                [f"{source}: unresolved local Markdown link missing.md"],
            )

    def test_semantic_compatibility_bridge_requires_certificate_without_data(self):
        valid = """\
/-- The word `noncomputable def` in documentation is harmless. -/
def reindex (x : Nat) := x
theorem measure_compute_eq_semantics : reindex 0 = 0 := rfl
"""
        noncomputable_data = """\
noncomputable def interpretedValue : Nat := 0
theorem interpretedValue_eq_zero : interpretedValue = 0 := rfl
"""
        missing_equality = "def reindex (x : Nat) := x\n"
        represents = """\
theorem effective_law_represents_volume : True := by trivial
"""

        self.assertTrue(semantic_compatibility_source_is_valid(valid))
        self.assertTrue(semantic_compatibility_source_is_valid(represents))
        self.assertFalse(
            semantic_compatibility_source_is_valid(noncomputable_data)
        )
        self.assertFalse(
            semantic_compatibility_source_is_valid(missing_equality)
        )


if __name__ == "__main__":
    unittest.main()
