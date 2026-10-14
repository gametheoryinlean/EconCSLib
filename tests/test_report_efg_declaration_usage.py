import tempfile
import textwrap
import unittest
from pathlib import Path

from scripts.report_efg_declaration_usage import (
    declaration_leading_metadata,
    facade_contract_token_counts,
)


class EFGDeclarationUsageReportTest(unittest.TestCase):
    def test_declaration_metadata_recognizes_adjacent_docstring_and_simp(self):
        source = textwrap.dedent(
            """\
            /-- A documented normalization endpoint. -/
            @[simp, aesop safe]
            theorem documented : True := by trivial
            """
        )
        declaration_start = source.index("theorem")

        has_doc_comment, attributes = declaration_leading_metadata(
            source, declaration_start
        )

        self.assertTrue(has_doc_comment)
        self.assertEqual(attributes, ["simp, aesop safe"])

    def test_facade_evidence_excludes_imports_comments_and_negative_guards(self):
        source = textwrap.dedent(
            """\
            import EconCSLib.Example.NegativeOnly

            /- NegativeOnly is intentionally absent. -/
            #guard_msgs in
            #check NegativeOnly

            #check PositiveEndpoint

            example : PositiveExample := positiveWitness
            """
        )
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "ExampleImportBoundary.lean"
            path.write_text(source, encoding="utf-8")

            counts = facade_contract_token_counts([path])

        self.assertEqual(counts["NegativeOnly"], 0)
        self.assertEqual(counts["PositiveEndpoint"], 1)
        self.assertEqual(counts["PositiveExample"], 1)
        self.assertEqual(counts["positiveWitness"], 1)


if __name__ == "__main__":
    unittest.main()
