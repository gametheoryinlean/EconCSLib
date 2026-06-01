import tempfile
import textwrap
import unittest
from pathlib import Path

from scripts.check_knowledge_references import check_path


class KnowledgeReferencesCheckTest(unittest.TestCase):
    def test_rejects_github_links_inside_references_only(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            node = root / "bad.md"
            node.write_text(
                textwrap.dedent(
                    """\
                    # Bad Node

                    ## References

                    - [EconCSLib pull request 27, blueprint/src/content.tex] Migrated from the old blueprint.

                    ## Provenance

                    - This section may mention https://github.com/example/project/pull/27.
                    """
                ),
                encoding="utf-8",
            )

            diagnostics = check_path(root)

            self.assertEqual(len(diagnostics), 1)
            self.assertEqual(diagnostics[0].path, node)

    def test_accepts_scholarly_references_and_provenance_github_links(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            node = root / "good.md"
            node.write_text(
                textwrap.dedent(
                    """\
                    # Good Node

                    ## References

                    - [MFoGT, Chapter 9] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*.

                    ## Provenance

                    - Migrated from https://github.com/example/project/pull/27.
                    """
                ),
                encoding="utf-8",
            )

            self.assertEqual(check_path(root), [])


if __name__ == "__main__":
    unittest.main()
