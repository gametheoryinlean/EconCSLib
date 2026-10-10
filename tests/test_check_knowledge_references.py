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

    def test_rejects_formalized_theorem_with_proof_gap(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            node = root / "gap.md"
            node.write_text(
                textwrap.dedent(
                    """\
                    ---
                    id: example.gap
                    title: Gap
                    kind: theorem
                    status: formalized
                    lean:
                      modules:
                        - Example
                      declarations:
                        - example_theorem
                    verification:
                      statement: accepted
                      proof: gap
                      alignment: aligned
                    ---

                    # Gap
                    """
                ),
                encoding="utf-8",
            )

            diagnostics = check_path(root)

            self.assertEqual(len(diagnostics), 1)
            self.assertIn("proof: accepted", diagnostics[0].text)

    def test_rejects_formalized_node_without_lean_mapping(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            node = root / "unmapped.md"
            node.write_text(
                textwrap.dedent(
                    """\
                    ---
                    id: example.unmapped
                    title: Unmapped
                    kind: definition
                    status: formalized
                    verification:
                      definition: accepted
                      proof: not_applicable
                      alignment: aligned
                    ---

                    # Unmapped
                    """
                ),
                encoding="utf-8",
            )

            diagnostics = check_path(root)

            self.assertEqual(len(diagnostics), 1)
            self.assertIn("Lean module/declaration mapping", diagnostics[0].text)

    def test_accepts_staged_theorem_with_proof_gap(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            node = root / "staged.md"
            node.write_text(
                textwrap.dedent(
                    """\
                    ---
                    id: example.staged
                    title: Staged
                    kind: theorem
                    status: staged
                    verification:
                      statement: accepted
                      proof: gap
                    ---

                    # Staged
                    """
                ),
                encoding="utf-8",
            )

            self.assertEqual(check_path(root), [])


if __name__ == "__main__":
    unittest.main()
