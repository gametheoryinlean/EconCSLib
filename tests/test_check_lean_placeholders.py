import tempfile
import unittest
from pathlib import Path

from scripts.check_lean_placeholders import check_file


class LeanPlaceholderCheckTest(unittest.TestCase):
    def check_source(self, source, path="EconCSLib/Foundation/Fixture.lean"):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            file = root / path
            file.parent.mkdir(parents=True, exist_ok=True)
            file.write_text(source + "\n", encoding="utf-8")
            return check_file(file, root)

    def test_rejects_placeholders_after_nested_interpolation_quotes(self):
        for placeholder in ("sorry", "by admit", "sorryAx String true"):
            with self.subTest(placeholder=placeholder):
                source = 'def bad : String := s!"{"hello" ++ (' + placeholder + ' : String)}"'
                self.assertTrue(self.check_source(source))

    def test_accepts_simple_interpolation(self):
        self.assertEqual(self.check_source('def s := s!"value: {(1 : Nat)}"'), [])

    def test_rejects_unsupported_interpolation_forms(self):
        sources = (
            'def s := s!"{"hello"}"',
            'def s := s!"{/- } -/ "hello" ++ (sorry : String)}"',
            'def s := s!"{(1 : Nat) -- }\n}"',
            'def s := s!"{«x}»}"',
            'def s := s!"{s!"{(1 : Nat)}"}"',
            'def s := s!"{r#"hello"#}"',
        )
        for source in sources:
            with self.subTest(source=source):
                self.assertTrue(self.check_source(source))

    def test_rejects_placeholders_in_simple_interpolation(self):
        for placeholder in ("sorry", "by admit", "sorryAx Nat true"):
            with self.subTest(placeholder=placeholder):
                source = 'def s := s!"{(' + placeholder + ' : Nat)}"'
                self.assertTrue(self.check_source(source))

    def test_accepts_nested_braces_and_character_literals(self):
        sources = (
            'def s := s!"{({ value := 1 }).value}"',
            "def s := s!\"{'}'} {'{'} {'\\\"'}\"",
            "def s := s!\"{x'}\"",
            "def s := s!\"{x'}' suffix\"",
            r'def s := s!"escaped quote: \" {(1 : Nat)}"',
            r'def s := s!"literal \{ \} {(1 : Nat)}"',
        )
        for source in sources:
            with self.subTest(source=source):
                self.assertEqual(self.check_source(source), [])

    def test_ordinary_literals_and_comments_do_not_hide_later_placeholders(self):
        prefixes = (
            'def s := "sorry admit sorryAx"',
            'def s := r#"quoted " sorry"#',
            '/- sorry /- admit -/ sorryAx -/',
            "def x' := 1",
        )
        for prefix in prefixes:
            with self.subTest(prefix=prefix):
                self.assertEqual(self.check_source(prefix), [])
                self.assertTrue(self.check_source(prefix + '\ntheorem bad : False := by sorry'))

    def test_scoped_answer_policy_is_preserved(self):
        path = "EconCSLib/OpenProblem/Fixture.lean"
        for result in ("answer(sorry) ↔ True", "(answer(sorry) : Nat) = answer(sorry)"):
            with self.subTest(result=result):
                source = "theorem question : " + result + " := by sorry"
                self.assertEqual(self.check_source(source, path), [])
                self.assertTrue(self.check_source(source))
                self.assertTrue(self.check_source(source + '\ntheorem bad : False := by sorry', path))

    def test_rejects_unresolved_parameters_and_concrete_answers_with_missing_proofs(self):
        for source in (
            "theorem q (x : answer(sorry)) : True := by sorry",
            "theorem q : answer(True) ↔ True := by sorry",
        ):
            with self.subTest(source=source):
                self.assertTrue(self.check_source(source, "EconCSLib/OpenProblem/Fixture.lean"))


if __name__ == "__main__":
    unittest.main()
