#!/usr/bin/env python3
"""Check Lean source files for disallowed placeholders.

Ordinary `sorry` and `admit` are forbidden in EconCSLib Lean source. Open
problem modules may use the upstream-style pattern

    theorem problemName : answer(sorry) ↔ P := by
      sorry

under `EconCSLib/OpenProblem/`. The answer elaborator implementation itself has
one syntax quotation mentioning `sorry`; this script allows that exact use.
"""

from __future__ import annotations

import argparse
import pathlib
import re
import sys


TOKEN_RE = re.compile(r"\b(sorry|admit)\b")


def strip_comments_and_strings(text: str) -> str:
    """Return text with Lean comments and strings replaced by spaces."""

    out: list[str] = []
    i = 0
    block_depth = 0
    in_line_comment = False
    in_string = False
    in_char = False

    while i < len(text):
        c = text[i]
        n = text[i + 1] if i + 1 < len(text) else ""

        if in_line_comment:
            if c == "\n":
                in_line_comment = False
                out.append(c)
            else:
                out.append(" ")
            i += 1
            continue

        if block_depth:
            if c == "/" and n == "-":
                block_depth += 1
                out.extend("  ")
                i += 2
            elif c == "-" and n == "/":
                block_depth -= 1
                out.extend("  ")
                i += 2
            else:
                out.append("\n" if c == "\n" else " ")
                i += 1
            continue

        if in_string:
            if c == "\\" and n:
                out.extend("  ")
                i += 2
            elif c == '"':
                in_string = False
                out.append(" ")
                i += 1
            else:
                out.append("\n" if c == "\n" else " ")
                i += 1
            continue

        if in_char:
            if c == "\\" and n:
                out.extend("  ")
                i += 2
            elif c == "'":
                in_char = False
                out.append(" ")
                i += 1
            else:
                out.append("\n" if c == "\n" else " ")
                i += 1
            continue

        if c == "-" and n == "-":
            in_line_comment = True
            out.extend("  ")
            i += 2
        elif c == "/" and n == "-":
            block_depth = 1
            out.extend("  ")
            i += 2
        elif c == '"':
            in_string = True
            out.append(" ")
            i += 1
        elif c == "'":
            in_char = True
            out.append(" ")
            i += 1
        else:
            out.append(c)
            i += 1

    return "".join(out)


def line_col(text: str, pos: int) -> tuple[int, int]:
    line = text.count("\n", 0, pos) + 1
    line_start = text.rfind("\n", 0, pos) + 1
    return line, pos - line_start + 1


def is_under_open_problem(path: pathlib.Path) -> bool:
    parts = path.parts
    return "EconCSLib" in parts and "OpenProblem" in parts


def is_answer_sorry(code: str, pos: int) -> bool:
    return code[:pos].rstrip().endswith("answer(")


def is_answer_utility_quote(path: pathlib.Path, code: str, pos: int) -> bool:
    return (
        path.as_posix().endswith("EconCSLib/OpenProblem/Util/Answer.lean")
        and code[:pos].rstrip().endswith("`(term|")
    )


def is_open_problem_proof_sorry(code: str, pos: int) -> bool:
    prefix = code[:pos].rstrip()
    if not prefix.endswith(":= by"):
        return False

    theorem_pos = max(prefix.rfind("\ntheorem "), prefix.rfind("\nlemma "))
    if prefix.startswith("theorem ") or prefix.startswith("lemma "):
        theorem_pos = 0
    if theorem_pos < 0:
        return False

    decl_prefix = prefix[theorem_pos:]
    return re.search(r"\banswer\s*\(\s*sorry\s*\)\s*↔", decl_prefix) is not None


def check_file(path: pathlib.Path, root: pathlib.Path) -> list[str]:
    text = path.read_text(encoding="utf-8")
    code = strip_comments_and_strings(text)
    errors: list[str] = []

    for match in TOKEN_RE.finditer(code):
        token = match.group(1)
        pos = match.start()
        rel = path.relative_to(root)
        loc = line_col(text, pos)

        if token == "admit":
            errors.append(f"{rel}:{loc[0]}:{loc[1]}: disallowed admit")
            continue

        if not is_under_open_problem(path):
            errors.append(f"{rel}:{loc[0]}:{loc[1]}: disallowed sorry outside OpenProblem")
            continue

        if (
            is_answer_sorry(code, pos)
            or is_answer_utility_quote(path, code, pos)
            or is_open_problem_proof_sorry(code, pos)
        ):
            continue

        errors.append(
            f"{rel}:{loc[0]}:{loc[1]}: disallowed sorry; use only "
            "`answer(sorry)` statements and their direct `by sorry` proofs"
        )

    return errors


def iter_lean_files(paths: list[pathlib.Path]) -> list[pathlib.Path]:
    files: list[pathlib.Path] = []
    for path in paths:
        if path.is_file() and path.suffix == ".lean":
            files.append(path)
        elif path.is_dir():
            files.extend(sorted(path.rglob("*.lean")))
    return files


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("paths", nargs="*", default=["EconCSLib"])
    args = parser.parse_args()

    root = pathlib.Path.cwd()
    files = iter_lean_files([pathlib.Path(p) for p in args.paths])
    errors: list[str] = []
    for path in files:
        errors.extend(check_file(path.resolve(), root.resolve()))

    if errors:
        print("\n".join(errors))
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
