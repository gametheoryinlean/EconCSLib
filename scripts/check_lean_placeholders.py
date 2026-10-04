#!/usr/bin/env python3
"""Conservative source-level check of the scoped open-answer policy.

Ordinary sorry/admit are forbidden. Only theorem/lemma result types under
EconCSLib/OpenProblem may contain answer(sorry); a bare `:= by sorry` is
allowed only for that same declaration. See docs/design/open-problem-verification.md.
This is a lexical policy check, not a Lean parser or a transitive axiom audit.
"""
from __future__ import annotations

import argparse
from pathlib import Path
import re
import sys
from typing import NamedTuple


class Token(NamedTuple):
    value: str
    start: int
    end: int
    depth: int


class LexError(ValueError):
    pass


# Apostrophes are identifier continuations, not the beginning of a string.
def ident_start(c: str) -> bool:
    return bool(c) and (c == '_' or c.isidentifier())


def ident_rest(c: str) -> bool:
    return bool(c) and (c in "_'." or c.isalnum() or ('a' + c).isidentifier()
                        or c in '₀₁₂₃₄₅₆₇₈₉′″')


CHAR = re.compile(r"'(?:[^'\\\n]|\\(?:[nrt0\\'\"]|x[0-9a-fA-F]{2}|u[0-9a-fA-F]{4}))'")
RAW = re.compile(r'r(#*)"')
OPEN = {'(': ')', '[': ']', '{': '}', '⟨': '⟩', '⦃': '⦄'}
CLOSE = set(OPEN.values())
# Command boundaries prevent an earlier answer from authorizing a later declaration.
BOUNDARIES = set('''theorem lemma def abbrev example instance structure inductive
class axiom axioms opaque constant constants syntax macro macro_rules elab elab_rules
initialize builtin_initialize namespace section end open export attribute variable
variables universe universes set_option notation infix infixl infixr prefix postfix
private protected public noncomputable unsafe partial meta local scoped mutual
termination_by decreasing_by where deriving include omit import module'''.split())


def tokenize(text: str) -> list[Token]:
    """Read identifiers and delimiters; comments/literals never erase later code."""
    tokens: list[Token] = []
    stack: list[str] = []
    i, n = 0, len(text)
    while i < n:
        start = i
        if text[i].isspace():
            i += 1
            continue
        if text.startswith('--', i):
            e = text.find('\n', i)
            i = n if e < 0 else e
            continue
        if text.startswith('/-', i):
            level = 1
            i += 2
            while i < n and level:
                if text.startswith('/-', i):
                    level += 1; i += 2
                elif text.startswith('-/', i):
                    level -= 1; i += 2
                else:
                    i += 1
            if level:
                raise LexError(f'unterminated block comment at offset {start}')
            continue
        raw = RAW.match(text, i)
        if raw:
            closing = '"' + raw.group(1)
            e = text.find(closing, raw.end())
            if e < 0:
                raise LexError(f'unterminated raw string at offset {start}')
            i = e + len(closing)
            value = '<literal>'
        elif text[i] == '"':
            i += 1
            while i < n:
                if text[i] == '\\':
                    i += 2
                elif text[i] == '"':
                    i += 1
                    break
                else:
                    i += 1
            else:
                raise LexError(f'unterminated string at offset {start}')
            # Do not silently hide executable interpolation behind string stripping.
            # Complex interpolation is deliberately fail-closed for placeholder words.
            if (tokens and tokens[-1].value == '!' and
                    re.search(r'\b(?:sorry|admit|sorryAx)\b', text[start:i])):
                raise LexError('placeholder-like text in an interpolated string: '
                               'use an ordinary string for literal text; '
                               'executable placeholders are forbidden')
            value = '<literal>'
        elif text[i] == '«':
            e = text.find('»', i + 1)
            if e < 0:
                raise LexError(f'unterminated quoted identifier at offset {start}')
            i = e + 1
            value = text[start:i]  # Not the reserved token `sorry`.
        elif text[i] == "'" and (char := CHAR.match(text, i)):
            i = char.end()
            value = '<literal>'
        elif ident_start(text[i]):
            i += 1
            while i < n and ident_rest(text[i]):
                i += 1
            value = text[start:i]
        elif text.startswith(':=', i):
            value = ':='; i += 2
        else:
            value = text[i]; i += 1
        if value in CLOSE:
            if stack and stack[-1] == value:
                stack.pop()
            else:
                # Lean will diagnose invalid syntax. Do not mask the rest of the file.
                stack.clear()
        depth = len(stack)
        tokens.append(Token(value, start, i, depth))
        if value in OPEN:
            stack.append(OPEN[value])
    return tokens


def strip_comments_and_strings(text: str) -> str:
    """Compatibility helper; preserves offsets, newlines and apostrophes."""
    out = ['\n' if c == '\n' else ' ' for c in text]
    for token in tokenize(text):
        if token.value != '<literal>':
            out[token.start:token.end] = text[token.start:token.end]
    return ''.join(out)


def line_col(text: str, pos: int) -> tuple[int, int]:
    return text.count('\n', 0, pos) + 1, pos - text.rfind('\n', 0, pos)


def is_under_open_problem(relative: Path) -> bool:
    return relative.parts[:2] == ('EconCSLib', 'OpenProblem')


def quotation_positions(tokens: list[Token]) -> set[int]:
    """Token indices inside parenthesized syntax quotations, not executable terms."""
    quoted: set[int] = set()
    for i in range(1, len(tokens)):
        if tokens[i - 1].value != '`' or tokens[i].value != '(':
            continue
        depth = tokens[i].depth
        stop = next((j for j in range(i + 1, len(tokens))
                     if tokens[j].value == ')' and tokens[j].depth == depth),
                    len(tokens) - 1)
        quoted.update(range(i, stop + 1))
    return quoted


def command_boundary(tokens: list[Token], i: int) -> bool:
    """Recognize declaration boundaries without treating @Eq or #[...] as commands."""
    token = tokens[i]
    if token.depth != 0:
        return False
    if token.value in BOUNDARIES:
        return True
    following = tokens[i + 1].value if i + 1 < len(tokens) else None
    # Hash commands differ from array literals; @[...] introduces attributes,
    # whereas @ applied to an identifier is an ordinary explicit application.
    return ((token.value == '#' and following != '[')
            or (token.value == '@' and following == '['))


def allowed_positions(tokens: list[Token], relative: Path) -> set[int]:
    allowed: set[int] = set()
    if not is_under_open_problem(relative):
        return allowed
    values = [t.value for t in tokens]
    quoted = quotation_positions(tokens)
    starts = [i for i in range(len(tokens))
              if i not in quoted and command_boundary(tokens, i)]
    stops = starts[1:] + [len(tokens)]
    for start, stop in zip(starts, stops):
        if values[start] not in {'theorem', 'lemma'}:
            continue
        assign = next((i for i in range(start + 1, stop)
                       if values[i] == ':=' and tokens[i].depth == 0), None)
        if assign is None:
            continue
        colon = next((i for i in range(start + 1, assign)
                      if values[i] == ':' and tokens[i].depth == 0), None)
        if colon is None:
            continue
        slots = [i + 2 for i in range(colon + 1, assign - 3)
                 if i not in quoted
                 and values[i - 1] != '`'
                 and values[i:i + 4] == ['answer', '(', 'sorry', ')']]
        allowed.update(tokens[i].start for i in slots)
        if slots and values[assign + 1:stop] == ['by', 'sorry']:
            allowed.add(tokens[assign + 2].start)
    # A syntax comparison in the repository's elaborator, not a proof hole.
    if relative.as_posix() == 'EconCSLib/OpenProblem/Util/Answer.lean':
        for i in range(4, len(tokens) - 1):
            if (values[i] == 'sorry' and values[i - 4:i] == ['`', '(', 'term', '|']
                    and values[i + 1] == ')'):
                allowed.add(tokens[i].start)
    return allowed


def check_file(path: Path, root: Path) -> list[str]:
    try:
        relative = path.resolve().relative_to(root.resolve())
    except ValueError:
        return [f'{path}: source lies outside the repository root']
    try:
        text = path.read_text(encoding='utf-8')
        tokens = tokenize(text)
    except (OSError, UnicodeError, LexError) as exc:
        return [f'{relative}: {exc}']
    allowed = allowed_positions(tokens, relative)
    errors = []
    for token in tokens:
        # Lean permits escaped name components and explicit universe suffixes.
        # The lexer emits `sorryAx.` before `{...}` and preserves «sorryAx».
        name = token.value.removeprefix('«').removesuffix('»').rstrip('.').rsplit('.', 1)[-1]
        forbidden = (token.value in {'sorry', 'admit'} or name == 'sorryAx')
        if not forbidden:
            continue
        if token.value == 'sorry' and token.start in allowed:
            continue
        line, col = line_col(text, token.start)
        errors.append(f'{relative}:{line}:{col}: disallowed {token.value}; '
                      'only answer(sorry) in an open theorem/lemma result type and '
                      'that declaration\'s bare := by sorry are permitted')
    return errors


def iter_lean_files(paths: list[Path]) -> list[Path]:
    files: set[Path] = set()
    for path in paths:
        if not path.exists():
            raise ValueError(f'path does not exist: {path}')
        if path.is_symlink():
            raise ValueError(f'symlink is not an accepted source path: {path}')
        if path.is_file() and path.suffix == '.lean':
            files.add(path.resolve())
        elif path.is_dir():
            # rglob does not descend into symlink directories. Reject them
            # explicitly instead of silently treating their sources as covered.
            for candidate in path.rglob('*'):
                if candidate.is_symlink():
                    raise ValueError(f'symlink is not an accepted source: {candidate}')
                if candidate.is_file() and candidate.suffix == '.lean':
                    files.add(candidate.resolve())
        else:
            raise ValueError(f'not a Lean file or directory: {path}')
    if not files:
        raise ValueError('no Lean files found; refusing an empty successful check')
    return sorted(files)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('paths', nargs='*', default=['EconCSLib', 'EconCSLib.lean'])
    args = parser.parse_args()
    root = Path.cwd().resolve()
    try:
        files = iter_lean_files([Path(p) for p in args.paths])
    except ValueError as exc:
        print(exc, file=sys.stderr)
        return 2
    errors = [error for p in files for error in check_file(p, root)]
    if errors:
        print('\n'.join(errors))
        return 1
    print(f'Placeholder policy passed for {len(files)} Lean files.')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
