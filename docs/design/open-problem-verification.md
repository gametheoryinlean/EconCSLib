# Open-problem verification

## Build coverage

The dedicated `Open-problem verification` workflow builds every tracked Lean
file under `EconCSLib/OpenProblem/`, including supporting modules and shared
definitions. It runs on pull requests to `main`, pushes to `main`, and manual
dispatch, using the repository's Lean toolchain. New modules are discovered
automatically from the checkout being built.

Open problems remain opt-in. The existing library and example builds continue
separately; `EconCSLib.lean` must not import open-problem modules. A successful
build checks elaboration and imports, not the mathematical fidelity of a statement.

To run the same checks locally from a clean, staged checkout:

```bash
python3 scripts/check_lean_placeholders.py EconCSLib EconCSLib.lean
lake exe cache get
modules=()
while IFS= read -r -d '' file; do
  module=${file%.lean}
  modules+=("${module//\//.}")
done < <(git ls-files -z -- 'EconCSLib/OpenProblem/*.lean')
test "${#modules[@]}" -gt 0 && lake build "${modules[@]}"
```

## Answer placeholders

Named theorems and lemmas under `EconCSLib/OpenProblem/` may contain
`answer(sorry)` in their result types. Each problem determines its answer type:
a proposition, number, function, structure, or other mathematical data.
Multiple answer slots are allowed. For example:

```lean
theorem existenceQuestion : answer(sorry) ↔ P := by sorry
theorem quantitativeQuestion : IsCorrect (answer(sorry) : AnswerType) := by sorry
```

Only the same declaration may have the entire proof `:= by sorry`. Unresolved
answers are forbidden in declaration parameters, definitions, helper proofs,
and implementations. Concrete answers do not authorize unfinished proofs.
Ordinary `sorry`, `admit`, and direct `sorryAx` uses remain forbidden elsewhere.
The existing syntax quotation in `OpenProblem/Util/Answer.lean` has a narrow
exception. The answer elaborator is unchanged.

The checker recognizes identifier apostrophes, comments, and string literals.
It rejects interpolated expressions containing nested strings, quoted identifiers,
or comments rather than risk hiding executable placeholders. Use a named
intermediate value for these expressions.
It checks source syntax; mathematical correctness and transitive axiom
dependencies require review. Unresolved answers must not justify supporting
results or implementations.

## Dependencies and merge order

The following new-module dependencies were checked against PRs #40–65 on
2026-10-04. Existing library and Mathlib imports are omitted. Dependencies
include imports from supporting modules. There are no cross-problem imports.

| Prerequisite PRs | Dependent PRs |
|---|---|
| None | #40, #41, #42, #43, #46, #47, #48, #49, #50, #54, #63, #65 |
| #40 (`Complexity`) | #44, #53, #57, #58, #61, #62, #64 |
| #40 and #41 (`SharedConcepts`) | #45, #51, #52, #55, #56, #59, #60 |

1. Merge this verification prerequisite.
2. Review [#42](https://github.com/gametheoryinlean/EconCSLib/pull/42), EFX
   existence, as the template for statements, assumptions, and source correspondence.
   It requires neither #40 nor #41.
3. Review the other independent formulations in small batches.
4. Review #40's operation costs, encodings, and unproved equivalence claims before
   accepting dependent computational statements. Merge #41 when needed.
5. Review dependent formulations after their prerequisites. Keep #52
   (`PCPForPPAD`), #53 (`InformationalSubstitutesComplements`), and #58
   (`MeaningOfAGame`) as drafts pending mathematical review.

Update dependencies when imports change. Rebase each PR after its prerequisites
merge and run CI on that branch. Import independence does not establish
mathematical correctness. Maintainers can require the new CI job in branch
protection settings.
