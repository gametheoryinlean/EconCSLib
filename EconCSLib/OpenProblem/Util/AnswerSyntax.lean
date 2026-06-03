/-
Copyright 2025 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

/-!
Syntax definitions for the EconCSLib open-problem `answer()` elaborator.

Adapted from `FormalConjectures.Util.Answer.Syntax` in
`google-deepmind/formal-conjectures`.
-/

public section

/-- Indicates where the answer is in an open-problem statement. -/
syntax (name := EconCSLib.OpenProblem.answer) "answer(" term ")" : term
