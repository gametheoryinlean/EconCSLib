/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.OpenProblem.New.Complexity.WordRAM.Search



section

/-!
# Fixed executable certificate checkers

Acceptance is a literal output bit of the original interpreter. Each application
separately states soundness and completeness for its mathematical relation.
-/
namespace EconCSLib.OpenProblem.New.WordRAM.Certificates
open FiniteData

/-- One finite checker with a uniform polynomial acceptance-time bound. -/
structure Verifier where
  model : Model
  program : Program
  coefficient : ℕ
  exponent : ℕ

/-- Acceptance must occur in a bounded actual execution on the framed input/certificate
pair. Nonaccepting inputs may reject or fail to halt. -/
def Verifier.Accepts (verifier : Verifier) (input certificate : Code) : Prop :=
  ∃ fuel,
    let framed := pairCode input certificate
    let result := Search.execution verifier.model verifier.program fuel framed
    result.termination = .halted (words [true]) ∧
    result.cost ≤ verifier.coefficient *
      (bitSize verifier.model framed + 1) ^ verifier.exponent

end EconCSLib.OpenProblem.New.WordRAM.Certificates

end
