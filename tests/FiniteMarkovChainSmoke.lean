/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.Examples.FiniteMarkovChain

/-!
# Executable finite absorbing-chain regressions

Evaluate the main-library algorithms on the worked models. Guards check exact
rational outputs and failure branches; proof declarations use the ordinary
kernel-checked examples and the separate declaration audit.
-/

open FiniteMarkovChain Examples.FiniteMarkovChain

section Geometric

#guard geometric.autoCheck
#guard geometric.autoBound = 1 / 4
#guard geometric.autoSolve.map (fun vt => (vt.1 (.inl 0), vt.2 (.inl 0))) = .ok (6, 2)
#guard (geometric.run 0 0).mass (.inl 0) = 1
#guard (geometric.run 2 0).mass (.inl 0) = 1 / 4
#guard (geometric.run 2 0).mass (.inr (0, 0)) = 1 / 2
#guard (geometric.run 2 0).mass (.inr (1, 0)) = 1 / 4
#guard (geometric.run 2 0).mass (.inr (2, 0)) = 0
#guard (geometric.solve 0 (1 / 2) matches .error .absorptionBound)
#guard (geometric.solve 1 1 matches .error .absorptionBound)
#guard (geometric.solve 1 (-1) matches .error .absorptionBound)
#guard (Chain.solveLinear (0 : Matrix (Fin 1) (Fin 1) ℚ) (fun _ => 1)).isNone

end Geometric

section MultipleStates

#guard twoStage.autoCheck
#guard twoStage.autoSolve.map (fun vt => (vt.1 (.inl 0), vt.2 (.inl 0))) = .ok (2, 3)
#guard twoStage.autoSolve.map (fun vt => (vt.1 (.inl 1), vt.2 (.inl 1))) = .ok (2, 2)
#guard twoStage.autoSolve.map (fun vt => (vt.1 (.inr 0), vt.2 (.inr 0))) = .ok (-2, 0)
#guard (twoStage.run 1 0).mass (.inl 1) = 1
#guard (twoStage.run 2 0).mass (.inr (1, 0)) = 1 / 4
#guard (twoStage.run 2 0).mass (.inr (1, 1)) = 1 / 4
#guard cyclic.autoCheck
#guard cyclic.autoSolve.map (fun vt => (vt.1 (.inl 0), vt.2 (.inl 0))) = .ok (5, 4)
#guard cyclic.autoSolve.map (fun vt => (vt.1 (.inl 1), vt.2 (.inl 1))) = .ok (5, 3)
#guard (cyclic.run 3 0).mass (.inr (1, 0)) = 1 / 2
#guard (cyclic.run 3 0).mass (.inl 1) = 1 / 2

end MultipleStates

section DomainBoundaries

-- Rejection covers the supplied domain even though one particular start succeeds.
#guard !partiallyClosed.autoCheck
#guard (partiallyClosed.autoSolve matches .error .absorptionBound)
#guard (partiallyClosed.run 1 0).mass (.inr (0, 0)) = 1
#guard partiallyClosed.survival 8 1 = 1
#guard noTransient.autoCheck
#guard noTransient.autoBound = 0
#guard noTransient.autoSolve.map (fun vt => (vt.1 (.inr 0), vt.2 (.inr 0))) = .ok (-3, 0)

end DomainBoundaries
