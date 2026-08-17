/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.OpenProblem.Util.UnitCostRAMMachine

/-!
# Instruction-level unit-cost RAM example

This regression example adds two input integers.  The result is written into
an explicitly allocated memory cell and returned by `halt`; the ordinary
instructions, the allocated word, and the output-word transfer are all charged
by the interpreter.
-/

namespace EconCSLib.Examples.UnitCostRAMMachine

open EconCSLib.OpenProblem.UnitCostRAM

noncomputable section

def addTwoIntegersProgram : Program Empty where
  code := #[
    .constant 1 (.integer 0),
    .load 2 1,
    .constant 1 (.integer 1),
    .load 3 1,
    .integerAdd 4 2 3,
    .constant 6 (.integer 1),
    .allocate 6 5,
    .store 5 4,
    .constant 7 (.integer 1),
    .halt 5 7]

def addTwoIntegersRun : ProfiledCost ExecutionResult :=
  run (closedEnvironment fun _ => false) addTwoIntegersProgram 10
    [.integer 2, .integer 3]

def returnedFive : Bool :=
  match addTwoIntegersRun.ret with
  | .halted [.integer 5] _ => true
  | _ => false

example : returnedFive = true := by decide

example : ProfiledCost.steps addTwoIntegersRun = 12 := by
  decide

example : ProfiledCost.peakCells addTwoIntegersRun = 1 := by
  decide

end

end EconCSLib.Examples.UnitCostRAMMachine
