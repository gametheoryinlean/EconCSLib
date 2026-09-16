/-!
# EFG computability audit integration fixture

This module deliberately contains one noncomputable declaration so the Python
checker test can verify `Lean.isNoncomputable` against an elaborated module.
It is not part of the library or example import surfaces.
-/

/-- A deliberately noncomputable declaration for the environment audit. -/
noncomputable def EFGComputabilityNoncomputable.selectedNat : Nat :=
  Classical.choice inferInstance
