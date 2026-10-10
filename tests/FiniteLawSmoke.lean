/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.Math.Probability.FiniteLaw

/-!
# Executable finite-law regressions

The guards evaluate the main-library algorithms. The examples instantiate
their correctness theorems; neither introduces native-decision proof axioms.
The separate `FiniteLawAudit` replays the safe library declarations in the kernel.
-/

namespace FiniteLawSmoke

private def fairCoin : FiniteLaw Bool where
  atoms := [(false, 1 / 2), (true, 1 / 2)]
  normalized := by norm_num

section Composition

#guard fairCoin.mass false = 1 / 2
#guard fairCoin.mass true = 1 / 2

private def twoCoins : FiniteLaw (Bool × Bool) :=
  FiniteLaw.independentPair fairCoin fairCoin

#guard twoCoins.mass (true, true) = 1 / 4
#guard (fairCoin.map fun b => if b then (4 : ℚ) else 0).expectRat id = 2

-- An infinite function carrier requires neither enumeration nor function equality.
private def functions : FiniteLaw (ℕ → ℕ) :=
  fairCoin.map fun b n => if b then n + 1 else n

#guard functions.expectRat (fun f => f 3) = 7 / 2
#guard (functions.bind fun f => FiniteLaw.pure (f 3)).mass 4 = 1 / 2

-- Repeated atoms and zero-weight occurrences are part of the sparse representation.
private def repeated : FiniteLaw Bool where
  atoms := [(true, 1 / 4), (false, 0), (true, 3 / 4)]
  normalized := by norm_num

#guard repeated.mass true = 1
#guard repeated.mass false = 0

example : repeated.Equivalent (FiniteLaw.pure true) := by
  intro value
  change (1 / 4 : ℚ) * value true + (0 * value false +
      ((3 / 4 : ℚ) * value true + 0)) = 1 * value true + 0
  ring

end Composition

section Conditioning

#guard (fairCoin.condition? fun outcome => outcome).map (fun law => law.mass true) = some 1
#guard fairCoin.condition? (fun _ => false) = none
#guard (fairCoin.conditionOnFiber id true).map (fun law => law.mass true) = some 1
#guard fairCoin.conditionOnFiber (fun _ => false) true = none

-- A possible observation with payoff zero remains a successful posterior.
#guard (fairCoin.conditionOnFiber id false).map (fun law => law.expectRat (fun _ => 0)) =
  some 0
#guard (FiniteLaw.normalize? ([] : List (Bool × ℚ≥0))).isNone
#guard (FiniteLaw.normalize? [(true, (0 : ℚ≥0))]).isNone

end Conditioning

section IndependentTables

private def indexedCoins : FiniteLaw ((i : Fin 2) → Bool) :=
  FiniteLaw.finPi 2 fun _ => fairCoin

#guard indexedCoins.mass (fun _ => true) = 1 / 4
#guard ((FiniteLaw.fintypePi (I := Fin 2) fun _ => fairCoin).map (fun table => table 1)).mass
  true = 1 / 2

example (laws : Fin 2 → FiniteLaw Bool) (i : Fin 2) :
    ((FiniteLaw.fintypePi laws).map (fun table => table i)).Equivalent (laws i) :=
  FiniteLaw.fintypePi_map_apply laws i

end IndependentTables

section Couplings

private def diagonal := FiniteLaw.relCoupling_refl fairCoin

#guard diagonal.joint.eventMass (fun pair => pair.1.1 && pair.1.2) = 1 / 2

example : (diagonal.joint.map fun pair => pair.1.1).Equivalent fairCoin :=
  diagonal.leftEquivalent

private def coinAfterTrue (outcome : Bool) : FiniteLaw Bool :=
  if outcome then fairCoin else FiniteLaw.pure false

private def composed :=
  diagonal.bind (leftNext := coinAfterTrue) (rightNext := coinAfterTrue) fun left right h => by
    cases h
    exact FiniteLaw.relCoupling_refl (coinAfterTrue left)

#guard composed.joint.eventMass (fun pair => pair.1.1 && pair.1.2) = 1 / 4
#guard composed.joint.eventMass (fun pair => pair.1.1 != pair.1.2) = 0

end Couplings

section DeferredSampling

-- A chance draw decides whether to query the one available coordinate.
private def queryTree : FiniteLaw.FreshQueryTree (fun _ : Fin 1 => Bool) Bool {0} :=
  .chance fairCoin fun query =>
    if query then .query ⟨0, by simp⟩ fun answer => .done answer
    else .done false

#guard (queryTree.runOnDemand (fun _ => fairCoin)).mass true = 1 / 4
#guard (queryTree.runPresampled (fun _ => fairCoin)).mass true = 1 / 4

example : (queryTree.runPresampled (fun _ => fairCoin)).Equivalent
    (queryTree.runOnDemand (fun _ => fairCoin)) :=
  queryTree.runPresampled_eq_runOnDemand (fun _ => fairCoin)

end DeferredSampling

end FiniteLawSmoke
