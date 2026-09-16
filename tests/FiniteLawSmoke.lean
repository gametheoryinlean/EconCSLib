import EconCSLib.Math.Probability.FiniteLaw

namespace FiniteLawSmoke

private def fairCoin : FiniteLaw Bool where
  atoms := [(false, 1 / 2), (true, 1 / 2)]
  normalized := by native_decide

example : fairCoin.mass false = 1 / 2 := by
  native_decide

example : fairCoin.mass true = 1 / 2 := by
  native_decide

private def twoCoins : FiniteLaw (Bool × Bool) :=
  FiniteLaw.independentPair fairCoin fairCoin

example : twoCoins.mass (true, true) = 1 / 4 := by
  native_decide

example :
    (fairCoin.condition? fun outcome => outcome).map
        (fun law => law.mass true) =
      some 1 := by
  native_decide

example : fairCoin.condition? (fun _ => false) = none := by
  native_decide

example :
    (fairCoin.conditionOnFiber id true).map
        (fun law => law.mass true) =
      some 1 := by
  native_decide

example :
    fairCoin.conditionOnFiber (fun _ => false) true = none := by
  native_decide

private def indexedCoins : FiniteLaw ((i : Fin 2) → Bool) :=
  FiniteLaw.finPi 2 fun _ => fairCoin

example : indexedCoins.mass (fun _ => true) = 1 / 4 := by
  native_decide

end FiniteLawSmoke
