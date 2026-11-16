import EconCSLib.Math.Probability.FiniteMarkovChain.Reachability
import EconCSLib.Math.Probability.FiniteMarkovChain.Discounted
import EconCSLib.Math.Probability.FiniteMarkovChain.Automaton
import EconCSLib.Math.Probability.FiniteMarkovChain.Parity

/-!
# Nonabsorbing finite Markov-chain smoke test

The initial state terminates with probability `1 / 2` and enters a closed
nonterminal class with probability `1 / 2`.  This exercises the exact
reachability solver without importing analytic measure semantics or the
examples tree.  The same two bottom classes exercise min-parity: the closed
nonterminal class has odd priority and the absorbing terminal has even
priority, so accepting and rejecting mass are both `1 / 2`.
-/

namespace FiniteMarkovReachabilitySmoke

open FiniteMarkovChain

private def chain : Chain 2 1 where
  transient i j :=
    if i = 0 then
      if j = 1 then (1 / 2 : ℚ≥0) else 0
    else
      if j = 1 then 1 else 0
  terminal i _ := if i = 0 then (1 / 2 : ℚ≥0) else 0
  normalized := by native_decide
  reward := fun _ => 6

example : chain.canReachTerminal 0 = true := by
  native_decide

example : chain.canReachTerminal 1 = false := by
  native_decide

example : chain.reachProbability 0 = 1 / 2 := by
  native_decide

example : chain.nonterminationProbability 0 = 1 / 2 := by
  native_decide

example : chain.zeroOnNonhitReward 0 = 3 := by
  native_decide

example : (chain.outcomeLaw 0).mass (some 0) = 1 / 2 := by
  native_decide

example : (chain.outcomeLaw 0).mass none = 1 / 2 := by
  native_decide

example : chain.lateHitMass 1 0 = 0 := by
  native_decide

example : chain.solveDiscounted (1 / 2) (fun _ => 2) =
    some (fun i => if i = 0 then 3 else 4) := by
  native_decide

example : chain.discountedValue (1 / 2) (fun _ => 2) 1 = 4 := by
  native_decide

example : chain.finiteDiscountedValue (1 / 2) (fun _ => 2) 3 1 = 7 / 2 := by
  native_decide

example : chain.solveDiscounted 1 (fun _ => 2) = none := by
  native_decide

private def terminalMonitor : DeterministicMonitor 2 Bool Bool where
  initial := 0
  nextTransient state label := if label then 1 else state
  nextTerminal state label := if label then 1 else state
  accepting state := decide (state = 1)

private def transientLabel (state : Fin 2) : Bool :=
  decide (state = 1)

private def terminalLabel (_state : Fin 1) : Bool := true

example : chain.acceptanceProbability terminalMonitor
    transientLabel terminalLabel 0 = 1 / 2 := by
  native_decide

example : chain.initialAcceptanceValue terminalMonitor
    transientLabel terminalLabel 0 = 1 / 2 := by
  native_decide

example : chain.monitoredNonterminationProbability terminalMonitor
    transientLabel terminalLabel 0 = 1 / 2 := by
  native_decide

private def minPriority (state : Chain.TotalState 2 1) : ℕ :=
  if state = Chain.encodeTotal (Sum.inl (1 : Fin 2)) then 1 else 0

example : chain.isBottom
    (Chain.encodeTotal (Sum.inl (1 : Fin 2))) = true := by
  native_decide

example : chain.isBottom
    (Chain.encodeTotal (Sum.inr (0 : Fin 1))) = true := by
  native_decide

example : chain.parityProbability minPriority
    (Chain.encodeTotal (Sum.inl (0 : Fin 2))) = 1 / 2 := by
  native_decide

example : chain.parityNonacceptingProbability minPriority
    (Chain.encodeTotal (Sum.inl (0 : Fin 2))) = 1 / 2 := by
  native_decide

end FiniteMarkovReachabilitySmoke
