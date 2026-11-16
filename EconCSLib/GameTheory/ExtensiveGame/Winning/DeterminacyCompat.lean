/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Observed.PerfectRecall
import EconCSLib.GameTheory.ExtensiveGame.Observed.WellFormed
import EconCSLib.GameTheory.ExtensiveGame.Winning.BasicCompat
import EconCSLib.GameTheory.ExtensiveGame.Winning.Determinacy

/-!
# Payoff-aware logical-determinacy compatibility

The proved finite determinacy theorem is owned by the payoff-free controlled
carrier.  This module retains the legacy `ObservedGame` predicate and
hypothesis names without making the canonical theorem import payoffs.
-/

namespace ExtensiveGame.ObservedGame

variable {N U : Type*} {G : ObservedGame N U}

/-- Pathwise winning strategies for a fixed player. -/
abbrev PathwiseWinningStrategies
    (G : ObservedGame N U)
    (W : G.base.toArena.WinningCondition G.base.init N)
    (i : N) :=
  {strategy : G.PureStrategy i //
    G.HasPathwiseWinningStrategy W i strategy}

/-- Some player has a pathwise robust pure winning strategy. -/
def HasSomePathwiseWinningStrategy
    (G : ObservedGame N U)
    (W : G.base.toArena.WinningCondition G.base.init N) : Prop :=
  ∃ (i : N) (strategy : G.PureStrategy i),
    G.HasPathwiseWinningStrategy W i strategy

/-- Package one explicit pathwise winning strategy. -/
theorem hasSomePathwiseWinningStrategy_of_hasPathwiseWinningStrategy
    {W : G.base.toArena.WinningCondition G.base.init N}
    {i : N} {strategy : G.PureStrategy i}
    (hwinning : G.HasPathwiseWinningStrategy W i strategy) :
    G.HasSomePathwiseWinningStrategy W :=
  ⟨i, strategy, hwinning⟩

/-- Constructive two-player pathwise determinacy. -/
def IsTwoPlayerDetermined
    (G : ObservedGame (Fin 2) U)
    (W : G.base.toArena.WinningCondition G.base.init (Fin 2)) : Prop :=
  (∃ strategy : G.PureStrategy 0,
      G.HasPathwiseWinningStrategy W 0 strategy) ∨
    (∃ strategy : G.PureStrategy 1,
      G.HasPathwiseWinningStrategy W 1 strategy)

/-- The generic and explicit two-player predicates agree. -/
theorem hasSomePathwiseWinningStrategy_iff_isTwoPlayerDetermined
    {G : ObservedGame (Fin 2) U}
    {W : G.base.toArena.WinningCondition G.base.init (Fin 2)} :
    G.HasSomePathwiseWinningStrategy W ↔
      G.IsTwoPlayerDetermined W := by
  constructor
  · rintro ⟨i, strategy, hwinning⟩
    fin_cases i
    · exact Or.inl ⟨strategy, hwinning⟩
    · exact Or.inr ⟨strategy, hwinning⟩
  · rintro (hzero | hone)
    · rcases hzero with ⟨strategy, hwinning⟩
      exact ⟨0, strategy, hwinning⟩
    · rcases hone with ⟨strategy, hwinning⟩
      exact ⟨1, strategy, hwinning⟩

/-- Legacy payoff-aware finite determinacy hypothesis package. -/
structure FiniteTwoPlayerHypotheses
    (G : ObservedGame (Fin 2) U)
    (W : G.base.toArena.WinningCondition G.base.init (Fin 2)) : Type _ where
  finiteEFG : G.FiniteEFGHypotheses
  noChance : G.base.NoChanceOnHistories
  perfectInformation : G.PerfectInformation
  zeroSum : W.IsTwoPlayerZeroSum

/-- Legacy payoff-aware well-founded prefix hypothesis package. -/
structure WellFoundedPrefixHypotheses
    (G : ObservedGame (Fin 2) U)
    (W : G.base.toArena.WinningCondition G.base.init (Fin 2)) : Type _ where
  wellFounded : G.base.toArena.IsWellFoundedFrom G.base.init
  noChance : G.base.NoChanceOnHistories
  perfectInformation : G.PerfectInformation
  zeroSum : W.IsTwoPlayerZeroSum
  allDecisionInfoRepresented : G.AllDecisionInfoRepresented
  decisionMoverCoherent : G.DecisionMoverCoherent
  prefixDecision : Arena.WinningConditionFrom.PrefixDecision W

/-- Forget state payoffs from the legacy finite determinacy package. -/
def FiniteTwoPlayerHypotheses.toControlled
    {G : ObservedGame (Fin 2) U}
    {W : G.base.toArena.WinningCondition G.base.init (Fin 2)}
    (h : G.FiniteTwoPlayerHypotheses W) :
    G.toControlledObservedGame.FiniteTwoPlayerHypotheses W where
  finiteEFG := h.finiteEFG
  noChance := h.noChance
  perfectInformation := h.perfectInformation
  zeroSum := h.zeroSum

/-- Forget state payoffs from the legacy well-founded-prefix package. -/
def WellFoundedPrefixHypotheses.toControlled
    {G : ObservedGame (Fin 2) U}
    {W : G.base.toArena.WinningCondition G.base.init (Fin 2)}
    (h : G.WellFoundedPrefixHypotheses W) :
    G.toControlledObservedGame.WellFoundedPrefixHypotheses W where
  wellFounded := h.wellFounded
  noChance := h.noChance
  perfectInformation := h.perfectInformation
  zeroSum := h.zeroSum
  prefixDecision := h.prefixDecision

/-- Legacy payoff-aware finite determinacy is the canonical payoff-free
theorem under definitional payoff erasure. -/
theorem FiniteTwoPlayerHypotheses.isTwoPlayerDetermined
    {G : ObservedGame (Fin 2) U}
    {W : G.base.toArena.WinningCondition G.base.init (Fin 2)}
    (h : G.FiniteTwoPlayerHypotheses W) :
    G.IsTwoPlayerDetermined W :=
  h.toControlled.isTwoPlayerDetermined

/-- Legacy payoff-aware well-founded-prefix determinacy is the canonical
payoff-free theorem under definitional payoff erasure. -/
theorem WellFoundedPrefixHypotheses.isTwoPlayerDetermined
    {G : ObservedGame (Fin 2) U}
    {W : G.base.toArena.WinningCondition G.base.init (Fin 2)}
    (h : G.WellFoundedPrefixHypotheses W)
    (data :
      G.toControlledObservedGame.BackwardInductionData W) :
    G.IsTwoPlayerDetermined W :=
  h.toControlled.isTwoPlayerDetermined data

/-- Exclusive no-chance two-player objectives cannot give both players a
pathwise winning strategy. -/
theorem not_both_havePathwiseWinningStrategy
    {G : ObservedGame (Fin 2) U}
    [(state : G.base.State) →
      Decidable (G.base.isTerminal state)]
    {W : G.base.toArena.WinningCondition G.base.init (Fin 2)}
    (hNoChance : G.base.NoChanceOnHistories)
    (hexclusive : W.IsExclusive) :
    ¬ ((∃ strategy : G.PureStrategy 0,
          G.HasPathwiseWinningStrategy W 0 strategy) ∧
        (∃ strategy : G.PureStrategy 1,
          G.HasPathwiseWinningStrategy W 1 strategy)) := by
  rintro ⟨⟨strategyZero, hwinningZero⟩,
    ⟨strategyOne, hwinningOne⟩⟩
  let profile : G.PureProfile := fun i =>
    if hzero : i = 0 then
      hzero ▸ strategyZero
    else
      (Fin.eq_one_of_ne_zero i hzero) ▸ strategyOne
  have hprofileZero : profile 0 = strategyZero := by simp [profile]
  have hprofileOne : profile 1 = strategyOne := by simp [profile]
  let play : G.base.toArena.CompletePlayFrom G.base.init :=
    (profile.toHistoryPolicy G hNoChance).completePlay
  have hcompatibleZero :
      G.IsCompatibleWithPlayerStrategy 0 strategyZero play := by
    have hprofile :=
      profile.completePlay_isCompatibleWithPlayerStrategy hNoChance 0
    simpa [play, hprofileZero] using hprofile
  have hcompatibleOne :
      G.IsCompatibleWithPlayerStrategy 1 strategyOne play := by
    have hprofile :=
      profile.completePlay_isCompatibleWithPlayerStrategy hNoChance 1
    simpa [play, hprofileOne] using hprofile
  have hwinsZero : play ∈ W 0 :=
    hwinningZero play hcompatibleZero
  have hwinsOne : play ∈ W 1 :=
    hwinningOne play hcompatibleOne
  exact Fin.zero_ne_one (hexclusive play hwinsZero hwinsOne)

end ExtensiveGame.ObservedGame
