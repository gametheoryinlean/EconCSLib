/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Interface.Execution.Finite

/-!
# Finite-law execution import boundary

The finite-fuel public entry exposes deterministic, observed behavioral, and
finite-kernel execution without the measure-valued infinite-path or non-atomic
kernel layers.
-/

#check Arena.stochasticHistoryLawFrom
#check ExtensiveGame.ObservedChanceGame.withChanceKernel
#check ExtensiveGame.DiscreteObservedChanceGame
#check ExtensiveGame.ObservedChanceGame.completeInformation
#check ExtensiveGame.ObservedChanceGame.BehavioralProfile.toHistoryPolicy
#check ExtensiveGame.ObservedGame.FiniteEFGHypotheses.toFiniteHistoryGame
#check ExtensiveGame.ObservedGame.FiniteEFGHypotheses.toFiniteObservedGame
#check ExtensiveGame.ObservedGame.FiniteEFGHypotheses.toFiniteObservedChanceGame
#check ExtensiveGame.DiscreteControlledObservedChanceGame.BoundedHistoryLawFamily
#check ExtensiveGame.DiscreteControlledObservedChanceGame.BoundedHistoryLawFamily.CompleteHistoryLawRealization
#check ExtensiveGame.DiscreteControlledObservedChanceGame.CertifiedBehavioralExecutionLaw
#check ExtensiveGame.DiscreteControlledObservedChanceGame.behavioralCertifiedExecutionLaw
#check KernelArena

namespace CertifiedContinuationSupportBoundary

open ExtensiveGame

variable {N : Type*}
  {G : DiscreteControlledObservedChanceGame N}
  [terminalDecidable :
    (state : G.observed.base.State) →
      Decidable (G.observed.base.isTerminal state)]

/-- Downstream code obtains a legal continuation suffix from the certificate
without unfolding `behavioralHistoryLaw` or the stochastic executor. -/
example
    (S : G.CertifiedBehavioralExecutionLaw)
    (profile : G.BehavioralProfile)
    (current endpoint : G.observed.base.History)
    (fuel : ℕ)
    (hsupport :
      (S.historyLaw profile current fuel).HasPositiveAtom endpoint) :
    ∃ suffix :
        G.observed.base.toArena.History current.1 endpoint.1,
      endpoint.2 = current.2.append suffix :=
  S.exists_suffix_of_hasPositiveAtom profile current endpoint fuel hsupport

/-- Terminal absorption can likewise be consumed through the certificate:
every supported endpoint is the current history itself. -/
example
    (S : G.CertifiedBehavioralExecutionLaw)
    (profile : G.BehavioralProfile)
    (current endpoint : G.observed.base.History)
    (fuel : ℕ)
    (hterminal : G.observed.base.isTerminal current.1)
    (hsupport :
      (S.historyLaw profile current fuel).HasPositiveAtom endpoint) :
    endpoint = current :=
  S.eq_current_of_terminal_of_hasPositiveAtom
    profile current endpoint fuel hterminal hsupport

end CertifiedContinuationSupportBoundary

/--
error: Unknown constant `Arena.pathLaw`
-/
#guard_msgs in
#check Arena.pathLaw

/--
error: Unknown identifier `MeasurableKernelArena`
-/
#guard_msgs in
#check MeasurableKernelArena

/--
error: Unknown identifier `ProbabilityTheory.Kernel`
-/
#guard_msgs in
#check ProbabilityTheory.Kernel
