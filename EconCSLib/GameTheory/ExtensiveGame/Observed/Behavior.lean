/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Observed.Chance
import EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Law.Discrete

/-!
# EconCSLib.GameTheory.ExtensiveGame.Observed.Behavior

Information-indexed behavioral strategies for history-indexed observed EFGs.

Unlike the older state-indexed finite-simplex API in `BehaviorStrategy.lean`,
this layer makes information-set consistency structural:

```lean
(information : G.RepresentedInfo i) → FiniteLaw (G.InfoAction i information.1)
```

No finiteness assumption is imposed on action types.  For an
`ObservedChanceGame`, a behavioral profile induces a terminal-aware stochastic
history policy: player histories use the acting player's information-indexed
law, while chance histories use the game's declared chance kernel exactly.

## Main definitions

* `ObservedGame.BehavioralStrategy` and `BehavioralProfile`.
* `ObservedGame.BehavioralProfile.actionLawAt`.
* `ObservedGame.BehavioralProfile.deviate`.
* `ObservedChanceGame.BehavioralProfile.toHistoryPolicy`.

## Main results

* `ObservedChanceGame.BehavioralProfile.toHistoryPolicy_of_mover`.
* `ObservedChanceGame.BehavioralProfile.toHistoryPolicy_of_chance`.
* `ObservedChanceGame.BehavioralProfile.toHistoryPolicy_chanceConsistent`.
-/

namespace ExtensiveGame.ObservedGame

variable {N U : Type*} (G : ObservedGame N U)

/-- A behavioral strategy for player `i`, indexed only by that player's
decision information state. -/
abbrev BehavioralStrategy (i : N) :=
  G.toControlledObservedGame.BehavioralStrategy i

/-- One information-indexed behavioral strategy for every player. -/
abbrev BehavioralProfile :=
  G.toControlledObservedGame.BehavioralProfile

/-- The concrete legal-action law induced by a behavioral strategy at a
history controlled by its player. -/
def BehavioralStrategy.actionLawAt {i : N}
    (strategy : G.BehavioralStrategy i)
    (history : G.base.toArena.HistoryFrom G.base.init)
    (hmover : G.base.mover history.1 = some i)
    (hnonterminal : ¬ G.base.isTerminal history.1) :
    FiniteLaw (G.base.Action history.1) :=
  ControlledObservedGame.BehavioralStrategy.actionLawAt
    G.toControlledObservedGame strategy history hmover hnonterminal

/-- The concrete legal-action law induced by a behavioral profile at a
player-controlled history. -/
def BehavioralProfile.actionLawAt
    (profile : G.BehavioralProfile)
    (history : G.base.toArena.HistoryFrom G.base.init)
    (i : N) (hmover : G.base.mover history.1 = some i)
    (hnonterminal : ¬ G.base.isTerminal history.1) :
    FiniteLaw (G.base.Action history.1) :=
  ObservedGame.BehavioralStrategy.actionLawAt
    G (profile i) history hmover hnonterminal

/-- Equal information states force a behavioral profile to choose the same
packaged abstract action law. -/
theorem BehavioralProfile.actionLaw_eq_of_infoState_eq
    (profile : G.BehavioralProfile) (i : N)
    (history₁ history₂ :
      G.base.toArena.HistoryFrom G.base.init)
    (hmover₁ : G.base.mover history₁.1 = some i)
    (hdecision₁ : G.base.toArena.IsDecision history₁.1)
    (hmover₂ : G.base.mover history₂.1 = some i)
    (hdecision₂ : G.base.toArena.IsDecision history₂.1)
    (hsame :
      G.infoAt history₁ i hmover₁ hdecision₁ =
        G.infoAt history₂ i hmover₂ hdecision₂) :
    (⟨G.toControlledObservedGame.representedInfoAt
          history₁ i hmover₁ hdecision₁,
        profile i
          (G.toControlledObservedGame.representedInfoAt
            history₁ i hmover₁ hdecision₁)⟩ :
      Σ information : G.RepresentedInfo i,
        FiniteLaw (G.InfoAction i information.1)) =
      ⟨G.toControlledObservedGame.representedInfoAt
          history₂ i hmover₂ hdecision₂,
        profile i
          (G.toControlledObservedGame.representedInfoAt
            history₂ i hmover₂ hdecision₂)⟩ :=
  ControlledObservedGame.BehavioralProfile.actionLaw_eq_of_infoState_eq
    G.toControlledObservedGame profile i history₁ history₂
      hmover₁ hdecision₁ hmover₂ hdecision₂ hsame

/-- Unilateral deviation of an information-indexed behavioral profile. -/
abbrev BehavioralProfile.deviate [DecidableEq N]
    (profile : G.BehavioralProfile) (who : N)
    (deviation : G.BehavioralStrategy who) :
    G.BehavioralProfile :=
  ControlledObservedGame.BehavioralProfile.deviate
    G.toControlledObservedGame profile who deviation

@[simp]
theorem BehavioralProfile.deviate_same [DecidableEq N]
    (profile : G.BehavioralProfile) (who : N)
    (deviation : G.BehavioralStrategy who) :
    ObservedGame.BehavioralProfile.deviate
        G profile who deviation who =
      deviation := by
  simp [ObservedGame.BehavioralProfile.deviate,
    ControlledObservedGame.BehavioralProfile.deviate]

@[simp]
theorem BehavioralProfile.deviate_of_ne [DecidableEq N]
    (profile : G.BehavioralProfile) (who : N)
    (deviation : G.BehavioralStrategy who)
    {other : N} (hne : other ≠ who) :
    ObservedGame.BehavioralProfile.deviate
        G profile who deviation other =
      profile other := by
  simp [ObservedGame.BehavioralProfile.deviate,
    ControlledObservedGame.BehavioralProfile.deviate, hne]

end ExtensiveGame.ObservedGame

namespace ExtensiveGame.ObservedChanceGame

variable {N U : Type*} (G : ObservedChanceGame N U)

namespace BehavioralProfile

/-- The stochastic history policy induced by an observed-EFG behavioral
profile and the declared chance kernels. -/
def toHistoryPolicy
    (profile : G.observed.BehavioralProfile) :
    G.observed.base.toArena.StochasticHistoryPolicy
      G.observed.base.init :=
  fun history hnonterminal =>
    match hmover : G.observed.base.mover history.1 with
    | some i =>
        profile.actionLawAt G.observed history i hmover
          hnonterminal
    | none =>
        G.chanceKernel history ⟨hmover, hnonterminal⟩

/-- At a player history, the induced policy is exactly that player's
information-indexed concrete action law. -/
theorem toHistoryPolicy_of_mover
    (profile : G.observed.BehavioralProfile)
    (history :
      G.observed.base.toArena.HistoryFrom G.observed.base.init)
    (hnonterminal :
      ¬ G.observed.base.isTerminal history.1)
    (i : N)
    (hmover : G.observed.base.mover history.1 = some i) :
    toHistoryPolicy G profile history hnonterminal =
      profile.actionLawAt G.observed history i hmover
        hnonterminal := by
  rw [toHistoryPolicy]
  split
  · rename_i j hj
    have hji : j = i := by
      exact Option.some.inj (hj.symm.trans hmover)
    subst j
    rfl
  · rename_i hnone
    rw [hmover] at hnone
    contradiction

/-- At a chance history, the induced policy is exactly the declared chance
kernel. -/
theorem toHistoryPolicy_of_chance
    (profile : G.observed.BehavioralProfile)
    (history :
      G.observed.base.toArena.HistoryFrom G.observed.base.init)
    (hnonterminal :
      ¬ G.observed.base.isTerminal history.1)
    (hmover : G.observed.base.mover history.1 = none) :
    toHistoryPolicy G profile history hnonterminal =
      G.chanceKernel history ⟨hmover, hnonterminal⟩ := by
  rw [toHistoryPolicy]
  split
  · rename_i i hi
    rw [hmover] at hi
    contradiction
  · rfl

/-- Every behavioral-profile history policy is chance-consistent. -/
theorem toHistoryPolicy_chanceConsistent
    (profile : G.observed.BehavioralProfile) :
    G.ChanceConsistent (toHistoryPolicy G profile) := by
  intro history hnonterminal hmover
  exact
    toHistoryPolicy_of_chance G profile history hnonterminal hmover

end BehavioralProfile

end ExtensiveGame.ObservedChanceGame
