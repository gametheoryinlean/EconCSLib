/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Observed.Morphism.Inverse

/-!
# EconCSLib.GameTheory.ExtensiveGame.Observed.Morphism.Operational

Operational history and payoff naturality through strict isomorphisms.
-/

namespace ExtensiveGame.ObservedGame

universe uV

variable {N U : Type*}

namespace Iso

variable {G H : ObservedGame N U}

/-- The history-Arena isomorphism identifies terminal histories exactly. -/
theorem isTerminal_iff (e : G.Iso H)
    (h : G.base.toArena.HistoryFrom G.base.init) :
    G.base.isTerminal h.1 ↔
      H.base.isTerminal (e.historyIso.stateEquiv h).1 :=
  e.historyIso.isTerminal_iff h

/-- The pure history policies induced by mapped profiles commute with the
strict history and action equivalences. -/
theorem map_toHistoryPolicy
    (e : G.Iso H)
    (profile : G.PureProfile)
    (hNoChanceG : G.base.NoChanceOnHistories)
    (hNoChanceH : H.base.NoChanceOnHistories)
    (h : G.base.toArena.HistoryFrom G.base.init)
    (hsource : ¬ G.base.isTerminal h.1)
    (htarget :
      ¬ H.base.isTerminal (e.historyIso.stateEquiv h).1) :
    (e.mapProfile profile).toHistoryPolicy H hNoChanceH
        (e.historyIso.stateEquiv h) htarget =
      e.historyIso.actionEquiv h
        (profile.toHistoryPolicy G hNoChanceG h hsource) := by
  let i := G.playerAt hNoChanceG h hsource
  have hsourceMover :
      G.base.mover h.1 = some i :=
    G.mover_playerAt hNoChanceG h hsource
  have htargetMover :
      H.base.mover (e.historyIso.stateEquiv h).1 = some i := by
    rw [e.map_mover h]
    exact hsourceMover
  rw [PureProfile.toHistoryPolicy_of_mover
    H (e.mapProfile profile) hNoChanceH
    (e.historyIso.stateEquiv h) htarget i htargetMover]
  rw [PureProfile.toHistoryPolicy_of_mover
    G profile hNoChanceG h hsource i hsourceMover]
  exact
    e.map_actionAt profile h i hsourceMover
      (G.base.toArena.isDecision_of_not_isTerminal h.1 hsource)
      htargetMover
      (H.base.toArena.isDecision_of_not_isTerminal
        (e.historyIso.stateEquiv h).1 htarget)

/-- Strict history mapping commutes exactly with continuation execution of a
mapped no-chance pure profile. -/
theorem map_stoppedHistoryFrom
    [(s : G.base.State) → Decidable (G.base.isTerminal s)]
    [(t : H.base.State) → Decidable (H.base.isTerminal t)]
    (e : G.Iso H)
    (profile : G.PureProfile)
    (hNoChanceG : G.base.NoChanceOnHistories)
    (hNoChanceH : H.base.NoChanceOnHistories)
    (current : G.base.toArena.HistoryFrom G.base.init) :
    ∀ fuel,
      e.historyIso.stateEquiv
          (G.stoppedHistoryFrom profile hNoChanceG current fuel) =
        H.stoppedHistoryFrom (e.mapProfile profile) hNoChanceH
          (e.historyIso.stateEquiv current) fuel := by
  intro fuel
  induction fuel generalizing current with
  | zero =>
      rfl
  | succ fuel ih =>
      by_cases hsource : G.base.isTerminal current.1
      · have htarget :
            H.base.isTerminal
              (e.historyIso.stateEquiv current).1 :=
          (e.isTerminal_iff current).mp hsource
        rw [stoppedHistoryFrom, stoppedHistoryFrom,
          Arena.stoppedHistoryFrom_succ_of_terminal
            _ current fuel hsource,
          Arena.stoppedHistoryFrom_succ_of_terminal
            _ (e.historyIso.stateEquiv current) fuel htarget]
      · have htarget :
            ¬ H.base.isTerminal
              (e.historyIso.stateEquiv current).1 := by
          exact not_congr (e.isTerminal_iff current) |>.mp hsource
        rw [stoppedHistoryFrom, stoppedHistoryFrom,
          Arena.stoppedHistoryFrom_succ_of_not_terminal
            _ current fuel hsource,
          Arena.stoppedHistoryFrom_succ_of_not_terminal
            _ (e.historyIso.stateEquiv current) fuel htarget]
        change
          e.historyIso.stateEquiv
              (G.stoppedHistoryFrom profile hNoChanceG
                ⟨G.base.next current.1
                    (profile.toHistoryPolicy G hNoChanceG current hsource),
                  current.2.snoc
                    (profile.toHistoryPolicy G hNoChanceG current hsource)⟩
                fuel) =
            H.stoppedHistoryFrom (e.mapProfile profile) hNoChanceH
              ⟨H.base.next (e.historyIso.stateEquiv current).1
                  ((e.mapProfile profile).toHistoryPolicy H hNoChanceH
                    (e.historyIso.stateEquiv current) htarget),
                (e.historyIso.stateEquiv current).2.snoc
                  ((e.mapProfile profile).toHistoryPolicy H hNoChanceH
                    (e.historyIso.stateEquiv current) htarget)⟩
              fuel
        rw [ih]
        apply congrArg
          (fun next =>
            H.stoppedHistoryFrom (e.mapProfile profile) hNoChanceH
              next fuel)
        rw [e.map_toHistoryPolicy profile hNoChanceG hNoChanceH
          current hsource htarget]
        exact e.historyIso.map_next current
          (profile.toHistoryPolicy G hNoChanceG current hsource)

/-- Strict history mapping commutes with execution from the corresponding
initial empty histories. -/
theorem map_stoppedHistory
    [(s : G.base.State) → Decidable (G.base.isTerminal s)]
    [(t : H.base.State) → Decidable (H.base.isTerminal t)]
    (e : G.Iso H)
    (profile : G.PureProfile)
    (hNoChanceG : G.base.NoChanceOnHistories)
    (hNoChanceH : H.base.NoChanceOnHistories)
    (fuel : ℕ) :
    e.historyIso.stateEquiv
        (G.stoppedHistory profile hNoChanceG fuel) =
      H.stoppedHistory (e.mapProfile profile) hNoChanceH fuel := by
  change
    e.historyIso.stateEquiv
        (G.stoppedHistoryFrom profile hNoChanceG
          (Arena.HistoryFrom.nil G.base.toArena G.base.init) fuel) =
      H.stoppedHistoryFrom (e.mapProfile profile) hNoChanceH
        (Arena.HistoryFrom.nil H.base.toArena H.base.init) fuel
  rw [e.map_stoppedHistoryFrom, e.map_init]

/-- Strict observed-EFG isomorphisms preserve the optional terminal payoff of
every bounded continuation execution exactly. -/
theorem map_stoppedPayoffFrom
    [(s : G.base.State) → Decidable (G.base.isTerminal s)]
    [(t : H.base.State) → Decidable (H.base.isTerminal t)]
    (e : G.Iso H)
    (profile : G.PureProfile)
    (hNoChanceG : G.base.NoChanceOnHistories)
    (hNoChanceH : H.base.NoChanceOnHistories)
    (current : G.base.toArena.HistoryFrom G.base.init)
    (fuel : ℕ) :
    H.stoppedPayoffFrom (e.mapProfile profile) hNoChanceH
        (e.historyIso.stateEquiv current) fuel =
      G.stoppedPayoffFrom profile hNoChanceG current fuel := by
  rw [stoppedPayoffFrom, stoppedPayoffFrom,
    ← e.map_stoppedHistoryFrom profile hNoChanceG hNoChanceH current fuel]
  let result := G.stoppedHistoryFrom profile hNoChanceG current fuel
  change
    (if H.base.isTerminal (e.historyIso.stateEquiv result).1 then
        some (H.base.payoff (e.historyIso.stateEquiv result).1)
      else none) =
      if G.base.isTerminal result.1 then
        some (G.base.payoff result.1)
      else none
  by_cases hterminal : G.base.isTerminal result.1
  · have htarget :
        H.base.isTerminal (e.historyIso.stateEquiv result).1 :=
      (e.isTerminal_iff result).mp hterminal
    rw [if_pos htarget, if_pos hterminal,
      e.map_payoff result hterminal]
  · have htarget :
        ¬ H.base.isTerminal (e.historyIso.stateEquiv result).1 :=
      not_congr (e.isTerminal_iff result) |>.mp hterminal
    rw [if_neg htarget, if_neg hterminal]

/-- Strict observed-EFG isomorphisms preserve the optional terminal payoff
from the initial root exactly. -/
theorem map_stoppedPayoff
    [(s : G.base.State) → Decidable (G.base.isTerminal s)]
    [(t : H.base.State) → Decidable (H.base.isTerminal t)]
    (e : G.Iso H)
    (profile : G.PureProfile)
    (hNoChanceG : G.base.NoChanceOnHistories)
    (hNoChanceH : H.base.NoChanceOnHistories)
    (fuel : ℕ) :
    H.stoppedPayoff (e.mapProfile profile) hNoChanceH fuel =
      G.stoppedPayoff profile hNoChanceG fuel := by
  change
    H.stoppedPayoffFrom (e.mapProfile profile) hNoChanceH
        (Arena.HistoryFrom.nil H.base.toArena H.base.init) fuel =
      G.stoppedPayoffFrom profile hNoChanceG
        (Arena.HistoryFrom.nil G.base.toArena G.base.init) fuel
  rw [← e.map_init]
  exact
    e.map_stoppedPayoffFrom profile hNoChanceG hNoChanceH
      (Arena.HistoryFrom.nil G.base.toArena G.base.init) fuel

end Iso

end ExtensiveGame.ObservedGame
