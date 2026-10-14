/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Execution.FinitePayoff
import EconCSLib.GameTheory.ExtensiveGame.Observed.Mixed
import EconCSLib.GameTheory.StrategicGame.Checker
import Mathlib.Data.FinEnum

/-!
# Executable finite-horizon pure Nash checking

This module turns an observed chance EFG with explicitly enumerable
information coordinates and legal information actions into a finite strategic
game at one supplied complete history and horizon.  Its payoff uses the
existing complete-history executor and `stoppedExpectedPayoffFrom`, so an
unfinished history contributes zero exactly as in the finite payoff layer.

The checked strategy tables are the library's original root-bound
`ObservedGame.PureStrategy` types.  The checker enumerates every unilateral
deviation in that space; it does not replace occurrence-sensitive information
with endpoint states or introduce a smaller strategy carrier.  Enumeration is
executable data through `Fintype` instances.  A mere proof that a carrier is
finite is not converted into an enumeration by classical choice.

`all` returns the unordered `Finset` supplied by those existing `Fintype`
instances.  Returning one executable witness also requires an enumeration
order, so `find` asks separately for `FinEnum G.observed.PureProfile`.  This is
strictly stronger data than proposition-level finiteness or an unordered
`Fintype`; it is never manufactured by classical choice.  Its order affects
only which equilibrium is returned when several exist, not soundness or
completeness.

If there are `P` pure profiles, `all` runs the checker on all `P`, while
`find` stops at the first success and runs it at most `P` times.  Each check
enumerates every player's pure unilateral deviations and evaluates exact
bounded history laws.  Thus both the profile space and the finite execution
tree can grow exponentially in their respective information coordinates and
horizon.

This is a bounded payoff checker.  It does not assert pure Nash existence,
compute mixed equilibria, or identify the selected horizon with eventual
utility without an additional termination argument.

## Main definitions

* `FinitePureNash.strategicForm`;
* `FinitePureNash.check`;
* `FinitePureNash.all`;
* `FinitePureNash.find`;
* `FinitePureNash.check_iff`;
* `FinitePureNash.mem_all_iff_isNashEquilibrium`;
* `FinitePureNash.find_sound` and `FinitePureNash.find_complete`.
-/

namespace ExtensiveGame.ObservedChanceGame.FinitePureNash

variable {N : Type*} (G : ObservedChanceGame N ℚ)
variable [(state : G.observed.base.State) →
  Decidable (G.observed.base.isTerminal state)]

/-- The original root-bound pure strategy space, evaluated by exact bounded
complete-history execution.  The supplied `current` history retains its whole
action route and absolute length. -/
def strategicForm (current : G.observed.base.History) (horizon : ℕ) :
    StrategicGame N ℚ where
  strategy := G.observed.PureStrategy
  payoff profile player :=
    (ObservedChanceGame.BehavioralProfile.toHistoryPolicy G
      (ObservedGame.PureProfile.toBehavioral G.observed profile)).stoppedExpectedPayoffFrom
        current horizon fun history =>
          G.observed.base.payoff history.1 player

variable [Fintype N] [DecidableEq N]
variable [∀ player, Fintype (G.observed.RepresentedInfo player)]
variable [∀ player, DecidableEq (G.observed.RepresentedInfo player)]
variable [∀ player (information : G.observed.RepresentedInfo player),
  Fintype (G.observed.InfoAction player information.1)]

private local instance (player : N) :
    Fintype (G.observed.PureStrategy player) :=
  Pi.instFintype

private local instance (current : G.observed.base.History)
    (horizon : ℕ) (player : N) :
    Fintype ((strategicForm G current horizon).strategy player) :=
  inferInstanceAs (Fintype (G.observed.PureStrategy player))

private local instance :
    Fintype G.observed.PureProfile :=
  Pi.instFintype

/-- Decide whether a root-bound pure profile is Nash for the exact stopped
payoff at `horizon`. -/
def check (current : G.observed.base.History) (horizon : ℕ)
    (profile : G.observed.PureProfile) : Bool :=
  isNashEq (strategicForm G current horizon) profile

/-- Enumerate every root-bound pure profile that passes the exact bounded
Nash checker.  A `Finset` is used so the result contains no duplicates,
independently of how the component `Fintype` instances were assembled. -/
def all (current : G.observed.base.History) (horizon : ℕ) :
    Finset G.observed.PureProfile :=
  Finset.univ.filter fun profile => check G current horizon profile = true

/-- Return the first bounded pure Nash profile in the supplied executable
enumeration order.  `FinEnum` is explicit ordered enumeration data; this
definition does not extract an order from the unordered `Fintype`. -/
def find [FinEnum G.observed.PureProfile]
    (current : G.observed.base.History) (horizon : ℕ) :
    Option G.observed.PureProfile :=
  (FinEnum.toList G.observed.PureProfile).find? fun profile =>
    check G current horizon profile

/-- Soundness and completeness for the original EFG pure unilateral
deviation space.  Both profile update and payoffs are those of
`strategicForm`; no representation-surjectivity certificate is needed. -/
theorem check_iff (current : G.observed.base.History) (horizon : ℕ)
    (profile : G.observed.PureProfile) :
    check G current horizon profile = true ↔
      ∀ player (deviation : G.observed.PureStrategy player),
        (strategicForm G current horizon).payoff
            (Function.update profile player deviation) player ≤
          (strategicForm G current horizon).payoff profile player :=
  isNashEq_iff (strategicForm G current horizon) profile

/-- The Boolean checker decides the existing strategic-game Nash predicate
on exactly the same root-bound pure strategy space. -/
theorem check_iff_isNashEquilibrium
    (current : G.observed.base.History) (horizon : ℕ)
    (profile : G.observed.PureProfile) :
    check G current horizon profile = true ↔
      IsNashEquilibrium (strategicForm G current horizon) profile :=
  isNashEq_iff (strategicForm G current horizon) profile

/-- Membership in `all` is exactly acceptance by the Boolean checker. -/
@[simp]
theorem mem_all_iff_check
    (current : G.observed.base.History) (horizon : ℕ)
    (profile : G.observed.PureProfile) :
    profile ∈ all G current horizon ↔
      check G current horizon profile = true := by
  simp [all]

/-- Membership in `all` is exactly finite-horizon pure Nash on the original
root-bound pure strategy space. -/
@[simp]
theorem mem_all_iff_isNashEquilibrium
    (current : G.observed.base.History) (horizon : ℕ)
    (profile : G.observed.PureProfile) :
    profile ∈ all G current horizon ↔
      IsNashEquilibrium (strategicForm G current horizon) profile := by
  exact (mem_all_iff_check G current horizon profile).trans
    (check_iff_isNashEquilibrium G current horizon profile)

/-- Every profile returned by `find` passes the Boolean checker. -/
theorem find_check [FinEnum G.observed.PureProfile]
    (current : G.observed.base.History) (horizon : ℕ)
    (profile : G.observed.PureProfile)
    (hfind : find G current horizon = some profile) :
    check G current horizon profile = true :=
  List.find?_some hfind

/-- Every profile returned by `find` is a bounded Nash equilibrium in the
same original unilateral-deviation space used by `check`. -/
theorem find_sound [FinEnum G.observed.PureProfile]
    (current : G.observed.base.History) (horizon : ℕ)
    (profile : G.observed.PureProfile)
    (hfind : find G current horizon = some profile) :
    IsNashEquilibrium (strategicForm G current horizon) profile := by
  apply (check_iff_isNashEquilibrium G current horizon profile).mp
  exact find_check G current horizon profile hfind

/-- Search failure is equivalent to absence of a bounded pure Nash profile.
The quantifier still ranges over the original root-bound pure profiles. -/
theorem find_eq_none_iff [FinEnum G.observed.PureProfile]
    (current : G.observed.base.History) (horizon : ℕ) :
    find G current horizon = none ↔
      ∀ profile : G.observed.PureProfile,
        ¬ IsNashEquilibrium (strategicForm G current horizon) profile := by
  simp [find, List.find?_eq_none,
    check_iff_isNashEquilibrium G current horizon]

/-- If a bounded pure Nash profile exists, the executable ordered search
returns one.  The theorem does not select a profile by proof; it establishes
success of the concrete `List.find?` computation. -/
theorem find_complete [FinEnum G.observed.PureProfile]
    (current : G.observed.base.History) (horizon : ℕ)
    (hexists : ∃ profile : G.observed.PureProfile,
      IsNashEquilibrium (strategicForm G current horizon) profile) :
    ∃ profile, find G current horizon = some profile := by
  by_cases hresult : ∃ profile, find G current horizon = some profile
  · exact hresult
  · have hnone : find G current horizon = none := by
      cases hfind : find G current horizon with
      | none => rfl
      | some profile => exact (hresult ⟨profile, hfind⟩).elim
    rw [find_eq_none_iff G current horizon] at hnone
    exact hexists.elim fun profile hprofile => (hnone profile hprofile).elim

/-- The ordered search returns some profile exactly when a bounded pure Nash
profile exists. -/
theorem exists_find_eq_some_iff [FinEnum G.observed.PureProfile]
    (current : G.observed.base.History) (horizon : ℕ) :
    (∃ profile, find G current horizon = some profile) ↔
      ∃ profile : G.observed.PureProfile,
        IsNashEquilibrium (strategicForm G current horizon) profile := by
  constructor
  · rintro ⟨profile, hprofile⟩
    exact ⟨profile, find_sound G current horizon profile hprofile⟩
  · exact find_complete G current horizon

end ExtensiveGame.ObservedChanceGame.FinitePureNash
