/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.StrategicGame.Checker
import EconCSLib.GameTheory.ExtensiveGame.Observed.Mixed
import EconCSLib.GameTheory.ExtensiveGame.Compiler.GameTreeOccurrenceObserved

/-!
# Root-bound finite pure Nash checking

Opt-in prototypes for checking every pure unilateral deviation in an observed
chance EFG with explicitly enumerable represented information and legal actions.
`strategicForm` uses the existing complete-history executor and exact rational
expectation. Its utility is the terminal payoff at the specified horizon, with
zero on unfinished histories; an insufficient horizon is not eventual utility.

The strategy tables are exactly the existing root-bound `PureStrategy` types.
Finiteness of a tree does not make `GameTree.PlayerStrategy` finite. Enumeration
is required as executable data here, not extracted from a `Finite` proof.
The hidden-action regressions below construct their enumerations explicitly.
This module neither computes mixed equilibria nor asserts pure Nash existence
for imperfect information. Canonical/Frontend APIs remain unchanged.
-/

namespace Examples.ExtensiveGame.FinitePureNash

open _root_.ExtensiveGame

section FiniteTables

variable {N : Type*} (G : ObservedChanceGame N ℚ)
variable [(s : G.observed.base.State) → Decidable (G.observed.base.isTerminal s)]

/-- The original root-bound contingent plans, evaluated by finite execution.
`current` retains the full history, including its absolute length. -/
def strategicForm (current : G.observed.base.History) (horizon : ℕ) :
    StrategicGame N ℚ where
  strategy := G.observed.PureStrategy
  payoff profile i :=
    (G.observed.base.toArena.stochasticHistoryLawFrom
      (ObservedChanceGame.BehavioralProfile.toHistoryPolicy G
        (ObservedGame.PureProfile.toBehavioral G.observed profile)) current horizon).expectRat
      (fun history => if G.observed.base.isTerminal history.1 then
        G.observed.base.payoff history.1 i else 0)

variable [Fintype N] [DecidableEq N]
variable [∀ i, Fintype (G.observed.RepresentedInfo i)]
variable [∀ i, DecidableEq (G.observed.RepresentedInfo i)]
variable [∀ i (information : G.observed.RepresentedInfo i),
  Fintype (G.observed.InfoAction i information.1)]

-- Function enumeration is constructive once its finite domain and fibers are.
local instance (i : N) : Fintype (G.observed.PureStrategy i) :=
  Pi.instFintype

local instance (current : G.observed.base.History) (horizon : ℕ) (i : N) :
    Fintype ((strategicForm G current horizon).strategy i) :=
  inferInstanceAs (Fintype (G.observed.PureStrategy i))

/-- Check all root-bound pure strategy tables using the existing Nash checker. -/
def check (current : G.observed.base.History) (horizon : ℕ)
    (profile : G.observed.PureProfile) : Bool :=
  isNashEq (strategicForm G current horizon) profile

/-- Soundness and completeness for the actual EFG pure deviation space.
The strategic-form profile and its unilateral update are definitionally the
original EFG profile and update, so no surjectivity certificate is assumed. -/
theorem check_iff (current : G.observed.base.History) (horizon : ℕ)
    (profile : G.observed.PureProfile) :
    check G current horizon profile = true ↔
      ∀ i (deviation : G.observed.PureStrategy i),
        (strategicForm G current horizon).payoff (Function.update profile i deviation) i ≤
          (strategicForm G current horizon).payoff profile i :=
  isNashEq_iff (strategicForm G current horizon) profile

end FiniteTables

namespace HiddenAction

/-- Both players have an explicitly enumerable Boolean name. -/
abbrev Player := Bool

/-- Two hidden choices followed by a nondegenerate random bonus. -/
inductive State
  | root
  | second (first : Bool)
  | chance (first second : Bool)
  | terminal (first second bonus : Bool)
  deriving DecidableEq

/-- Only terminal states have no actions. -/
def Action : State → Type
  | .terminal _ _ _ => PEmpty
  | _ => Bool

/-- One actual choice per stage; histories retain both hidden actions. -/
def next : (state : State) → Action state → State
  | .root, first => .second first
  | .second first, second => .chance first second
  | .chance first second, bonus => .terminal first second bonus

/-- Coordination when `opposed=false`, matching pennies when `opposed=true`.
The common random bonus is independent of either player's choice. -/
def payoff (opposed : Bool) : State → Player → ℚ
  | .terminal first second bonus, i =>
      (if (first == second) != (opposed && i) then 1 else 0) +
        (if bonus then 1 else 0)
  | _, _ => 17

/-- The second player receives the same information after either first choice. -/
def observed (opposed : Bool) : ObservedGame Player ℚ where
  base := {
    State := State
    Action := Action
    next := next
    init := .root
    mover := fun state => match state with
      | .root => some false
      | .second _ => some true
      | _ => none
    payoff := payoff opposed }
  Observation _ := Unit
  PublicObservation := Unit
  observe _ _ := ()
  publicObserve _ := ()
  publicOf _ _ := ()
  observe_public _ _ := rfl
  InfoState _ := Unit
  infoObserve _ _ := ()
  infoAt _ _ _ _ := ()
  infoAt_observe _ _ _ _ := rfl
  InfoAction _ _ := Bool
  actionEquiv history i hmover _ := by
    rcases history with ⟨state, path⟩
    cases state with
    | root => exact Equiv.refl Bool
    | second first => exact Equiv.refl Bool
    | chance first second => simp at hmover
    | terminal first second bonus => simp at hmover

/-- The exact chance bonus is one with probability one third. -/
def bonusLaw : FiniteLaw Bool where
  atoms := [(false, 2 / 3), (true, 1 / 3)]
  normalized := by norm_num

/-- Attach the explicitly constructed rational chance law. -/
def game (opposed : Bool) : ObservedChanceGame Player ℚ where
  observed := observed opposed
  chanceKernel history hchance := by
    rcases history with ⟨state, path⟩
    cases state with
    | root => exact False.elim (Option.some_ne_none false hchance.1)
    | second first => exact False.elim (Option.some_ne_none true hchance.1)
    | chance first second => exact bonusLaw
    | terminal first second bonus =>
      exact False.elim (hchance.2 (inferInstance : IsEmpty PEmpty))

/-- Terminality is decided from the concrete state constructor. -/
local instance terminalDecision (opposed : Bool) (state : (game opposed).observed.base.State) :
    Decidable ((game opposed).observed.base.isTerminal state) := by
  cases state with
  | root => exact isFalse (fun h => h.false false)
  | second first => exact isFalse (fun h => h.false false)
  | chance first second => exact isFalse (fun h => h.false false)
  | terminal first second bonus => exact isTrue (inferInstanceAs (IsEmpty PEmpty))

/-- A concrete representative at the first decision of the indicated player. -/
def information (opposed : Bool) (i : Player) : (game opposed).observed.RepresentedInfo i :=
  match i with
  | false => (game opposed).observed.representedInfoAt
      ⟨.root, Arena.History.nil⟩ false rfl ⟨false⟩
  | true => (game opposed).observed.representedInfoAt
      ⟨.second false,
        (Arena.History.nil : (game opposed).observed.base.toArena.History .root .root).snoc
          false⟩ true rfl ⟨false⟩

/-- Every represented coordinate is the explicitly constructed coordinate. -/
theorem information_unique (opposed : Bool) (i : Player)
    (x : (game opposed).observed.RepresentedInfo i) : x = information opposed i :=
  Subtype.ext (@Subsingleton.elim Unit _ x.1 (information opposed i).1)

/-- Singleton information equality requires no comparison of histories. -/
local instance informationDecidableEq (opposed : Bool) (i : Player) :
    DecidableEq ((game opposed).observed.RepresentedInfo i) :=
  fun x y => isTrue (Subtype.ext (@Subsingleton.elim Unit _ x.1 y.1))

/-- The singleton table contains an actual reachable decision witness. -/
local instance informationFintype (opposed : Bool) (i : Player) :
    Fintype ((game opposed).observed.RepresentedInfo i) :=
  ⟨{information opposed i}, fun x => by simp [information_unique opposed i x]⟩

/-- Both legal actions are enumerated by the executable Boolean instance. -/
local instance actionFintype (opposed : Bool) (i : Player)
    (x : (game opposed).observed.RepresentedInfo i) :
    Fintype ((game opposed).observed.InfoAction i x.1) := inferInstanceAs (Fintype Bool)

/-- A two-bit table; a player cannot branch on the opponent's hidden action. -/
def profile (opposed first second : Bool) : (game opposed).observed.PureProfile :=
  fun i _ => if i then second else first

/-- Every original EFG pure profile is represented by exactly these two choices. -/
theorem profile_complete (opposed : Bool) (σ : (game opposed).observed.PureProfile) :
    σ = profile opposed (σ false (information opposed false))
      (σ true (information opposed true)) := by
  funext i x
  rw [information_unique opposed i x]
  cases i <;> rfl

/-- The two concrete occurrences remain different histories. -/
def secondHistory (opposed first : Bool) : (game opposed).observed.base.History :=
  ⟨.second first,
    (Arena.History.nil : (game opposed).observed.base.toArena.History .root .root).snoc first⟩

/-- Hidden information identifies choices, even though the concrete states
and their complete histories differ. -/
theorem information_consistency (opposed : Bool)
    (σ : (game opposed).observed.PureProfile) :
    secondHistory opposed false ≠ secondHistory opposed true ∧
      σ.actionAt (game opposed).observed (secondHistory opposed false) true rfl ⟨false⟩ =
        σ.actionAt (game opposed).observed (secondHistory opposed true) true rfl ⟨false⟩ := by
  constructor
  · intro h
    have hstate := congrArg Sigma.fst h
    cases hstate
  · rfl

/-- Compute the root check after all three actions. -/
def rootCheck (opposed first second : Bool) : Bool :=
  check (game opposed) ⟨.root, Arena.History.nil⟩ 3 (profile opposed first second)

/-- The exact rational root payoff, including the nondegenerate chance step. -/
theorem root_payoff (opposed first second i : Bool) :
    (strategicForm (game opposed) ⟨.root, Arena.History.nil⟩ 3).payoff
        (profile opposed first second) i =
      (if (first == second) != (opposed && i) then 1 else 0) + 1 / 3 := by
  cases opposed <;> cases first <;> cases second <;> cases i <;> decide +kernel

/-- Every atom has terminated after three actions, for every original EFG
pure profile. Thus the checked root utility is the final payoff in these games. -/
theorem root_terminates (opposed : Bool) (σ : (game opposed).observed.PureProfile) :
    ((game opposed).observed.base.toArena.stochasticHistoryLawFrom
      (ObservedChanceGame.BehavioralProfile.toHistoryPolicy (game opposed)
        (σ.toBehavioral (game opposed).observed)) ⟨.root, Arena.History.nil⟩ 3).atoms.all
        (fun atom => decide ((game opposed).observed.base.isTerminal atom.1.1)) = true := by
  rw [profile_complete opposed σ]
  generalize σ false (information opposed false) = first
  generalize σ true (information opposed true) = second
  cases opposed <;> cases first <;> cases second <;> decide +kernel

/-- The coordination checker accepts exactly matching choices. -/
theorem coordination_check (first second : Bool) :
    rootCheck false first second = (first == second) := by
  cases first <;> cases second <;> decide +kernel

/-- No one of the four information-consistent matching-pennies profiles passes. -/
theorem matchingPennies_check (first second : Bool) :
    rootCheck true first second = false := by
  cases first <;> cases second <;> decide +kernel

/-- A concrete pure equilibrium, with every EFG deviation covered by the theorem. -/
theorem coordination_nash :
    IsNashEquilibrium (strategicForm (game false) ⟨.root, Arena.History.nil⟩ 3)
      (profile false false false) :=
  (check_iff (game false) _ 3 _).mp (coordination_check false false)

/-- Completeness of the tables rules out *all* EFG pure equilibria, not just
the displayed candidates. -/
theorem matchingPennies_no_pure_nash :
    ¬ ∃ σ, IsNashEquilibrium
      (strategicForm (game true) ⟨.root, Arena.History.nil⟩ 3) σ := by
  rintro ⟨σ, hσ⟩
  have hcheck := (check_iff (game true) _ 3 _).mpr hσ
  rw [profile_complete true σ] at hcheck
  change rootCheck true _ _ = true at hcheck
  rw [matchingPennies_check] at hcheck
  contradiction

/-- An unfinished horizon uses stopped utility zero, despite the auxiliary
nonterminal payoff being 17; it can therefore give a different Nash answer. -/
theorem horizon_zero :
    check (game true) ⟨.root, Arena.History.nil⟩ 0 (profile true false false) = true ∧
      (strategicForm (game true) ⟨.root, Arena.History.nil⟩ 0).payoff
        (profile true false false) false = 0 := by
  decide +kernel

/-- A nonempty current history keeps the first player's actual action;
restarting this profile at the initial root would instead yield one third. -/
theorem retained_history_payoff :
    (strategicForm (game false) (secondHistory false true) 2).payoff
      (profile false false true) true = 4 / 3 ∧
    (strategicForm (game false) ⟨.root, Arena.History.nil⟩ 3).payoff
      (profile false false true) true = 1 / 3 := by
  decide +kernel

/-- info: (true, false, false, false) -/
#guard_msgs in
#eval (rootCheck false false false, rootCheck false false true,
  rootCheck true false false, rootCheck true false true)

end HiddenAction

namespace Occurrence

open GameTree

variable {N : Type*} (root : GameTree N ℚ)

/-- Pure occurrence profiles execute as Dirac laws in the existing chance
compiler. The proof reuses both pure execution and behavioral compilation. -/
theorem historyLaw_eq_pure
    (profile : (toOccurrenceObservedGame root).PureProfile)
    (current : (toExtensiveGame root).toArena.HistoryFrom root) (horizon : ℕ) :
    (toExtensiveGame root).toArena.stochasticHistoryLawFrom
        (ObservedChanceGame.BehavioralProfile.toHistoryPolicy
          (toOccurrenceObservedChanceGame root)
          (profile.toBehavioral (toOccurrenceObservedGame root))) current horizon =
      FiniteLaw.pure ((toOccurrenceObservedGame root).stoppedHistoryFrom profile
        (toExtensiveGame_noChanceOnHistories root) current horizon) := by
  apply Arena.stochasticHistoryLawFrom_eq_pure_stoppedHistoryFrom
  induction horizon generalizing current with
  | zero => trivial
  | succ horizon ih =>
    simp only [Arena.StochasticHistoryPolicy.IsPureFor]
    split
    · trivial
    · rename_i hterminal
      constructor
      · let i := (toOccurrenceObservedGame root).playerAt
          (toExtensiveGame_noChanceOnHistories root) current hterminal
        have hmover := (toOccurrenceObservedGame root).mover_playerAt
          (toExtensiveGame_noChanceOnHistories root) current hterminal
        exact (ObservedChanceGame.pureProfile_toBehavioral_toHistoryPolicy_of_mover
          (toOccurrenceObservedChanceGame root) profile current hterminal i hmover).trans
          (congrArg FiniteLaw.pure
            (ObservedGame.PureProfile.toHistoryPolicy_of_mover
              (toOccurrenceObservedGame root) profile (toExtensiveGame_noChanceOnHistories root)
              current hterminal i hmover).symm)
      · exact ih _

/-- A structurally sufficient horizon gives the original occurrence outcome,
including at a nonempty retained history. No termination certificate is supplied. -/
theorem payoff_eq_occurrenceOutcome
    (profile : (toOccurrenceObservedGame root).PureProfile)
    (current : (toExtensiveGame root).toArena.HistoryFrom root)
    (horizon : ℕ) (hsize : current.1.size ≤ horizon) (i : N) :
    (strategicForm (toOccurrenceObservedChanceGame root) current horizon).payoff profile i =
      occurrenceOutcome root profile current i := by
  dsimp only [strategicForm]
  change FiniteLaw.expectRat
    ((toExtensiveGame root).toArena.stochasticHistoryLawFrom
      (ObservedChanceGame.BehavioralProfile.toHistoryPolicy (toOccurrenceObservedChanceGame root)
        (profile.toBehavioral (toOccurrenceObservedGame root))) current horizon) _ = _
  rw [historyLaw_eq_pure]
  simp only [toOccurrenceObservedChanceGame, ObservedChanceGame.ofNoChance]
  refine (FiniteLaw.expectRat_pure _ _).trans ?_
  obtain ⟨payoff, hterminal, houtcome⟩ :=
    stoppedHistoryFrom_reaches_occurrenceOutcome root profile current horizon hsize
  rw [hterminal]
  change (if (toExtensiveGame root).isTerminal (.Leaf payoff) then payoff i else 0) = _
  rw [if_pos (toExtensiveGame_isTerminal_leaf root payoff)]
  exact congrFun houtcome i

variable [Fintype N] [DecidableEq N]
variable [∀ i, Fintype ((toOccurrenceObservedChanceGame root).observed.RepresentedInfo i)]
variable [∀ i, DecidableEq ((toOccurrenceObservedChanceGame root).observed.RepresentedInfo i)]
variable [∀ i (information : (toOccurrenceObservedChanceGame root).observed.RepresentedInfo i),
  Fintype ((toOccurrenceObservedChanceGame root).observed.InfoAction i information.1)]

/-- With the computed sufficient horizon, the Bool result is equivalent to
absence of profitable deviations in the full original occurrence strategy space. -/
theorem check_iff_occurrenceNash
    (current : (toExtensiveGame root).toArena.HistoryFrom root)
    (profile : (toOccurrenceObservedGame root).PureProfile) :
    check (toOccurrenceObservedChanceGame root) current root.size profile = true ↔
      ∀ i (deviation : (toOccurrenceObservedGame root).PureStrategy i),
        occurrenceOutcome root (Function.update profile i deviation) current i ≤
          occurrenceOutcome root profile current i := by
  rw [check_iff]
  have hsize := (arenaHistory_subtree current.2).size_le
  simp only [payoff_eq_occurrenceOutcome root _ current _ hsize]
  rfl

/-- Given executable occurrence-table enumerations, the existing backward
induction profile passes the checker at every continuation. This applies to
the perfect-information occurrence compiler, not to hidden-action games. -/
theorem check_backwardInduction
    (current : (toExtensiveGame root).toArena.HistoryFrom root) :
    check (toOccurrenceObservedChanceGame root) current root.size
      (occurrenceBackwardInductionProfile root) = true := by
  rw [check_iff_occurrenceNash]
  intro i deviation
  exact (occurrenceOutcome_deviate_le_value root current i deviation).trans_eq
    (congrFun (occurrenceOutcome_backwardInduction_eq_value root current).symm i)

end Occurrence

end Examples.ExtensiveGame.FinitePureNash
