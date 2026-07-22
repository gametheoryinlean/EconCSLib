/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Basic
import EconCSLib.GameTheory.ExtensiveGame.FiniteArenaExtraction
import EconCSLib.GameTheory.ExtensiveGame.GameTreeNE
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Examples.EntryDeterrence

The Entry Deterrence game: a classic 2-player extensive-form game.

```
                    Player 0
                   /        \
              Enter          Stay Out
               |               |
           Player 1          (1, 3)
           /      \
     Accommodate  Fight
        |           |
      (2, 2)      (0, 0)
```

## References

* [MSZ] Example 7.1
-/

/-! ### States and actions -/

inductive EDState | root | afterEnter | stayOut | accommodate | fight
  deriving DecidableEq, Repr, Inhabited

inductive EntrantAction | Enter | StayOut
  deriving DecidableEq, Repr, Inhabited

inductive IncumbentAction | Accommodate | Fight
  deriving DecidableEq, Repr, Inhabited

instance : Nonempty EntrantAction := ⟨.Enter⟩
instance : Nonempty IncumbentAction := ⟨.Accommodate⟩

open EDState EntrantAction IncumbentAction

@[reducible] def edAction : EDState → Type
  | root => EntrantAction
  | afterEnter => IncumbentAction
  | stayOut => Empty
  | accommodate => Empty
  | fight => Empty


/-! ### Game definition -/

@[reducible] def ED : ExtensiveGame (Fin 2) ℚ where
  State := EDState
  Action := edAction
  next s a := match s, a with
    | root, (Enter : edAction root) => afterEnter
    | root, (StayOut : edAction root) => stayOut
    | afterEnter, (Accommodate : edAction afterEnter) => accommodate
    | afterEnter, (Fight : edAction afterEnter) => fight
  init := root
  mover s := match s with
    | root => some 0
    | afterEnter => some 1
    | _ => none
  payoff s i := match s, i.val with
    | stayOut, 0 => 1
    | stayOut, _ => 3
    | accommodate, _ => 2
    | fight, _ => 0
    | _, _ => 0

/-! ### Verification -/

-- Terminal states (edAction s = Empty, so IsEmpty holds)
example : IsEmpty (edAction stayOut) := inferInstance
example : IsEmpty (edAction accommodate) := inferInstance
example : IsEmpty (edAction fight) := inferInstance

-- Non-terminal states (have at least one action)
example : Nonempty (edAction root) := ⟨Enter⟩
example : Nonempty (edAction afterEnter) := ⟨Accommodate⟩

-- Player assignment
example : ED.mover root = some 0 := rfl
example : ED.mover afterEnter = some 1 := rfl

-- Transitions
example : ED.next root Enter = afterEnter := rfl
example : ED.next root StayOut = stayOut := rfl
example : ED.next afterEnter Accommodate = accommodate := rfl
example : ED.next afterEnter Fight = fight := rfl

-- Payoffs
example : ED.payoff accommodate 0 = 2 := rfl
example : ED.payoff accommodate 1 = 2 := rfl
example : ED.payoff stayOut 0 = 1 := rfl
example : ED.payoff stayOut 1 = 3 := rfl
example : ED.payoff fight 0 = 0 := rfl
example : ED.payoff fight 1 = 0 := rfl

/-! ### Finite-tree equilibrium view

The following `GameTree` version formalizes the equilibrium-refinement point
made in MSZ Example 7.1: staying out while the incumbent threatens to fight is
a Nash equilibrium at the root, but it is not subgame-perfect because fighting
is not optimal in the reached subgame. Entering and accommodating is
subgame-perfect.
-/

namespace Examples.EntryDeterrence

open GameTree

/-- Player `0` is the entrant; player `1` is the incumbent. -/
abbrev Player := Fin 2

def entrant : Player := 0
def incumbent : Player := 1

/-- Terminal payoff vector for the entrant and incumbent. -/
def payoffVector (entrantPayoff incumbentPayoff : ℚ) : Player → ℚ
  | ⟨0, _⟩ => entrantPayoff
  | ⟨1, _⟩ => incumbentPayoff

def accommodateLeaf : GameTree Player ℚ := Leaf (payoffVector 2 2)
def fightLeaf : GameTree Player ℚ := Leaf (payoffVector 0 0)
def stayOutLeaf : GameTree Player ℚ := Leaf (payoffVector 1 3)

/-- The incumbent's subgame after entry. -/
def entryDeterrenceSubgame : GameTree Player ℚ :=
  Node incumbent accommodateLeaf (List.cons fightLeaf List.nil)

/-- The finite perfect-information entry-deterrence tree from MSZ Example 7.1. -/
def entryDeterrenceTree : GameTree Player ℚ :=
  Node entrant entryDeterrenceSubgame (List.cons stayOutLeaf List.nil)

/-- Select the first tail child when one exists; otherwise select the head.
    On the binary trees in this file this means "select the right branch". -/
def firstTailOrHead (h : GameTree Player ℚ) :
    (t : List (GameTree Player ℚ)) → { c : GameTree Player ℚ // c ∈ h :: t }
  | [] => ⟨h, by simp⟩
  | c :: _ => ⟨c, by simp⟩

/-- The strategy profile `(Enter, Accommodate)`. -/
def enterAccommodateStrategy : Strategy Player ℚ :=
  fun _ h _ => ⟨h, by simp⟩

/-- The strategy profile `(StayOut, Fight)`. -/
def stayOutFightStrategy : Strategy Player ℚ :=
  fun _ h t => firstTailOrHead h t

/-- The strategy profile `(StayOut, Accommodate)`, used as an incumbent
    deviation in the off-path subgame. -/
def stayOutAccommodateStrategy : Strategy Player ℚ :=
  fun m h t =>
    if m = incumbent then ⟨h, by simp⟩ else firstTailOrHead h t

theorem entryDeterrenceSubgame_subtree :
    Subtree entryDeterrenceSubgame entryDeterrenceTree := by
  simp [entryDeterrenceTree]
  exact Subtree.head entrant entryDeterrenceSubgame
    (List.cons stayOutLeaf List.nil)

theorem entryDeterrenceSubgame_properSubgame :
    ProperSubgame entryDeterrenceSubgame entryDeterrenceTree := by
  simp [entryDeterrenceTree]
  exact ProperSubgame.head entrant entryDeterrenceSubgame
    (List.cons stayOutLeaf List.nil)

theorem stayOutFight_to_stayOutAccommodate_incumbentVariant :
    IVariant incumbent stayOutFightStrategy stayOutAccommodateStrategy := by
  intro m h t hm
  simp [stayOutFightStrategy, stayOutAccommodateStrategy, hm]

theorem stayOutFight_isNashAt_entryDeterrence :
    IsNashAt stayOutFightStrategy entryDeterrenceTree := by
  intro i σ' hiv
  fin_cases i
  · have hroot_mem :
        (σ' entrant entryDeterrenceSubgame (List.cons stayOutLeaf List.nil)).val ∈
          entryDeterrenceSubgame :: List.cons stayOutLeaf List.nil :=
      (σ' entrant entryDeterrenceSubgame (List.cons stayOutLeaf List.nil)).property
    rcases List.mem_cons.mp hroot_mem with hroot | hroot_tail
    · have hsub_same :
          σ' incumbent accommodateLeaf (List.cons fightLeaf List.nil) =
            stayOutFightStrategy incumbent accommodateLeaf
              (List.cons fightLeaf List.nil) :=
        (hiv incumbent accommodateLeaf (List.cons fightLeaf List.nil) (by decide)).symm
      rw [entryDeterrenceTree, outcome_Node]
      rw [hroot]
      rw [entryDeterrenceSubgame, outcome_Node]
      rw [hsub_same]
      simp [stayOutFightStrategy, firstTailOrHead, fightLeaf, stayOutLeaf,
        payoffVector]
    · rcases List.mem_singleton.mp hroot_tail with hroot
      rw [entryDeterrenceTree, outcome_Node]
      rw [hroot]
      simp [stayOutFightStrategy, firstTailOrHead, stayOutLeaf, payoffVector]
  · have hroot_same :
        σ' entrant entryDeterrenceSubgame (List.cons stayOutLeaf List.nil) =
          stayOutFightStrategy entrant entryDeterrenceSubgame
            (List.cons stayOutLeaf List.nil) :=
      (hiv entrant entryDeterrenceSubgame (List.cons stayOutLeaf List.nil) (by decide)).symm
    rw [entryDeterrenceTree, outcome_Node]
    rw [hroot_same]
    simp [stayOutFightStrategy, firstTailOrHead, stayOutLeaf, payoffVector]

theorem stayOutFight_not_isNashAt_entrySubgame :
    ¬ IsNashAt stayOutFightStrategy entryDeterrenceSubgame := by
  intro hnash
  have hbad := hnash incumbent stayOutAccommodateStrategy
    stayOutFight_to_stayOutAccommodate_incumbentVariant
  have hle : (2 : ℚ) ≤ 0 := by
    simpa [entryDeterrenceSubgame, stayOutFightStrategy,
      stayOutAccommodateStrategy, firstTailOrHead, accommodateLeaf, fightLeaf,
      payoffVector, incumbent] using hbad
  norm_num at hle

theorem stayOutFight_not_isSubgamePerfectOn_entryDeterrence :
    ¬ IsSubgamePerfectOn stayOutFightStrategy entryDeterrenceTree := by
  intro hspe
  exact stayOutFight_not_isNashAt_entrySubgame
    (hspe.toNashAt_of_subtree entryDeterrenceSubgame_subtree)

theorem enterAccommodate_isNashAt_entrySubgame :
    IsNashAt enterAccommodateStrategy entryDeterrenceSubgame := by
  intro i σ' hiv
  fin_cases i
  · have hroot_same :
        σ' incumbent accommodateLeaf (List.cons fightLeaf List.nil) =
          enterAccommodateStrategy incumbent accommodateLeaf
            (List.cons fightLeaf List.nil) :=
      (hiv incumbent accommodateLeaf (List.cons fightLeaf List.nil) (by decide)).symm
    rw [entryDeterrenceSubgame, outcome_Node]
    rw [hroot_same]
    simp [enterAccommodateStrategy, accommodateLeaf, payoffVector]
  · have hroot_mem :
        (σ' incumbent accommodateLeaf (List.cons fightLeaf List.nil)).val ∈
          accommodateLeaf :: List.cons fightLeaf List.nil :=
      (σ' incumbent accommodateLeaf (List.cons fightLeaf List.nil)).property
    rcases List.mem_cons.mp hroot_mem with hroot | hroot_tail
    · rw [entryDeterrenceSubgame, outcome_Node]
      rw [hroot]
      simp [enterAccommodateStrategy, accommodateLeaf, payoffVector]
    · rcases List.mem_singleton.mp hroot_tail with hroot
      rw [entryDeterrenceSubgame, outcome_Node]
      rw [hroot]
      simp [enterAccommodateStrategy, fightLeaf, accommodateLeaf, payoffVector]

theorem enterAccommodate_isSubgamePerfectOn_entrySubgame :
    IsSubgamePerfectOn enterAccommodateStrategy entryDeterrenceSubgame := by
  change IsSubgamePerfectOn enterAccommodateStrategy
    (Node incumbent accommodateLeaf (List.cons fightLeaf List.nil))
  rw [isSubgamePerfectOn_Node_iff]
  refine ⟨enterAccommodate_isNashAt_entrySubgame, ?_, ?_⟩
  · exact isSubgamePerfectOn_Leaf enterAccommodateStrategy (payoffVector 2 2)
  · intro c hmem
    rcases List.mem_singleton.mp hmem with rfl
    exact isSubgamePerfectOn_Leaf enterAccommodateStrategy (payoffVector 0 0)

theorem enterAccommodate_isNashAt_entryDeterrence :
    IsNashAt enterAccommodateStrategy entryDeterrenceTree := by
  intro i σ' hiv
  fin_cases i
  · have hroot_mem :
        (σ' entrant entryDeterrenceSubgame (List.cons stayOutLeaf List.nil)).val ∈
          entryDeterrenceSubgame :: List.cons stayOutLeaf List.nil :=
      (σ' entrant entryDeterrenceSubgame (List.cons stayOutLeaf List.nil)).property
    rcases List.mem_cons.mp hroot_mem with hroot | hroot_tail
    · have hsub_same :
          σ' incumbent accommodateLeaf (List.cons fightLeaf List.nil) =
            enterAccommodateStrategy incumbent accommodateLeaf
              (List.cons fightLeaf List.nil) :=
        (hiv incumbent accommodateLeaf (List.cons fightLeaf List.nil) (by decide)).symm
      rw [entryDeterrenceTree, outcome_Node]
      rw [hroot]
      rw [entryDeterrenceSubgame, outcome_Node]
      rw [hsub_same]
      simp [enterAccommodateStrategy, accommodateLeaf, stayOutLeaf, payoffVector]
    · rcases List.mem_singleton.mp hroot_tail with hroot
      rw [entryDeterrenceTree, outcome_Node]
      rw [hroot]
      simp [enterAccommodateStrategy, entryDeterrenceSubgame, stayOutLeaf,
        accommodateLeaf, payoffVector]
  · have hroot_same :
        σ' entrant entryDeterrenceSubgame (List.cons stayOutLeaf List.nil) =
          enterAccommodateStrategy entrant entryDeterrenceSubgame
            (List.cons stayOutLeaf List.nil) :=
      (hiv entrant entryDeterrenceSubgame (List.cons stayOutLeaf List.nil) (by decide)).symm
    have hsub_mem :
        (σ' incumbent accommodateLeaf (List.cons fightLeaf List.nil)).val ∈
          accommodateLeaf :: List.cons fightLeaf List.nil :=
      (σ' incumbent accommodateLeaf (List.cons fightLeaf List.nil)).property
    rcases List.mem_cons.mp hsub_mem with hsub | hsub_tail
    · rw [entryDeterrenceTree, outcome_Node]
      rw [hroot_same]
      simp [enterAccommodateStrategy]
      rw [entryDeterrenceSubgame, outcome_Node]
      rw [hsub]
      simp [enterAccommodateStrategy, accommodateLeaf, payoffVector]
    · rcases List.mem_singleton.mp hsub_tail with hsub
      rw [entryDeterrenceTree, outcome_Node]
      rw [hroot_same]
      simp [enterAccommodateStrategy]
      rw [entryDeterrenceSubgame, outcome_Node]
      rw [hsub]
      simp [enterAccommodateStrategy, fightLeaf, accommodateLeaf, payoffVector]

theorem enterAccommodate_isSubgamePerfectOn_entryDeterrence :
    IsSubgamePerfectOn enterAccommodateStrategy entryDeterrenceTree := by
  change IsSubgamePerfectOn enterAccommodateStrategy
    (Node entrant entryDeterrenceSubgame (List.cons stayOutLeaf List.nil))
  rw [isSubgamePerfectOn_Node_iff]
  refine ⟨enterAccommodate_isNashAt_entryDeterrence, ?_, ?_⟩
  · exact enterAccommodate_isSubgamePerfectOn_entrySubgame
  · intro c hmem
    rcases List.mem_singleton.mp hmem with rfl
    exact isSubgamePerfectOn_Leaf enterAccommodateStrategy (payoffVector 1 3)

/-- The Arena-style entry-deterrence game extracts to the finite
    perfect-information `GameTree` used by the equilibrium-refinement proofs. -/
theorem entryDeterrenceArena_extracts_tree :
    ExtensiveGame.ExtractsGameTree ED ED.init entryDeterrenceTree := by
  change ExtensiveGame.ExtractsGameTree ED root entryDeterrenceTree
  unfold entryDeterrenceTree entryDeterrenceSubgame accommodateLeaf fightLeaf
    stayOutLeaf
  apply ExtensiveGame.ExtractsGameTree.node
    (head := Enter)
    (tail := List.cons StayOut List.nil)
  · rfl
  · intro a
    cases a <;> simp
  · apply ExtensiveGame.ExtractsGameTree.node
      (head := Accommodate)
      (tail := List.cons Fight List.nil)
    · rfl
    · intro a
      cases a <;> simp
    · convert ExtensiveGame.ExtractsGameTree.leaf (G := ED) accommodate ?_
      · funext i
        fin_cases i <;> rfl
      · change IsEmpty (edAction accommodate)
        infer_instance
    · apply ExtensiveGame.ExtractsGameTreeList.cons
      · convert ExtensiveGame.ExtractsGameTree.leaf (G := ED) fight ?_
        · funext i
          fin_cases i <;> rfl
        · change IsEmpty (edAction fight)
          infer_instance
      · apply ExtensiveGame.ExtractsGameTreeList.nil
  · apply ExtensiveGame.ExtractsGameTreeList.cons
    · convert ExtensiveGame.ExtractsGameTree.leaf (G := ED) stayOut ?_
      · funext i
        fin_cases i <;> rfl
      · change IsEmpty (edAction stayOut)
        infer_instance
    · apply ExtensiveGame.ExtractsGameTreeList.nil

end Examples.EntryDeterrence
