/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Basic
import EconCSLib.GameTheory.ExtensiveGame.FiniteArenaExtraction
import EconCSLib.GameTheory.ExtensiveGame.GameTreeNE
import Mathlib.Data.Rat.Cast.Defs

/-!
# EconCSLib.Examples.CentipedeGame

The Centipede Game with the Arena framework.

Players alternate choosing Stop or Continue. On Continue, the acting player
pays 1 (thousand) to give 3 (thousand) to the other. Backward induction
says Stop immediately — the paradox of backward induction.

## Attribution

Adapted from `GameTheory/Examples/TheCentipedeGame.lean` in
[math-xmum/gametheory](https://github.com/math-xmum/gametheory).
-/

inductive CPAct | S | C
  deriving DecidableEq, Repr, Inhabited

open CPAct

/-- State of a centipede game. -/
structure CPState where
  round : ℕ
  maxRound : ℕ
  moneyI : ℤ
  moneyII : ℤ
  turnIsI : Bool   -- true = Player I's turn
  ended : Bool
  deriving DecidableEq, Repr

def CPState.isOver (s : CPState) : Bool := s.ended || (s.round > s.maxRound)

/-- Apply an action (Stop or Continue). Terminal states map to themselves. -/
def CPState.step (s : CPState) (a : CPAct) : CPState :=
  if s.isOver then s
  else match a with
  | S => { s with ended := true }
  | C =>
    if s.turnIsI then
      { round := s.round + 1, maxRound := s.maxRound,
        moneyI := s.moneyI - 1, moneyII := s.moneyII + 3,
        turnIsI := false, ended := false }
    else
      { round := s.round + 1, maxRound := s.maxRound,
        moneyI := s.moneyI + 3, moneyII := s.moneyII - 1,
        turnIsI := true, ended := false }

/-- The n-round Centipede Game.

  Actions are `CPAct` at ALL states (including terminal). At terminal states,
  actions are "no-ops" (the state doesn't change). This avoids dependent types.
  Terminal states are detected by `IsOver`. -/
def centipede (n : ℕ) : ExtensiveGame (Fin 2) ℤ where
  State := CPState
  Action := fun _ => CPAct
  next := CPState.step
  init := { round := 1, maxRound := n, moneyI := 1, moneyII := 0,
            turnIsI := true, ended := false }
  mover s := if s.isOver then none else if s.turnIsI then some 0 else some 1
  payoff s i := if i = 0 then s.moneyI else s.moneyII

/-! ### Verification for n = 3 -/

def cp3 := centipede 3
def s₀ := cp3.init

-- Initial state
example : s₀.round = 1 := rfl
example : s₀.moneyI = 1 := rfl
example : s₀.turnIsI = true := rfl
example : s₀.isOver = false := rfl

-- Player I stops immediately: payoff (1, 0)
def s₀S := s₀.step S
example : s₀S.ended = true := rfl
example : cp3.payoff s₀S 0 = 1 := rfl
example : cp3.payoff s₀S 1 = 0 := rfl

-- Play: I continues, II continues, I continues
def s₁ := s₀.step C    -- I continues
def s₂ := s₁.step C    -- II continues
def s₃ := s₂.step C    -- I continues

example : s₁.round = 2 := rfl
example : s₁.moneyI = 0 := rfl
example : s₁.moneyII = 3 := rfl
example : s₁.turnIsI = false := rfl

example : s₂.round = 3 := rfl
example : s₂.moneyI = 3 := rfl
example : s₂.moneyII = 2 := rfl
example : s₂.turnIsI = true := rfl

example : s₃.round = 4 := rfl
example : s₃.isOver = true := rfl

-- Final payoffs after full cooperation: (2, 5)
example : cp3.payoff s₃ 0 = 2 := rfl
example : cp3.payoff s₃ 1 = 5 := rfl

-- Compare: if I stops at round 1: (1, 0)
--          if both cooperate:      (2, 5)
-- Backward induction says Stop, but cooperation is better!

/-! ### A finite-tree equilibrium view -/

/-- States for a two-decision Centipede prefix with terminal states represented
    by empty action types. -/
inductive PrefixState
  | root
  | afterContinue
  | stop0
  | stop1
  | continue1
  deriving DecidableEq, Repr

namespace PrefixState

/-- Available actions in the two-decision Centipede prefix.  Terminal states
    have no constructors. -/
inductive PrefixAction : PrefixState → Type
  | stopRoot : PrefixAction root
  | continueRoot : PrefixAction root
  | stopP1 : PrefixAction afterContinue
  | continueP1 : PrefixAction afterContinue

instance : IsEmpty (PrefixAction stop0) :=
  ⟨by intro a; cases a⟩

instance : IsEmpty (PrefixAction stop1) :=
  ⟨by intro a; cases a⟩

instance : IsEmpty (PrefixAction continue1) :=
  ⟨by intro a; cases a⟩

open PrefixAction

def next : (s : PrefixState) → PrefixAction s → PrefixState
  | root, stopRoot => stop0
  | root, continueRoot => afterContinue
  | afterContinue, stopP1 => stop1
  | afterContinue, continueP1 => continue1

def mover : PrefixState → Option (Fin 2)
  | root => some 0
  | afterContinue => some 1
  | stop0 => none
  | stop1 => none
  | continue1 => none

def payoff : PrefixState → Fin 2 → ℤ
  | stop0, i => if i = 0 then 1 else 0
  | stop1, i => if i = 0 then 0 else 3
  | continue1, i => if i = 0 then 3 else 2
  | root, _ => 0
  | afterContinue, _ => 0

end PrefixState

/-- Arena-style presentation of the two-decision Centipede prefix. -/
def centipedePrefixArena : ExtensiveGame (Fin 2) ℤ where
  State := PrefixState
  Action := PrefixState.PrefixAction
  next := PrefixState.next
  init := PrefixState.root
  mover := PrefixState.mover
  payoff := PrefixState.payoff

/-- A small two-decision finite-tree centipede prefix using the same payoff
    convention as the Arena example. -/
def centipedePrefixTree : GameTree (Fin 2) ℤ :=
  GameTree.Node (0 : Fin 2)
    (GameTree.Leaf (fun i => if i = 0 then 1 else 0))
    (List.cons
      (GameTree.Node (1 : Fin 2)
        (GameTree.Leaf (fun i => if i = 0 then 0 else 3))
        (List.cons (GameTree.Leaf (fun i => if i = 0 then 3 else 2)) List.nil))
      List.nil)

/-- The finite-tree centipede prefix has a root-scoped subgame-perfect
    equilibrium by backward induction. -/
theorem centipedePrefix_has_spe_on :
    ∃ σ : GameTree.Strategy (Fin 2) ℤ,
      GameTree.IsSubgamePerfectOn σ centipedePrefixTree :=
  GameTree.Kuhn_exists_SPE_on centipedePrefixTree

/-- Subgame-perfect equilibrium at the root yields a root Nash equilibrium for
    the finite-tree centipede prefix. -/
theorem centipedePrefix_has_nash_at :
    ∃ σ : GameTree.Strategy (Fin 2) ℤ,
      GameTree.IsNashAt σ centipedePrefixTree := by
  obtain ⟨σ, hspe⟩ := centipedePrefix_has_spe_on
  exact ⟨σ, hspe.toNashAt⟩

/-- The finite no-chance Arena prefix extracts to the corresponding
    perfect-information `GameTree`. -/
theorem centipedePrefixArena_extracts_tree :
    ExtensiveGame.ExtractsGameTree centipedePrefixArena
      centipedePrefixArena.init centipedePrefixTree := by
  change ExtensiveGame.ExtractsGameTree centipedePrefixArena
    PrefixState.root centipedePrefixTree
  unfold centipedePrefixTree
  apply ExtensiveGame.ExtractsGameTree.node
    (head := PrefixState.PrefixAction.stopRoot)
    (tail := List.cons PrefixState.PrefixAction.continueRoot List.nil)
  · rfl
  · intro a
    cases a <;> simp
  · apply ExtensiveGame.ExtractsGameTree.leaf
    change IsEmpty (PrefixState.PrefixAction PrefixState.stop0)
    infer_instance
  · apply ExtensiveGame.ExtractsGameTreeList.cons
    · apply ExtensiveGame.ExtractsGameTree.node
        (head := PrefixState.PrefixAction.stopP1)
        (tail := List.cons PrefixState.PrefixAction.continueP1 List.nil)
      · rfl
      · intro a
        cases a <;> simp
      · apply ExtensiveGame.ExtractsGameTree.leaf
        change IsEmpty (PrefixState.PrefixAction PrefixState.stop1)
        infer_instance
      · apply ExtensiveGame.ExtractsGameTreeList.cons
        · apply ExtensiveGame.ExtractsGameTree.leaf
          change IsEmpty (PrefixState.PrefixAction PrefixState.continue1)
          infer_instance
        · apply ExtensiveGame.ExtractsGameTreeList.nil
    · apply ExtensiveGame.ExtractsGameTreeList.nil
