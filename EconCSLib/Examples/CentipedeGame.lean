/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Basic
import EconCSLib.GameTheory.ExtensiveGame.FiniteArenaExtraction
import EconCSLib.GameTheory.ExtensiveGame.GameTreeNE
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Rat.Cast.Defs

/-!
# Examples.CentipedeGame

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

/-- The terminal payoff when Player I stops immediately. -/
def centipedePrefixStop0Leaf : GameTree (Fin 2) ℤ :=
  GameTree.Leaf (fun i => if i = 0 then 1 else 0)

/-- The terminal payoff when Player II stops after Player I continues. -/
def centipedePrefixStop1Leaf : GameTree (Fin 2) ℤ :=
  GameTree.Leaf (fun i => if i = 0 then 0 else 3)

/-- The terminal payoff when both players continue in the two-decision prefix. -/
def centipedePrefixContinue1Leaf : GameTree (Fin 2) ℤ :=
  GameTree.Leaf (fun i => if i = 0 then 3 else 2)

/-- Player II's subgame after Player I continues in the two-decision prefix. -/
def centipedePrefixContinuationTree : GameTree (Fin 2) ℤ :=
  GameTree.Node (1 : Fin 2)
    centipedePrefixStop1Leaf
    (List.cons centipedePrefixContinue1Leaf List.nil)

/-- A small two-decision finite-tree centipede prefix using the same payoff
    convention as the Arena example. -/
def centipedePrefixTree : GameTree (Fin 2) ℤ :=
  GameTree.Node (0 : Fin 2)
    centipedePrefixStop0Leaf
    (List.cons centipedePrefixContinuationTree List.nil)

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

/-- The concrete backward-induction strategy in the two-decision centipede
    prefix: stop at every decision node. -/
def centipedePrefixStopStrategy : GameTree.Strategy (Fin 2) ℤ :=
  fun _ h _ => ⟨h, by simp⟩

/-- Stopping is Nash in Player II's continuation subgame: Player II receives
    `3` from stopping and only `2` from continuing. -/
theorem centipedePrefixStop_isNashAt_continuation :
    GameTree.IsNashAt centipedePrefixStopStrategy
      centipedePrefixContinuationTree := by
  intro i σ' hiv
  fin_cases i
  · have hsame :
        σ' (1 : Fin 2) centipedePrefixStop1Leaf
            (List.cons centipedePrefixContinue1Leaf List.nil) =
          centipedePrefixStopStrategy (1 : Fin 2) centipedePrefixStop1Leaf
            (List.cons centipedePrefixContinue1Leaf List.nil) :=
      (hiv (1 : Fin 2) centipedePrefixStop1Leaf
        (List.cons centipedePrefixContinue1Leaf List.nil) (by decide)).symm
    rw [centipedePrefixContinuationTree, GameTree.outcome_Node]
    rw [hsame]
    simp [centipedePrefixStopStrategy, centipedePrefixStop1Leaf]
  · have hchoice_mem :
        (σ' (1 : Fin 2) centipedePrefixStop1Leaf
          (List.cons centipedePrefixContinue1Leaf List.nil)).val ∈
            centipedePrefixStop1Leaf ::
              List.cons centipedePrefixContinue1Leaf List.nil :=
      (σ' (1 : Fin 2) centipedePrefixStop1Leaf
        (List.cons centipedePrefixContinue1Leaf List.nil)).property
    rcases List.mem_cons.mp hchoice_mem with hchoice | hchoice_tail
    · rw [centipedePrefixContinuationTree, GameTree.outcome_Node]
      rw [hchoice]
      simp [centipedePrefixStopStrategy, centipedePrefixStop1Leaf]
    · rcases List.mem_singleton.mp hchoice_tail with hchoice
      rw [centipedePrefixContinuationTree, GameTree.outcome_Node]
      rw [hchoice]
      simp [centipedePrefixStopStrategy, centipedePrefixStop1Leaf,
        centipedePrefixContinue1Leaf]

/-- Stopping immediately is Nash at the root of the two-decision centipede
    prefix, given that Player II stops in the continuation subgame. -/
theorem centipedePrefixStop_isNashAt :
    GameTree.IsNashAt centipedePrefixStopStrategy centipedePrefixTree := by
  intro i σ' hiv
  fin_cases i
  · have hroot_mem :
        (σ' (0 : Fin 2) centipedePrefixStop0Leaf
          (List.cons centipedePrefixContinuationTree List.nil)).val ∈
            centipedePrefixStop0Leaf ::
              List.cons centipedePrefixContinuationTree List.nil :=
      (σ' (0 : Fin 2) centipedePrefixStop0Leaf
        (List.cons centipedePrefixContinuationTree List.nil)).property
    rcases List.mem_cons.mp hroot_mem with hroot | hroot_tail
    · rw [centipedePrefixTree, GameTree.outcome_Node]
      rw [hroot]
      simp [centipedePrefixStopStrategy, centipedePrefixStop0Leaf]
    · have hsame :
          σ' (1 : Fin 2) centipedePrefixStop1Leaf
              (List.cons centipedePrefixContinue1Leaf List.nil) =
            centipedePrefixStopStrategy (1 : Fin 2) centipedePrefixStop1Leaf
              (List.cons centipedePrefixContinue1Leaf List.nil) :=
        (hiv (1 : Fin 2) centipedePrefixStop1Leaf
          (List.cons centipedePrefixContinue1Leaf List.nil) (by decide)).symm
      rcases List.mem_singleton.mp hroot_tail with hroot
      rw [centipedePrefixTree, GameTree.outcome_Node]
      rw [hroot]
      rw [centipedePrefixContinuationTree, GameTree.outcome_Node]
      rw [hsame]
      simp [centipedePrefixStopStrategy, centipedePrefixStop0Leaf,
        centipedePrefixStop1Leaf]
  · have hroot_same :
        σ' (0 : Fin 2) centipedePrefixStop0Leaf
            (List.cons centipedePrefixContinuationTree List.nil) =
          centipedePrefixStopStrategy (0 : Fin 2) centipedePrefixStop0Leaf
            (List.cons centipedePrefixContinuationTree List.nil) :=
      (hiv (0 : Fin 2) centipedePrefixStop0Leaf
        (List.cons centipedePrefixContinuationTree List.nil) (by decide)).symm
    rw [centipedePrefixTree, GameTree.outcome_Node]
    rw [hroot_same]
    simp [centipedePrefixStopStrategy, centipedePrefixStop0Leaf]

/-- Stopping at Player II's continuation node is subgame-perfect on that
    continuation subgame. -/
theorem centipedePrefixStop_isSubgamePerfectOn_continuation :
    GameTree.IsSubgamePerfectOn centipedePrefixStopStrategy
      centipedePrefixContinuationTree := by
  change GameTree.IsSubgamePerfectOn centipedePrefixStopStrategy
    (GameTree.Node (1 : Fin 2) centipedePrefixStop1Leaf
      (List.cons centipedePrefixContinue1Leaf List.nil))
  rw [GameTree.isSubgamePerfectOn_Node_iff]
  refine ⟨centipedePrefixStop_isNashAt_continuation, ?_, ?_⟩
  · exact GameTree.isSubgamePerfectOn_Leaf centipedePrefixStopStrategy
      (fun i => if i = 0 then 0 else 3)
  · intro c hc
    rcases List.mem_singleton.mp hc with rfl
    exact GameTree.isSubgamePerfectOn_Leaf centipedePrefixStopStrategy
      (fun i => if i = 0 then 3 else 2)

/-- The concrete backward-induction strategy is subgame-perfect at the root of
    the two-decision centipede prefix. -/
theorem centipedePrefixStop_isSubgamePerfectOn :
    GameTree.IsSubgamePerfectOn centipedePrefixStopStrategy
      centipedePrefixTree := by
  change GameTree.IsSubgamePerfectOn centipedePrefixStopStrategy
    (GameTree.Node (0 : Fin 2) centipedePrefixStop0Leaf
      (List.cons centipedePrefixContinuationTree List.nil))
  rw [GameTree.isSubgamePerfectOn_Node_iff]
  refine ⟨centipedePrefixStop_isNashAt, ?_, ?_⟩
  · exact GameTree.isSubgamePerfectOn_Leaf centipedePrefixStopStrategy
      (fun i => if i = 0 then 1 else 0)
  · intro c hc
    rcases List.mem_singleton.mp hc with rfl
    exact centipedePrefixStop_isSubgamePerfectOn_continuation

/-- Select the first tail child when available; otherwise select the head.
    On the binary prefix this means "continue". -/
def centipedePrefixTailOrHead (h : GameTree (Fin 2) ℤ) :
    (t : List (GameTree (Fin 2) ℤ)) → { c : GameTree (Fin 2) ℤ // c ∈ h :: t }
  | [] => ⟨h, by simp⟩
  | c :: _ => ⟨c, by simp⟩

/-- The cooperative-looking strategy that continues at every decision node. -/
def centipedePrefixContinueStrategy : GameTree.Strategy (Fin 2) ℤ :=
  fun _ h t => centipedePrefixTailOrHead h t

/-- A Player II deviation from all-continue: keep Player I's root continuation
    choice, but stop in Player II's continuation subgame. -/
def centipedePrefixContinueThenStopStrategy : GameTree.Strategy (Fin 2) ℤ :=
  fun m h t =>
    if m = (1 : Fin 2) then ⟨h, by simp⟩ else centipedePrefixTailOrHead h t

/-- Continuing at both decision nodes reaches the high-payoff terminal branch
    `(3, 2)` in the two-decision prefix. -/
theorem centipedePrefixContinue_outcome :
    GameTree.outcome centipedePrefixContinueStrategy centipedePrefixTree 0 = 3 ∧
      GameTree.outcome centipedePrefixContinueStrategy centipedePrefixTree 1 = 2 := by
  simp [centipedePrefixTree, centipedePrefixContinuationTree,
    centipedePrefixContinueStrategy, centipedePrefixTailOrHead,
    centipedePrefixContinue1Leaf]

/-- The Player II stop-after-continuation deviation changes only Player II's
    decision nodes relative to the all-continue strategy. -/
theorem centipedePrefixContinueThenStop_playerOneVariant :
    GameTree.IVariant (1 : Fin 2) centipedePrefixContinueStrategy
      centipedePrefixContinueThenStopStrategy := by
  intro m h t hm
  simp [centipedePrefixContinueStrategy, centipedePrefixContinueThenStopStrategy,
    centipedePrefixTailOrHead, hm]

/-- The all-continue strategy is not Nash at the root: once Player I continues,
    Player II prefers stopping for payoff `3` over continuing for payoff `2`. -/
theorem centipedePrefixContinue_not_isNashAt :
    ¬ GameTree.IsNashAt centipedePrefixContinueStrategy centipedePrefixTree := by
  intro hnash
  have hbad := hnash (1 : Fin 2) centipedePrefixContinueThenStopStrategy
    centipedePrefixContinueThenStop_playerOneVariant
  have hle : (3 : ℤ) ≤ 2 := by
    simp [centipedePrefixTree, centipedePrefixContinuationTree,
      centipedePrefixContinueStrategy, centipedePrefixContinueThenStopStrategy,
      centipedePrefixTailOrHead, centipedePrefixStop1Leaf,
      centipedePrefixContinue1Leaf] at hbad
  exact (by decide : ¬ ((3 : ℤ) ≤ 2)) hle

/-! ### MSZ Example 7.16: exact 100-stage Centipede tree -/

/-- Payoff vector helper for the MSZ Centipede tree. -/
def centipedeMSZPayoff (p0 p1 : ℤ) : Fin 2 → ℤ :=
  fun i => if i = 0 then p0 else p1

@[simp]
theorem centipedeMSZPayoff_zero (p0 p1 : ℤ) :
    centipedeMSZPayoff p0 p1 (0 : Fin 2) = p0 := by
  simp [centipedeMSZPayoff]

@[simp]
theorem centipedeMSZPayoff_one (p0 p1 : ℤ) :
    centipedeMSZPayoff p0 p1 (1 : Fin 2) = p1 := by
  simp [centipedeMSZPayoff]

/-- A finite Centipede continuation.

`centipedeMSZTree n p0 p1 true` has `n` remaining decision nodes, Player I
moves next, and stopping immediately gives payoff `(p0, p1)`. Continuing from
a Player I node changes the next stop payoff to `(p0 - 1, p1 + 3)`;
continuing from a Player II node changes it to `(p0 + 3, p1 - 1)`.

Thus `centipedeMSZTree 100 1 0 true` is MSZ Example 7.16 / Figure 7.9:
stage 1 stop payoff `(1,0)`, stage 100 stop payoff `(98,101)`, and final
all-continue payoff `(101,100)`. -/
def centipedeMSZTree : ℕ → ℤ → ℤ → Bool → GameTree (Fin 2) ℤ
  | 0, p0, p1, _ => GameTree.Leaf (centipedeMSZPayoff p0 p1)
  | n + 1, p0, p1, true =>
      GameTree.Node (0 : Fin 2)
        (GameTree.Leaf (centipedeMSZPayoff p0 p1))
        (List.cons (centipedeMSZTree n (p0 - 1) (p1 + 3) false) List.nil)
  | n + 1, p0, p1, false =>
      GameTree.Node (1 : Fin 2)
        (GameTree.Leaf (centipedeMSZPayoff p0 p1))
        (List.cons (centipedeMSZTree n (p0 + 3) (p1 - 1) true) List.nil)

/-- The exact 100-stage Centipede game from MSZ Example 7.16. -/
def centipedeMSZ100Tree : GameTree (Fin 2) ℤ :=
  centipedeMSZTree 100 1 0 true

/-- The stop-at-every-node strategy immediately reaches the current stop payoff
    in every MSZ Centipede continuation. -/
@[simp]
theorem centipedeMSZStop_outcome_tree (n : ℕ) (p0 p1 : ℤ)
    (turnIsI : Bool) :
    GameTree.outcome centipedePrefixStopStrategy
        (centipedeMSZTree n p0 p1 turnIsI) =
      centipedeMSZPayoff p0 p1 := by
  cases n <;> cases turnIsI <;>
    simp [centipedeMSZTree, centipedePrefixStopStrategy]

/-- Continuing through a terminal MSZ Centipede continuation reaches its
    terminal payoff. -/
@[simp]
theorem centipedeMSZContinue_outcome_tree_zero (p0 p1 : ℤ)
    (turnIsI : Bool) :
    GameTree.outcome centipedePrefixContinueStrategy
        (centipedeMSZTree 0 p0 p1 turnIsI) =
      centipedeMSZPayoff p0 p1 := by
  cases turnIsI <;> simp [centipedeMSZTree]

/-- At a Player-I MSZ Centipede node, the all-continue strategy moves to the
    unique continuation child. -/
@[simp]
theorem centipedeMSZContinue_outcome_tree_succ_true (n : ℕ) (p0 p1 : ℤ) :
    GameTree.outcome centipedePrefixContinueStrategy
        (centipedeMSZTree (n + 1) p0 p1 true) =
      GameTree.outcome centipedePrefixContinueStrategy
        (centipedeMSZTree n (p0 - 1) (p1 + 3) false) := by
  simp [centipedeMSZTree, centipedePrefixContinueStrategy,
    centipedePrefixTailOrHead]

/-- At a Player-II MSZ Centipede node, the all-continue strategy moves to the
    unique continuation child. -/
@[simp]
theorem centipedeMSZContinue_outcome_tree_succ_false (n : ℕ) (p0 p1 : ℤ) :
    GameTree.outcome centipedePrefixContinueStrategy
        (centipedeMSZTree (n + 1) p0 p1 false) =
      GameTree.outcome centipedePrefixContinueStrategy
        (centipedeMSZTree n (p0 + 3) (p1 - 1) true) := by
  simp [centipedeMSZTree, centipedePrefixContinueStrategy,
    centipedePrefixTailOrHead]

/-- Deviation that makes player `i` choose the head child at every one of
    their decision nodes, leaving every other player's choices unchanged. -/
def centipedeStopAllFor (i : Fin 2) (σ : GameTree.Strategy (Fin 2) ℤ) :
    GameTree.Strategy (Fin 2) ℤ :=
  fun m h t => if m = i then ⟨h, by simp⟩ else σ m h t

/-- `centipedeStopAllFor i σ` changes only player `i`'s choices. -/
theorem centipedeStopAllFor_variant (i : Fin 2)
    (σ : GameTree.Strategy (Fin 2) ℤ) :
    GameTree.IVariant i σ (centipedeStopAllFor i σ) := by
  intro m h t hm
  simp [centipedeStopAllFor, hm]

/-- In every finite MSZ Centipede continuation, any subgame-perfect strategy
    profile produces the current stop payoff. This is the payoff form of the
    backward-induction uniqueness argument. -/
theorem centipedeMSZSPE_outcome :
    ∀ (n : ℕ) (p0 p1 : ℤ) (turnIsI : Bool)
      (σ : GameTree.Strategy (Fin 2) ℤ),
      GameTree.IsSubgamePerfectOn σ (centipedeMSZTree n p0 p1 turnIsI) →
        GameTree.outcome σ (centipedeMSZTree n p0 p1 turnIsI) =
          centipedeMSZPayoff p0 p1 := by
  intro n
  induction n with
  | zero =>
      intro p0 p1 turnIsI σ _hspe
      cases turnIsI <;> simp [centipedeMSZTree]
  | succ n ih =>
      intro p0 p1 turnIsI σ hspe
      cases turnIsI
      · let h : GameTree (Fin 2) ℤ :=
          GameTree.Leaf (centipedeMSZPayoff p0 p1)
        let child : GameTree (Fin 2) ℤ :=
          centipedeMSZTree n (p0 + 3) (p1 - 1) true
        let t : List (GameTree (Fin 2) ℤ) := List.cons child List.nil
        change GameTree.outcome σ (GameTree.Node (1 : Fin 2) h t) =
          centipedeMSZPayoff p0 p1
        have hchild_spe : GameTree.IsSubgamePerfectOn σ child := by
          simpa [child] using
            (hspe.tail_mem (c := child) (by simp [child]))
        have hchild_out :
            GameTree.outcome σ child = centipedeMSZPayoff (p0 + 3) (p1 - 1) :=
          ih (p0 + 3) (p1 - 1) true σ hchild_spe
        have hchoice : σ (1 : Fin 2) h t = ⟨h, by simp⟩ := by
          have hchoice_mem : (σ (1 : Fin 2) h t).val ∈ h :: t :=
            (σ (1 : Fin 2) h t).property
          rcases List.mem_cons.mp hchoice_mem with hstop | hcontinue_mem
          · exact Subtype.ext hstop
          · rcases List.mem_singleton.mp hcontinue_mem with hcontinue
            let τ : GameTree.Strategy (Fin 2) ℤ :=
              centipedeStopAllFor (1 : Fin 2) σ
            have hbad := hspe.toNashAt (1 : Fin 2) τ
              (centipedeStopAllFor_variant (1 : Fin 2) σ)
            change GameTree.outcome τ (GameTree.Node (1 : Fin 2) h t) (1 : Fin 2) ≤
              GameTree.outcome σ (GameTree.Node (1 : Fin 2) h t) (1 : Fin 2) at hbad
            rw [GameTree.outcome_Node, GameTree.outcome_Node] at hbad
            simp [τ, centipedeStopAllFor, h, t, child, hcontinue, hchild_out] at hbad
        rw [GameTree.outcome_Node, hchoice]
        simp [h]
      · let h : GameTree (Fin 2) ℤ :=
          GameTree.Leaf (centipedeMSZPayoff p0 p1)
        let child : GameTree (Fin 2) ℤ :=
          centipedeMSZTree n (p0 - 1) (p1 + 3) false
        let t : List (GameTree (Fin 2) ℤ) := List.cons child List.nil
        change GameTree.outcome σ (GameTree.Node (0 : Fin 2) h t) =
          centipedeMSZPayoff p0 p1
        have hchild_spe : GameTree.IsSubgamePerfectOn σ child := by
          simpa [child] using
            (hspe.tail_mem (c := child) (by simp [child]))
        have hchild_out :
            GameTree.outcome σ child = centipedeMSZPayoff (p0 - 1) (p1 + 3) :=
          ih (p0 - 1) (p1 + 3) false σ hchild_spe
        have hchoice : σ (0 : Fin 2) h t = ⟨h, by simp⟩ := by
          have hchoice_mem : (σ (0 : Fin 2) h t).val ∈ h :: t :=
            (σ (0 : Fin 2) h t).property
          rcases List.mem_cons.mp hchoice_mem with hstop | hcontinue_mem
          · exact Subtype.ext hstop
          · rcases List.mem_singleton.mp hcontinue_mem with hcontinue
            let τ : GameTree.Strategy (Fin 2) ℤ :=
              centipedeStopAllFor (0 : Fin 2) σ
            have hbad := hspe.toNashAt (0 : Fin 2) τ
              (centipedeStopAllFor_variant (0 : Fin 2) σ)
            change GameTree.outcome τ (GameTree.Node (0 : Fin 2) h t) (0 : Fin 2) ≤
              GameTree.outcome σ (GameTree.Node (0 : Fin 2) h t) (0 : Fin 2) at hbad
            rw [GameTree.outcome_Node, GameTree.outcome_Node] at hbad
            simp [τ, centipedeStopAllFor, h, t, child, hcontinue, hchild_out] at hbad
        rw [GameTree.outcome_Node, hchoice]
        simp [h]

/-- At every nonterminal Player-I MSZ Centipede continuation, any
    subgame-perfect strategy must choose Stop at the root. -/
theorem centipedeMSZSPE_root_stop_true (n : ℕ) (p0 p1 : ℤ)
    {σ : GameTree.Strategy (Fin 2) ℤ}
    (hspe : GameTree.IsSubgamePerfectOn σ
      (centipedeMSZTree (n + 1) p0 p1 true)) :
    σ (0 : Fin 2) (GameTree.Leaf (centipedeMSZPayoff p0 p1))
        (List.cons (centipedeMSZTree n (p0 - 1) (p1 + 3) false) List.nil) =
      ⟨GameTree.Leaf (centipedeMSZPayoff p0 p1), by simp⟩ := by
  let h : GameTree (Fin 2) ℤ := GameTree.Leaf (centipedeMSZPayoff p0 p1)
  let child : GameTree (Fin 2) ℤ :=
    centipedeMSZTree n (p0 - 1) (p1 + 3) false
  let t : List (GameTree (Fin 2) ℤ) := List.cons child List.nil
  change σ (0 : Fin 2) h t = ⟨h, by simp⟩
  have hchild_spe : GameTree.IsSubgamePerfectOn σ child := by
    simpa [child] using
      (hspe.tail_mem (c := child) (by simp [child]))
  have hchild_out :
      GameTree.outcome σ child = centipedeMSZPayoff (p0 - 1) (p1 + 3) :=
    centipedeMSZSPE_outcome n (p0 - 1) (p1 + 3) false σ hchild_spe
  have hchoice_mem : (σ (0 : Fin 2) h t).val ∈ h :: t :=
    (σ (0 : Fin 2) h t).property
  rcases List.mem_cons.mp hchoice_mem with hstop | hcontinue_mem
  · exact Subtype.ext hstop
  · rcases List.mem_singleton.mp hcontinue_mem with hcontinue
    let τ : GameTree.Strategy (Fin 2) ℤ := centipedeStopAllFor (0 : Fin 2) σ
    have hbad := hspe.toNashAt (0 : Fin 2) τ
      (centipedeStopAllFor_variant (0 : Fin 2) σ)
    change GameTree.outcome τ (GameTree.Node (0 : Fin 2) h t) (0 : Fin 2) ≤
      GameTree.outcome σ (GameTree.Node (0 : Fin 2) h t) (0 : Fin 2) at hbad
    rw [GameTree.outcome_Node, GameTree.outcome_Node] at hbad
    simp [τ, centipedeStopAllFor, h, t, child, hcontinue, hchild_out] at hbad

/-- At every nonterminal Player-II MSZ Centipede continuation, any
    subgame-perfect strategy must choose Stop at the root. -/
theorem centipedeMSZSPE_root_stop_false (n : ℕ) (p0 p1 : ℤ)
    {σ : GameTree.Strategy (Fin 2) ℤ}
    (hspe : GameTree.IsSubgamePerfectOn σ
      (centipedeMSZTree (n + 1) p0 p1 false)) :
    σ (1 : Fin 2) (GameTree.Leaf (centipedeMSZPayoff p0 p1))
        (List.cons (centipedeMSZTree n (p0 + 3) (p1 - 1) true) List.nil) =
      ⟨GameTree.Leaf (centipedeMSZPayoff p0 p1), by simp⟩ := by
  let h : GameTree (Fin 2) ℤ := GameTree.Leaf (centipedeMSZPayoff p0 p1)
  let child : GameTree (Fin 2) ℤ :=
    centipedeMSZTree n (p0 + 3) (p1 - 1) true
  let t : List (GameTree (Fin 2) ℤ) := List.cons child List.nil
  change σ (1 : Fin 2) h t = ⟨h, by simp⟩
  have hchild_spe : GameTree.IsSubgamePerfectOn σ child := by
    simpa [child] using
      (hspe.tail_mem (c := child) (by simp [child]))
  have hchild_out :
      GameTree.outcome σ child = centipedeMSZPayoff (p0 + 3) (p1 - 1) :=
    centipedeMSZSPE_outcome n (p0 + 3) (p1 - 1) true σ hchild_spe
  have hchoice_mem : (σ (1 : Fin 2) h t).val ∈ h :: t :=
    (σ (1 : Fin 2) h t).property
  rcases List.mem_cons.mp hchoice_mem with hstop | hcontinue_mem
  · exact Subtype.ext hstop
  · rcases List.mem_singleton.mp hcontinue_mem with hcontinue
    let τ : GameTree.Strategy (Fin 2) ℤ := centipedeStopAllFor (1 : Fin 2) σ
    have hbad := hspe.toNashAt (1 : Fin 2) τ
      (centipedeStopAllFor_variant (1 : Fin 2) σ)
    change GameTree.outcome τ (GameTree.Node (1 : Fin 2) h t) (1 : Fin 2) ≤
      GameTree.outcome σ (GameTree.Node (1 : Fin 2) h t) (1 : Fin 2) at hbad
    rw [GameTree.outcome_Node, GameTree.outcome_Node] at hbad
    simp [τ, centipedeStopAllFor, h, t, child, hcontinue, hchild_out] at hbad

/-- If Player I deviates by continuing, the next Player II node is unchanged
    under a Player-I-only deviation, so the continuation immediately stops with
    Player I payoff `p0 - 1`. -/
theorem centipedeMSZPlayerIContinue_variant_outcome (n : ℕ) (p0 p1 : ℤ)
    {σ' : GameTree.Strategy (Fin 2) ℤ}
    (hiv : GameTree.IVariant (0 : Fin 2) centipedePrefixStopStrategy σ') :
    GameTree.outcome σ' (centipedeMSZTree n (p0 - 1) (p1 + 3) false)
        (0 : Fin 2) = p0 - 1 := by
  cases n with
  | zero =>
      simp [centipedeMSZTree, centipedeMSZPayoff]
  | succ n =>
      let h : GameTree (Fin 2) ℤ :=
        GameTree.Leaf (centipedeMSZPayoff (p0 - 1) (p1 + 3))
      let t : List (GameTree (Fin 2) ℤ) :=
        List.cons (centipedeMSZTree n ((p0 - 1) + 3) ((p1 + 3) - 1) true)
          List.nil
      change GameTree.outcome σ' (GameTree.Node (1 : Fin 2) h t)
          (0 : Fin 2) = p0 - 1
      have hsame :
          σ' (1 : Fin 2) h t =
            centipedePrefixStopStrategy (1 : Fin 2) h t :=
        (hiv (1 : Fin 2) h t (by decide)).symm
      rw [GameTree.outcome_Node, hsame]
      simp [h, t, centipedePrefixStopStrategy]

/-- If Player II deviates by continuing, the next Player I node is unchanged
    under a Player-II-only deviation, so the continuation immediately stops with
    Player II payoff `p1 - 1`. -/
theorem centipedeMSZPlayerIIContinue_variant_outcome (n : ℕ) (p0 p1 : ℤ)
    {σ' : GameTree.Strategy (Fin 2) ℤ}
    (hiv : GameTree.IVariant (1 : Fin 2) centipedePrefixStopStrategy σ') :
    GameTree.outcome σ' (centipedeMSZTree n (p0 + 3) (p1 - 1) true)
        (1 : Fin 2) = p1 - 1 := by
  cases n with
  | zero =>
      simp [centipedeMSZTree, centipedeMSZPayoff]
  | succ n =>
      let h : GameTree (Fin 2) ℤ :=
        GameTree.Leaf (centipedeMSZPayoff (p0 + 3) (p1 - 1))
      let t : List (GameTree (Fin 2) ℤ) :=
        List.cons (centipedeMSZTree n ((p0 + 3) - 1) ((p1 - 1) + 3) false)
          List.nil
      change GameTree.outcome σ' (GameTree.Node (0 : Fin 2) h t)
          (1 : Fin 2) = p1 - 1
      have hsame :
          σ' (0 : Fin 2) h t =
            centipedePrefixStopStrategy (0 : Fin 2) h t :=
        (hiv (0 : Fin 2) h t (by decide)).symm
      rw [GameTree.outcome_Node, hsame]
      simp [h, t, centipedePrefixStopStrategy]

/-- Stopping is Nash at the root of every nonterminal MSZ Centipede
    continuation. -/
theorem centipedeMSZStop_isNashAt_tree_succ (n : ℕ) (p0 p1 : ℤ)
    (turnIsI : Bool) :
    GameTree.IsNashAt centipedePrefixStopStrategy
      (centipedeMSZTree (n + 1) p0 p1 turnIsI) := by
  cases turnIsI
  · let h : GameTree (Fin 2) ℤ :=
      GameTree.Leaf (centipedeMSZPayoff p0 p1)
    let t : List (GameTree (Fin 2) ℤ) :=
      List.cons (centipedeMSZTree n (p0 + 3) (p1 - 1) true) List.nil
    change GameTree.IsNashAt centipedePrefixStopStrategy
      (GameTree.Node (1 : Fin 2) h t)
    intro i σ' hiv
    fin_cases i
    · have hsame :
          σ' (1 : Fin 2) h t =
            centipedePrefixStopStrategy (1 : Fin 2) h t :=
        (hiv (1 : Fin 2) h t (by decide)).symm
      rw [GameTree.outcome_Node, GameTree.outcome_Node, hsame]
      simp [h, t, centipedePrefixStopStrategy]
    · have hchoice_mem :
          (σ' (1 : Fin 2) h t).val ∈ h :: t :=
        (σ' (1 : Fin 2) h t).property
      rcases List.mem_cons.mp hchoice_mem with hchoice | hchoice_tail
      · rw [GameTree.outcome_Node, hchoice, GameTree.outcome_Node]
        simp [h, t, centipedePrefixStopStrategy]
      · rcases List.mem_singleton.mp hchoice_tail with hchoice
        rw [GameTree.outcome_Node, hchoice, GameTree.outcome_Node]
        change GameTree.outcome σ'
            (centipedeMSZTree n (p0 + 3) (p1 - 1) true) (1 : Fin 2) ≤
          GameTree.outcome centipedePrefixStopStrategy
            (centipedePrefixStopStrategy (1 : Fin 2) h t).val (1 : Fin 2)
        rw [centipedeMSZPlayerIIContinue_variant_outcome n p0 p1 hiv]
        simp [h, t, centipedePrefixStopStrategy]
  · let h : GameTree (Fin 2) ℤ :=
      GameTree.Leaf (centipedeMSZPayoff p0 p1)
    let t : List (GameTree (Fin 2) ℤ) :=
      List.cons (centipedeMSZTree n (p0 - 1) (p1 + 3) false) List.nil
    change GameTree.IsNashAt centipedePrefixStopStrategy
      (GameTree.Node (0 : Fin 2) h t)
    intro i σ' hiv
    fin_cases i
    · have hchoice_mem :
          (σ' (0 : Fin 2) h t).val ∈ h :: t :=
        (σ' (0 : Fin 2) h t).property
      rcases List.mem_cons.mp hchoice_mem with hchoice | hchoice_tail
      · rw [GameTree.outcome_Node, hchoice, GameTree.outcome_Node]
        simp [h, t, centipedePrefixStopStrategy]
      · rcases List.mem_singleton.mp hchoice_tail with hchoice
        rw [GameTree.outcome_Node, hchoice, GameTree.outcome_Node]
        change GameTree.outcome σ'
            (centipedeMSZTree n (p0 - 1) (p1 + 3) false) (0 : Fin 2) ≤
          GameTree.outcome centipedePrefixStopStrategy
            (centipedePrefixStopStrategy (0 : Fin 2) h t).val (0 : Fin 2)
        rw [centipedeMSZPlayerIContinue_variant_outcome n p0 p1 hiv]
        simp [h, t, centipedePrefixStopStrategy]
    · have hsame :
          σ' (0 : Fin 2) h t =
            centipedePrefixStopStrategy (0 : Fin 2) h t :=
        (hiv (0 : Fin 2) h t (by decide)).symm
      rw [GameTree.outcome_Node, GameTree.outcome_Node, hsame]
      simp [h, t, centipedePrefixStopStrategy]

/-- Stopping at every decision node is subgame-perfect in every finite MSZ
    Centipede continuation. This is the backward-induction argument used in
    MSZ Example 7.16, stated recursively. -/
theorem centipedeMSZStop_isSubgamePerfectOn_tree :
    ∀ (n : ℕ) (p0 p1 : ℤ) (turnIsI : Bool),
      GameTree.IsSubgamePerfectOn centipedePrefixStopStrategy
        (centipedeMSZTree n p0 p1 turnIsI) := by
  intro n
  induction n with
  | zero =>
      intro p0 p1 turnIsI
      cases turnIsI <;>
        simpa [centipedeMSZTree] using
          (GameTree.isSubgamePerfectOn_Leaf centipedePrefixStopStrategy
            (centipedeMSZPayoff p0 p1))
  | succ n ih =>
      intro p0 p1 turnIsI
      cases turnIsI
      · change GameTree.IsSubgamePerfectOn centipedePrefixStopStrategy
          (GameTree.Node (1 : Fin 2)
            (GameTree.Leaf (centipedeMSZPayoff p0 p1))
            (List.cons (centipedeMSZTree n (p0 + 3) (p1 - 1) true) List.nil))
        rw [GameTree.isSubgamePerfectOn_Node_iff]
        refine ⟨centipedeMSZStop_isNashAt_tree_succ n p0 p1 false, ?_, ?_⟩
        · exact GameTree.isSubgamePerfectOn_Leaf centipedePrefixStopStrategy
            (centipedeMSZPayoff p0 p1)
        · intro c hc
          rcases List.mem_singleton.mp hc with rfl
          exact ih (p0 + 3) (p1 - 1) true
      · change GameTree.IsSubgamePerfectOn centipedePrefixStopStrategy
          (GameTree.Node (0 : Fin 2)
            (GameTree.Leaf (centipedeMSZPayoff p0 p1))
            (List.cons (centipedeMSZTree n (p0 - 1) (p1 + 3) false) List.nil))
        rw [GameTree.isSubgamePerfectOn_Node_iff]
        refine ⟨centipedeMSZStop_isNashAt_tree_succ n p0 p1 true, ?_, ?_⟩
        · exact GameTree.isSubgamePerfectOn_Leaf centipedePrefixStopStrategy
            (centipedeMSZPayoff p0 p1)
        · intro c hc
          rcases List.mem_singleton.mp hc with rfl
          exact ih (p0 - 1) (p1 + 3) false

/-- In the exact 100-stage MSZ Centipede game, stopping at every decision node
    is subgame-perfect. -/
theorem centipedeMSZ100_stop_isSubgamePerfectOn :
    GameTree.IsSubgamePerfectOn centipedePrefixStopStrategy
      centipedeMSZ100Tree := by
  simpa [centipedeMSZ100Tree] using
    centipedeMSZStop_isSubgamePerfectOn_tree 100 1 0 true

/-- The same stop-at-every-node strategy is Nash at the root of the exact
    100-stage MSZ Centipede game. -/
theorem centipedeMSZ100_stop_isNashAt :
    GameTree.IsNashAt centipedePrefixStopStrategy centipedeMSZ100Tree :=
  centipedeMSZ100_stop_isSubgamePerfectOn.toNashAt

/-- The subgame-perfect stop-at-every-node outcome in the exact 100-stage MSZ
    Centipede game is `(1, 0)`, as in the textbook backward-induction
    conclusion. -/
theorem centipedeMSZ100_stop_outcome :
    GameTree.outcome centipedePrefixStopStrategy centipedeMSZ100Tree (0 : Fin 2) = 1 ∧
      GameTree.outcome centipedePrefixStopStrategy centipedeMSZ100Tree (1 : Fin 2) = 0 := by
  simp [centipedeMSZ100Tree]

/-- If both players continue through every decision node in the exact
    100-stage MSZ Centipede game, the terminal payoff is `(101, 100)`. -/
theorem centipedeMSZ100_continue_outcome :
    GameTree.outcome centipedePrefixContinueStrategy centipedeMSZ100Tree (0 : Fin 2) = 101 ∧
      GameTree.outcome centipedePrefixContinueStrategy centipedeMSZ100Tree (1 : Fin 2) = 100 := by
  simp [centipedeMSZ100Tree]

/-- The finite no-chance Arena prefix extracts to the corresponding
    perfect-information `GameTree`. -/
theorem centipedePrefixArena_extracts_tree :
    ExtensiveGame.ExtractsGameTree centipedePrefixArena
      centipedePrefixArena.init centipedePrefixTree := by
  change ExtensiveGame.ExtractsGameTree centipedePrefixArena
    PrefixState.root centipedePrefixTree
  unfold centipedePrefixTree centipedePrefixStop0Leaf
    centipedePrefixContinuationTree centipedePrefixStop1Leaf
    centipedePrefixContinue1Leaf
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
