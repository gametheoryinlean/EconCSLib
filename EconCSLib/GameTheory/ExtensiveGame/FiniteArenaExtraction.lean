/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Subgame
import EconCSLib.GameTheory.ExtensiveGame.GameTreeNE

/-!
# EconCSLib.GameTheory.ExtensiveGame.FiniteArenaExtraction

Interfaces for extracting finite no-chance Arena-style games into `GameTree`.

The general reverse bridge from `ExtensiveGame` to `GameTree` cannot be total:
the Arena API allows infinite state spaces, cycles, chance states, and histories
that merge.  This file records the assumptions needed for extraction and gives
small certified extraction constructors that can be extended case by case.

## Main definitions

* `ExtensiveGame.NoChance` — every nonterminal state has a strategic mover.
* `ExtensiveGame.TreeShapedFrom` — uniqueness of histories into a state.
* `ExtensiveGame.FiniteExtractable` — explicit assumption package for reverse
  extraction.
* `ExtensiveGame.ActionListComplete` — an explicit finite action enumeration at
  one state.
* `ExtensiveGame.ExtractsGameTree` — relational extraction from a state to a
  `GameTree`.
* `ExtensiveGame.extractTerminalGameTree` — certified extraction of a terminal
  state to a one-leaf `GameTree`.
* `ExtensiveGame.ExtractsGameTree.leaf_payoff` — extracted leaves preserve the
  Arena payoff vector.
* `ExtensiveGame.ExtractsGameTree.node_head_reachable` — the extracted head
  child is reached by one Arena transition.
-/

namespace ExtensiveGame

variable {N U : Type*} (G : ExtensiveGame N U)

/-- A weak tree-shapedness condition: any two paths from the root to the same
    state are equal as reachability proofs.

This is intentionally proof-valued.  Concrete finite extraction modules may
replace it with a computable predecessor/history representation. -/
def TreeShapedFrom (root : G.State) : Prop :=
  ∀ s : G.State, Subsingleton (Arena.Reachable G.toArena root s)

/-- Assumptions under which an Arena-style game can be extracted to a finite
    no-chance `GameTree`.  The actual recursive extraction is intentionally not
    bundled here; users provide a finite unfolding depth or well-founded child
    enumeration appropriate for their concrete game. -/
structure FiniteExtractable : Prop where
  state_finite : Nonempty (Fintype G.State)
  no_chance : G.NoChance
  tree_shaped : G.TreeShapedFrom G.init

/-- A nonempty action list `head :: tail` contains every available action at
    state `s`.  The list is an explicit finite enumeration supplied by the
    concrete game. -/
def ActionListComplete (s : G.State) (head : G.Action s) (tail : List (G.Action s)) :
    Prop :=
  ∀ a : G.Action s, a ∈ head :: tail

/- Relational extraction of an Arena-style no-chance extensive game state to a
    finite `GameTree`.

The relation is intentionally assumption-explicit: each decision node supplies a
complete nonempty action enumeration, a player owner, and extracted child trees
for exactly that action list. -/
mutual
  inductive ExtractsGameTree : G.State → GameTree N U → Prop where
    | leaf (s : G.State) (hs : G.isTerminal s) :
        ExtractsGameTree s (GameTree.Leaf (G.payoff s))
    | node (s : G.State) (i : N) (head : G.Action s) (tail : List (G.Action s))
        (headTree : GameTree N U) (tailTrees : List (GameTree N U))
        (hm : G.mover s = some i)
        (hcomplete : G.ActionListComplete s head tail)
        (hhead : ExtractsGameTree (G.next s head) headTree)
        (htail : ExtractsGameTreeList s tail tailTrees) :
        ExtractsGameTree s (GameTree.Node i headTree tailTrees)

  inductive ExtractsGameTreeList :
      (s : G.State) → List (G.Action s) → List (GameTree N U) → Prop where
    | nil (s : G.State) : ExtractsGameTreeList s [] []
    | cons (s : G.State) (head : G.Action s) (tail : List (G.Action s))
        (headTree : GameTree N U) (tailTrees : List (GameTree N U))
        (hhead : ExtractsGameTree (G.next s head) headTree)
        (htail : ExtractsGameTreeList s tail tailTrees) :
        ExtractsGameTreeList s (head :: tail) (headTree :: tailTrees)
end

/-- Terminal states extract to one-leaf `GameTree`s. -/
def extractTerminalGameTree (s : G.State) (_hs : G.isTerminal s) : GameTree N U :=
  GameTree.Leaf (G.payoff s)

theorem extractTerminal_payoff (s : G.State) (hs : G.isTerminal s) :
    G.extractTerminalGameTree s hs = GameTree.Leaf (G.payoff s) :=
  rfl

/-- The certified terminal-state extractor satisfies the relational extraction
interface. -/
theorem extractTerminal_extracts (s : G.State) (hs : G.isTerminal s) :
    ExtractsGameTree G s (G.extractTerminalGameTree s hs) := by
  rw [extractTerminal_payoff]
  exact ExtractsGameTree.leaf s hs

/-- If an Arena state extracts to a leaf, the leaf payoff is exactly the Arena
payoff at that state. -/
theorem ExtractsGameTree.leaf_payoff {s : G.State} {p : N → U}
    (h : ExtractsGameTree G s (GameTree.Leaf p)) :
    p = G.payoff s := by
  cases h
  rfl

/-- At an extracted decision node, the head child is reached by one Arena
transition and itself has an extracted subtree. -/
theorem ExtractsGameTree.node_head_reachable {s : G.State} {i : N}
    {headTree : GameTree N U} {tailTrees : List (GameTree N U)}
    (h : ExtractsGameTree G s (GameTree.Node i headTree tailTrees)) :
    ∃ head : G.Action s,
      Arena.Reachable G.toArena s (G.next s head) ∧
        ExtractsGameTree G (G.next s head) headTree := by
  cases h with
  | node s i head tail headTree tailTrees hm hcomplete hhead htail =>
      exact ⟨head, Arena.Reachable.step head (Arena.Reachable.refl _), hhead⟩

/-- On any extracted tree, root-scoped subgame perfection implies root Nash
equilibrium through the ordinary `GameTree` equilibrium API. -/
theorem ExtractsGameTree.spe_on_to_nash_at [TotalPreorder U]
    {s : G.State} {tree : GameTree N U}
    (_h : ExtractsGameTree G s tree) {σ : GameTree.Strategy N U}
    (hspe : GameTree.IsSubgamePerfectOn σ tree) :
    GameTree.IsNashAt σ tree :=
  hspe.toNashAt

end ExtensiveGame
