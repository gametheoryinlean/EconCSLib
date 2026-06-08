/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.GameTreeNE
import EconCSLib.GameTheory.StrategicGame.NashEquilibrium

/-!
# ExtensiveGame.GameTreeStrategicForm

Strategic-form extraction for finite perfect-information `GameTree` games.

The extracted normal-form game gives every player a complete contingent plan:
at each node context `(mover, head, tail)`, choose one of the available
children.  During play, the node's mover selects which player's plan is used.

## Main definitions

* `GameTree.PlayerStrategy` — one player's contingent plan on a `GameTree`.
* `GameTree.profileStrategy` — combine a normal-form profile into a global tree
  strategy.
* `GameTree.profileStrategy_surjective` — every global tree strategy is
  represented by some normal-form profile.
* `GameTree.optStrategyProfile` — the extracted normal-form profile induced by
  backward induction.
* `GameTree.toStrategicGame` — extracted pure normal-form game.

## Main results

* `toStrategicGame_nash_iff_isNashAt` — pure Nash in the extracted game is
  exactly root-scoped Nash in the original tree.
* `toStrategicGame_nash_toNashAt` / `IsNashAt.toStrategicGame_nash` — named
  directions of the pure Nash/root Nash equivalence.
* `exists_toStrategicGame_nash_iff_exists_isNashAt` — pure Nash existence in
  the extracted game is exactly root-scoped Nash existence in the tree.
* `toStrategicGame_nash_toSubgamePerfectOn_of_hasOnlyRootSubgames` — when the
  root has no proper subgames, strategic-form Nash already gives root-scoped SPE.
* `IsSubgamePerfectOn.toStrategicGame_nash` — root-scoped SPE induces a pure
  Nash equilibrium in the extracted strategic-form game.
* `IsSubgamePerfectOn.toStrategicGame_nash_of_subtree` — root-scoped SPE
  induces pure Nash in the extracted game of each subtree.
* `IsSubgamePerfectOn.exists_toStrategicGame_nash_of_subtree` — a tree-strategy
  SPE witness is represented by a pure Nash profile on each subtree.
* `isSubgamePerfectOn_iff_forall_subtree_toStrategicGame_nash` — root-scoped
  SPE is equivalent to strategic-form Nash at every extracted subtree.
* `exists_forall_subtree_toStrategicGame_nash_iff_exists_forall_subtree_isNashAt` —
  subtree-wise strategic-form Nash existence is equivalent to subtree-wise
  root Nash existence.
* `exists_forall_subtree_toStrategicGame_nash_iff_exists_isSubgamePerfectOn` —
  subtree-wise strategic-form Nash existence is equivalent to root-scoped SPE
  existence.
* `exists_toStrategicGame_nash_and_forall_properSubgame_isSubgamePerfectOn_iff_exists_isSubgamePerfectOn` —
  root strategic-form Nash plus proper-subgame SPE existence is equivalent to
  root-scoped SPE existence.
* `isSubgamePerfectOn_iff_toStrategicGame_nash_and_forall_properSubgame_isSubgamePerfectOn` —
  root-scoped SPE is root strategic-form Nash plus SPE on every proper subgame.
* `isSubgamePerfectOn_Node_iff_toStrategicGame_nash_and_children` — recursive
  node check using strategic-form Nash at the root and SPE on direct children.
* `IsSubgamePerfectOn.toStrategicGame_nash_and_head_tail` — bundled node
  decomposition into strategic-form root Nash plus head/tail SPE.
* `isSubgamePerfect_iff_forall_toStrategicGame_nash` — global SPE is
  equivalent to strategic-form Nash at every extracted root.
* `Kuhn_exists_toStrategicGame_nash` — the extracted strategic-form game has a
  pure Nash equilibrium, witnessed by the backward-induction strategy.
* `Kuhn_exists_toStrategicGame_nash_and_SPE_on_properSubgames` — one
  normal-form profile is root Nash and SPE on every proper subgame.
-/

namespace GameTree

variable {ι U : Type*}

/-- A single player's pure strategy in the normal form of a `GameTree`:
    a complete contingent plan choosing a child at every possible node. -/
def PlayerStrategy (ι U : Type*) : Type _ :=
  (m : ι) → (h : GameTree ι U) → (t : List (GameTree ι U)) →
    { c : GameTree ι U // c ∈ h :: t }

/-- Combine a normal-form profile into the global `GameTree.Strategy` used by
    the game-tree evaluator.  At each node, the mover's contingent plan is used. -/
def profileStrategy (σ : ι → PlayerStrategy ι U) : Strategy ι U :=
  fun m h t => σ m m h t

/-- A global tree strategy is recovered from the constant normal-form profile
    that assigns that complete contingent plan to every player. -/
@[simp]
theorem profileStrategy_const (τ : Strategy ι U) :
    profileStrategy (fun _ : ι => (τ : PlayerStrategy ι U)) = τ :=
  rfl

/-- Every global tree strategy is represented by some extracted normal-form
    profile. A constant profile containing the same complete contingent plan
    for every player is enough. -/
theorem profileStrategy_surjective :
    Function.Surjective (profileStrategy : (ι → PlayerStrategy ι U) → Strategy ι U) :=
  fun τ => ⟨fun _ : ι => (τ : PlayerStrategy ι U), profileStrategy_const τ⟩

/-- The normal-form profile induced by the canonical backward-induction
    strategy. Each player is assigned the same complete contingent plan
    `optStrategy`; at a node, `profileStrategy` then reads the mover's plan. -/
noncomputable def optStrategyProfile [TotalPreorder U] : ι → PlayerStrategy ι U :=
  fun _ => (optStrategy : PlayerStrategy ι U)

/-- Evaluating the backward-induction normal-form profile recovers the
    canonical backward-induction tree strategy. -/
@[simp]
theorem profileStrategy_optStrategyProfile [TotalPreorder U] :
    profileStrategy (optStrategyProfile : ι → PlayerStrategy ι U) =
      (optStrategy : Strategy ι U) :=
  rfl

variable [DecidableEq ι]

/-- The strategic-form extraction of a finite perfect-information tree. -/
noncomputable def toStrategicGame (g : GameTree ι U) : StrategicGame ι U where
  strategy := fun _ => PlayerStrategy ι U
  payoff σ i := outcome (profileStrategy σ) g i

/-- Replacing player `i`'s normal-form contingent plan produces an `i`-variant
    global tree strategy. -/
theorem profileStrategy_deviate_variant (σ : ι → PlayerStrategy ι U)
    (i : ι) (s' : PlayerStrategy ι U) :
    IVariant i (profileStrategy σ) (profileStrategy (Function.update σ i s')) := by
  intro m h t hmi
  simp [profileStrategy, hmi]

/-- Any global `i`-variant tree strategy can be represented by deviating player
    `i`'s normal-form contingent plan. -/
theorem profileStrategy_deviate_eq_of_variant (σ : ι → PlayerStrategy ι U)
    (i : ι) (τ : Strategy ι U) (hτ : IVariant i (profileStrategy σ) τ) :
    profileStrategy (Function.update σ i (τ : PlayerStrategy ι U)) = τ := by
  funext m h t
  by_cases hmi : m = i
  · subst hmi
    simp [profileStrategy]
  · simp [profileStrategy, hmi]
    exact hτ m h t hmi

variable [TotalPreorder U]

/-- Nash equilibrium in the extracted strategic-form game is exactly Nash
    equilibrium at the root of the original tree. -/
theorem toStrategicGame_nash_iff_isNashAt (g : GameTree ι U)
    (σ : (toStrategicGame g).Profile) :
    _root_.IsNashEquilibrium (toStrategicGame g) σ ↔ IsNashAt (profileStrategy σ) g := by
  constructor
  · intro hN i τ hτ
    have hdev := hN i (τ : PlayerStrategy ι U)
    simpa [toStrategicGame, IsBestResponse, StrategicGame.deviate,
      profileStrategy_deviate_eq_of_variant σ i τ hτ] using hdev
  · intro hN i s'
    exact hN i (profileStrategy (Function.update σ i s'))
      (profileStrategy_deviate_variant σ i s')

/-- Pure Nash equilibrium in the extracted strategic-form game gives root
    Nash equilibrium for the induced tree strategy. -/
theorem toStrategicGame_nash_toNashAt {g : GameTree ι U}
    {σ : (toStrategicGame g).Profile}
    (hnash : _root_.IsNashEquilibrium (toStrategicGame g) σ) :
    IsNashAt (profileStrategy σ) g :=
  (toStrategicGame_nash_iff_isNashAt g σ).mp hnash

/-- Root Nash equilibrium for a represented tree strategy gives pure Nash
    equilibrium in the extracted strategic-form game. -/
theorem IsNashAt.toStrategicGame_nash {g : GameTree ι U}
    {σ : (toStrategicGame g).Profile}
    (hnash : IsNashAt (profileStrategy σ) g) :
    _root_.IsNashEquilibrium (toStrategicGame g) σ :=
  (toStrategicGame_nash_iff_isNashAt g σ).mpr hnash

/-- Existence of a pure Nash equilibrium in the extracted strategic-form game
    is equivalent to existence of a root-scoped Nash equilibrium in the
    original game tree. -/
theorem exists_toStrategicGame_nash_iff_exists_isNashAt (g : GameTree ι U) :
    (∃ σ : (toStrategicGame g).Profile,
      _root_.IsNashEquilibrium (toStrategicGame g) σ) ↔
      ∃ τ : Strategy ι U, IsNashAt τ g := by
  constructor
  · rintro ⟨σ, hnash⟩
    exact ⟨profileStrategy σ, (toStrategicGame_nash_iff_isNashAt g σ).mp hnash⟩
  · rintro ⟨τ, hnash⟩
    refine ⟨fun _ : ι => (τ : PlayerStrategy ι U), ?_⟩
    exact (toStrategicGame_nash_iff_isNashAt g _).mpr (by
      simpa using hnash)

/-- A root-scoped Nash equilibrium in the game tree gives a pure Nash
    equilibrium in the extracted strategic-form game by using the same complete
    contingent plan for every player. -/
theorem IsNashAt.exists_toStrategicGame_nash
    {g : GameTree ι U} {τ : Strategy ι U} (hnash : IsNashAt τ g) :
    ∃ σ : (toStrategicGame g).Profile,
      _root_.IsNashEquilibrium (toStrategicGame g) σ :=
  (exists_toStrategicGame_nash_iff_exists_isNashAt g).mpr ⟨τ, hnash⟩

/-- A root-scoped subgame-perfect tree strategy gives a represented pure Nash
    profile in the extracted strategic-form game at the same root. -/
theorem IsSubgamePerfectOn.exists_toStrategicGame_nash
    {g : GameTree ι U} {τ : Strategy ι U} (hspe : IsSubgamePerfectOn τ g) :
    ∃ σ : (toStrategicGame g).Profile,
      _root_.IsNashEquilibrium (toStrategicGame g) σ :=
  hspe.toNashAt.exists_toStrategicGame_nash

/-- A root-scoped subgame-perfect tree strategy gives a represented pure Nash
    profile in the extracted strategic-form game of any subtree. -/
theorem IsSubgamePerfectOn.exists_toStrategicGame_nash_of_subtree
    {g s : GameTree ι U} {τ : Strategy ι U}
    (hspe : IsSubgamePerfectOn τ g) (hsub : Subtree s g) :
    ∃ σ : (toStrategicGame s).Profile,
      _root_.IsNashEquilibrium (toStrategicGame s) σ :=
  (hspe.toNashAt_of_subtree hsub).exists_toStrategicGame_nash

/-- A root-scoped subgame-perfect tree strategy gives a represented pure Nash
    profile in the extracted strategic-form game of any proper subgame. -/
theorem IsSubgamePerfectOn.exists_toStrategicGame_nash_of_properSubgame
    {g s : GameTree ι U} {τ : Strategy ι U}
    (hspe : IsSubgamePerfectOn τ g) (hproper : ProperSubgame s g) :
    ∃ σ : (toStrategicGame s).Profile,
      _root_.IsNashEquilibrium (toStrategicGame s) σ :=
  hspe.exists_toStrategicGame_nash_of_subtree hproper.toSubtree

/-- The extracted strategic-form game of a terminal leaf has a pure Nash
    equilibrium. -/
theorem exists_toStrategicGame_nash_Leaf (p : ι → U) :
    ∃ σ : (toStrategicGame (Leaf p : GameTree ι U)).Profile,
      _root_.IsNashEquilibrium (toStrategicGame (Leaf p : GameTree ι U)) σ :=
  (isNashAt_Leaf (optStrategy : Strategy ι U) p).exists_toStrategicGame_nash

/-- On a terminal leaf, pure Nash existence in the extracted strategic-form
    game is equivalent to root-scoped subgame-perfect existence. -/
theorem exists_toStrategicGame_nash_Leaf_iff_exists_isSubgamePerfectOn
    (p : ι → U) :
    (∃ σ : (toStrategicGame (Leaf p : GameTree ι U)).Profile,
      _root_.IsNashEquilibrium (toStrategicGame (Leaf p : GameTree ι U)) σ) ↔
      ∃ τ : Strategy ι U, IsSubgamePerfectOn τ (Leaf p) := by
  rw [exists_toStrategicGame_nash_iff_exists_isNashAt]
  exact (exists_isSubgamePerfectOn_Leaf_iff_exists_isNashAt p).symm

/-- If a finite perfect-information root has no proper subgames, then pure
    Nash equilibrium in its extracted strategic-form game already gives
    root-scoped subgame perfection. This is the strategic-form version of the
    pure finite-tree form of MSZ Theorem 7.4. -/
theorem toStrategicGame_nash_toSubgamePerfectOn_of_hasOnlyRootSubgames
    {g : GameTree ι U} {σ : (toStrategicGame g).Profile}
    (hnash : _root_.IsNashEquilibrium (toStrategicGame g) σ)
    (hsubgames : HasOnlyRootSubgames g) :
    IsSubgamePerfectOn (profileStrategy σ) g :=
  ((toStrategicGame_nash_iff_isNashAt g σ).mp hnash).toSubgamePerfectOn_of_hasOnlyRootSubgames
    hsubgames

/-- On a finite perfect-information root with no proper subgames, pure Nash in
    the extracted strategic-form game is equivalent to root-scoped subgame
    perfection. This is the strategic-form iff form of MSZ Theorem 7.4. -/
theorem isSubgamePerfectOn_iff_toStrategicGame_nash_of_hasOnlyRootSubgames
    {g : GameTree ι U} (σ : (toStrategicGame g).Profile)
    (hsubgames : HasOnlyRootSubgames g) :
    IsSubgamePerfectOn (profileStrategy σ) g ↔
      _root_.IsNashEquilibrium (toStrategicGame g) σ := by
  constructor
  · intro hspe
    exact (toStrategicGame_nash_iff_isNashAt g σ).mpr hspe.toNashAt
  · intro hnash
    exact toStrategicGame_nash_toSubgamePerfectOn_of_hasOnlyRootSubgames hnash
      hsubgames

/-- If the root has no proper subgame, pure Nash in the extracted
    strategic-form game is equivalent to root-scoped subgame perfection. -/
theorem isSubgamePerfectOn_iff_toStrategicGame_nash_of_no_properSubgame
    {g : GameTree ι U} (σ : (toStrategicGame g).Profile)
    (hnoProper : ¬ ∃ s : GameTree ι U, ProperSubgame s g) :
    IsSubgamePerfectOn (profileStrategy σ) g ↔
      _root_.IsNashEquilibrium (toStrategicGame g) σ :=
  isSubgamePerfectOn_iff_toStrategicGame_nash_of_hasOnlyRootSubgames σ
    ((hasOnlyRootSubgames_iff_no_properSubgame g).mpr hnoProper)

/-- Root-scoped subgame perfection in a finite perfect-information tree induces
    a pure Nash equilibrium in the extracted strategic-form game. -/
theorem IsSubgamePerfectOn.toStrategicGame_nash
    {g : GameTree ι U} {σ : (toStrategicGame g).Profile}
    (hspe : IsSubgamePerfectOn (profileStrategy σ) g) :
    _root_.IsNashEquilibrium (toStrategicGame g) σ :=
  (toStrategicGame_nash_iff_isNashAt g σ).mpr hspe.toNashAt

/-- Global subgame perfection induces a pure Nash equilibrium in the extracted
    strategic-form game for every finite perfect-information root. -/
theorem IsSubgamePerfect.toStrategicGame_nash
    {g : GameTree ι U} {σ : (toStrategicGame g).Profile}
    (hspe : IsSubgamePerfect (profileStrategy σ)) :
    _root_.IsNashEquilibrium (toStrategicGame g) σ :=
  (hspe.toSubgamePerfectOn g).toStrategicGame_nash

set_option linter.unusedSectionVars false in
/-- If a global subgame-perfect tree strategy exists, then it is represented by
    some normal-form profile. -/
theorem exists_profileStrategy_isSubgamePerfect_of_exists_isSubgamePerfect
    (hexists : ∃ τ : Strategy ι U, IsSubgamePerfect τ) :
    ∃ σ : ι → PlayerStrategy ι U, IsSubgamePerfect (profileStrategy σ) := by
  rcases hexists with ⟨τ, hspe⟩
  exact ⟨fun _ : ι => (τ : PlayerStrategy ι U), by simpa using hspe⟩

set_option linter.unusedSectionVars false in
/-- Existence of a global subgame-perfect tree strategy is equivalent to
    existence of a normal-form profile whose induced tree strategy is globally
    subgame-perfect. -/
theorem exists_profileStrategy_isSubgamePerfect_iff_exists_isSubgamePerfect :
    (∃ σ : ι → PlayerStrategy ι U, IsSubgamePerfect (profileStrategy σ)) ↔
      ∃ τ : Strategy ι U, IsSubgamePerfect τ := by
  constructor
  · rintro ⟨σ, hspe⟩
    exact ⟨profileStrategy σ, hspe⟩
  · exact exists_profileStrategy_isSubgamePerfect_of_exists_isSubgamePerfect

set_option linter.unusedSectionVars false in
/-- If a root-scoped subgame-perfect tree strategy exists, then it is
    represented by some normal-form profile. -/
theorem exists_profileStrategy_isSubgamePerfectOn_of_exists_isSubgamePerfectOn
    (g : GameTree ι U)
    (hexists : ∃ τ : Strategy ι U, IsSubgamePerfectOn τ g) :
    ∃ σ : (toStrategicGame g).Profile,
      IsSubgamePerfectOn (profileStrategy σ) g := by
  rcases hexists with ⟨τ, hspe⟩
  exact ⟨fun _ : ι => (τ : PlayerStrategy ι U), by simpa using hspe⟩

set_option linter.unusedSectionVars false in
/-- Existence of root-scoped subgame perfection in the tree is equivalent to
    existence of a normal-form profile whose induced tree strategy is
    root-scoped subgame-perfect. -/
theorem exists_profileStrategy_isSubgamePerfectOn_iff_exists_isSubgamePerfectOn
    (g : GameTree ι U) :
    (∃ σ : (toStrategicGame g).Profile,
      IsSubgamePerfectOn (profileStrategy σ) g) ↔
      ∃ τ : Strategy ι U, IsSubgamePerfectOn τ g := by
  constructor
  · rintro ⟨σ, hspe⟩
    exact ⟨profileStrategy σ, hspe⟩
  · exact exists_profileStrategy_isSubgamePerfectOn_of_exists_isSubgamePerfectOn g

/-- A global subgame-perfect strategy induces a pure Nash equilibrium in the
    extracted strategic-form game of every finite perfect-information root. -/
theorem IsSubgamePerfect.forall_toStrategicGame_nash
    {σ : ι → PlayerStrategy ι U} (hspe : IsSubgamePerfect (profileStrategy σ)) :
    ∀ g : GameTree ι U, _root_.IsNashEquilibrium (toStrategicGame g) σ :=
  fun g => hspe.toStrategicGame_nash (g := g)

/-- Global subgame perfection is equivalent to pure Nash equilibrium in every
    extracted strategic-form game. -/
theorem isSubgamePerfect_iff_forall_toStrategicGame_nash
    (σ : ι → PlayerStrategy ι U) :
    IsSubgamePerfect (profileStrategy σ) ↔
      ∀ g : GameTree ι U, _root_.IsNashEquilibrium (toStrategicGame g) σ := by
  constructor
  · intro hspe
    exact hspe.forall_toStrategicGame_nash
  · intro hnash
    exact IsSubgamePerfect.of_forall_isNashAt
      (fun g => (toStrategicGame_nash_iff_isNashAt g σ).mp (hnash g))

/-- Existence of one normal-form profile that is pure Nash in every extracted
    strategic-form game is equivalent to existence of a global
    subgame-perfect tree strategy. -/
theorem exists_forall_toStrategicGame_nash_iff_exists_isSubgamePerfect :
    (∃ σ : ι → PlayerStrategy ι U,
      ∀ g : GameTree ι U, _root_.IsNashEquilibrium (toStrategicGame g) σ) ↔
      ∃ τ : Strategy ι U, IsSubgamePerfect τ := by
  constructor
  · rintro ⟨σ, hnash⟩
    exact ⟨profileStrategy σ,
      IsSubgamePerfect.of_forall_isNashAt
        (fun g => (toStrategicGame_nash_iff_isNashAt g σ).mp (hnash g))⟩
  · rintro ⟨τ, hspe⟩
    refine ⟨fun _ : ι => (τ : PlayerStrategy ι U), ?_⟩
    intro g
    exact (toStrategicGame_nash_iff_isNashAt g _).mpr (by
      simpa using hspe.toNashAt g)

/-- Root-scoped subgame perfection gives pure Nash equilibrium in the extracted
    strategic-form game of every subtree of the root. -/
theorem IsSubgamePerfectOn.forall_subtree_toStrategicGame_nash
    {g : GameTree ι U} {σ : (toStrategicGame g).Profile}
    (hspe : IsSubgamePerfectOn (profileStrategy σ) g) :
    ∀ s : GameTree ι U, Subtree s g →
      _root_.IsNashEquilibrium (toStrategicGame s) σ :=
  fun s hsub =>
    (toStrategicGame_nash_iff_isNashAt s σ).mpr
      (hspe.toNashAt_of_subtree hsub)

/-- Root-scoped subgame perfection gives pure Nash equilibrium in the
    extracted strategic-form game of any fixed subtree of the root. -/
theorem IsSubgamePerfectOn.toStrategicGame_nash_of_subtree
    {g s : GameTree ι U} {σ : (toStrategicGame g).Profile}
    (hspe : IsSubgamePerfectOn (profileStrategy σ) g) (hsub : Subtree s g) :
    _root_.IsNashEquilibrium (toStrategicGame s) σ :=
  (toStrategicGame_nash_iff_isNashAt s σ).mpr
    (hspe.toNashAt_of_subtree hsub)

/-- Root-scoped subgame perfection gives pure Nash equilibrium in the extracted
    strategic-form game of every proper subgame of the root. -/
theorem IsSubgamePerfectOn.forall_properSubgame_toStrategicGame_nash
    {g : GameTree ι U} {σ : (toStrategicGame g).Profile}
    (hspe : IsSubgamePerfectOn (profileStrategy σ) g) :
    ∀ s : GameTree ι U, ProperSubgame s g →
      _root_.IsNashEquilibrium (toStrategicGame s) σ :=
  fun s hproper =>
    (toStrategicGame_nash_iff_isNashAt s σ).mpr
      (hspe.toNashAt_of_properSubgame hproper)

/-- Root-scoped subgame perfection gives pure Nash equilibrium in the
    extracted strategic-form game of any fixed proper subgame of the root. -/
theorem IsSubgamePerfectOn.toStrategicGame_nash_of_properSubgame
    {g s : GameTree ι U} {σ : (toStrategicGame g).Profile}
    (hspe : IsSubgamePerfectOn (profileStrategy σ) g)
    (hproper : ProperSubgame s g) :
    _root_.IsNashEquilibrium (toStrategicGame s) σ :=
  hspe.toStrategicGame_nash_of_subtree hproper.toSubtree

/-- Root-scoped subgame perfection gives strategic-form root Nash together
    with strategic-form Nash at every proper subgame. -/
theorem IsSubgamePerfectOn.toStrategicGame_nash_and_forall_properSubgame_toStrategicGame_nash
    {g : GameTree ι U} {σ : (toStrategicGame g).Profile}
    (hspe : IsSubgamePerfectOn (profileStrategy σ) g) :
    _root_.IsNashEquilibrium (toStrategicGame g) σ ∧
      ∀ s : GameTree ι U, ProperSubgame s g →
        _root_.IsNashEquilibrium (toStrategicGame s) σ :=
  ⟨hspe.toStrategicGame_nash, hspe.forall_properSubgame_toStrategicGame_nash⟩

/-- Root-scoped subgame perfection gives strategic-form root Nash together
    with root-scoped subgame perfection on every proper subgame. -/
theorem IsSubgamePerfectOn.toStrategicGame_nash_and_forall_properSubgame_isSubgamePerfectOn
    {g : GameTree ι U} {σ : (toStrategicGame g).Profile}
    (hspe : IsSubgamePerfectOn (profileStrategy σ) g) :
    _root_.IsNashEquilibrium (toStrategicGame g) σ ∧
      ∀ s : GameTree ι U, ProperSubgame s g →
        IsSubgamePerfectOn (profileStrategy σ) s :=
  ⟨hspe.toStrategicGame_nash, hspe.forall_properSubgame_isSubgamePerfectOn⟩

/-- Root-scoped subgame perfection at a node gives pure Nash equilibrium in
    the extracted strategic-form game of its head child. -/
theorem IsSubgamePerfectOn.toStrategicGame_nash_head
    {σ : ι → PlayerStrategy ι U}
    {m : ι} {h : GameTree ι U} {t : List (GameTree ι U)}
    (hspe : IsSubgamePerfectOn (profileStrategy σ) (Node m h t)) :
    _root_.IsNashEquilibrium (toStrategicGame h) σ :=
  (toStrategicGame_nash_iff_isNashAt h σ).mpr hspe.toNashAt_head

/-- Root-scoped subgame perfection at a node gives pure Nash equilibrium in
    the extracted strategic-form game of every tail child. -/
theorem IsSubgamePerfectOn.toStrategicGame_nash_tail_mem
    {σ : ι → PlayerStrategy ι U}
    {m : ι} {h : GameTree ι U} {t : List (GameTree ι U)}
    {c : GameTree ι U}
    (hspe : IsSubgamePerfectOn (profileStrategy σ) (Node m h t)) (hmem : c ∈ t) :
    _root_.IsNashEquilibrium (toStrategicGame c) σ :=
  (toStrategicGame_nash_iff_isNashAt c σ).mpr
    (hspe.toNashAt_tail_mem hmem)

/-- Root-scoped subgame perfection at a node gives pure Nash equilibrium in
    the extracted strategic-form game of every direct child. -/
theorem IsSubgamePerfectOn.toStrategicGame_nash_child_mem
    {σ : ι → PlayerStrategy ι U}
    {m : ι} {h : GameTree ι U} {t : List (GameTree ι U)}
    {c : GameTree ι U}
    (hspe : IsSubgamePerfectOn (profileStrategy σ) (Node m h t)) (hmem : c ∈ h :: t) :
    _root_.IsNashEquilibrium (toStrategicGame c) σ :=
  (toStrategicGame_nash_iff_isNashAt c σ).mpr
    (hspe.toNashAt_child_mem hmem)

/-- Root-scoped subgame perfection at a node gives pure Nash equilibrium in
    the extracted strategic-form game of every child in the public `children`
    list. -/
theorem IsSubgamePerfectOn.toStrategicGame_nash_child
    {σ : ι → PlayerStrategy ι U}
    {m : ι} {h : GameTree ι U} {t : List (GameTree ι U)}
    {c : GameTree ι U}
    (hspe : IsSubgamePerfectOn (profileStrategy σ) (Node m h t))
    (hmem : c ∈ children (Node m h t)) :
    _root_.IsNashEquilibrium (toStrategicGame c) σ :=
  (toStrategicGame_nash_iff_isNashAt c σ).mpr
    (hspe.toNashAt_child hmem)

/-- Existence of one normal-form profile that is pure Nash in every extracted
    subtree game is equivalent to existence of one tree strategy that is
    root-scoped Nash at every subtree. -/
theorem exists_forall_subtree_toStrategicGame_nash_iff_exists_forall_subtree_isNashAt
    (g : GameTree ι U) :
    (∃ σ : ι → PlayerStrategy ι U,
      ∀ s : GameTree ι U, Subtree s g →
        _root_.IsNashEquilibrium (toStrategicGame s) σ) ↔
      ∃ τ : Strategy ι U,
        ∀ s : GameTree ι U, Subtree s g → IsNashAt τ s := by
  constructor
  · rintro ⟨σ, hnash⟩
    exact ⟨profileStrategy σ,
      fun s hsub => (toStrategicGame_nash_iff_isNashAt s σ).mp (hnash s hsub)⟩
  · rintro ⟨τ, hnash⟩
    refine ⟨fun _ : ι => (τ : PlayerStrategy ι U), ?_⟩
    intro s hsub
    exact (toStrategicGame_nash_iff_isNashAt s _).mpr (by
      simpa using hnash s hsub)

/-- Existence of one normal-form profile that is pure Nash in every extracted
    proper-subgame game is equivalent to existence of one tree strategy that is
    root-scoped Nash at every proper subgame. -/
theorem exists_forall_properSubgame_toStrategicGame_nash_iff_exists_forall_properSubgame_isNashAt
    (g : GameTree ι U) :
    (∃ σ : ι → PlayerStrategy ι U,
      ∀ s : GameTree ι U, ProperSubgame s g →
        _root_.IsNashEquilibrium (toStrategicGame s) σ) ↔
      ∃ τ : Strategy ι U,
        ∀ s : GameTree ι U, ProperSubgame s g → IsNashAt τ s := by
  constructor
  · rintro ⟨σ, hnash⟩
    exact ⟨profileStrategy σ,
      fun s hproper =>
        (toStrategicGame_nash_iff_isNashAt s σ).mp (hnash s hproper)⟩
  · rintro ⟨τ, hnash⟩
    refine ⟨fun _ : ι => (τ : PlayerStrategy ι U), ?_⟩
    intro s hproper
    exact (toStrategicGame_nash_iff_isNashAt s _).mpr (by
      simpa using hnash s hproper)

/-- Existence of one normal-form profile that is pure Nash in every extracted
    subtree game is equivalent to existence of a root-scoped subgame-perfect
    tree strategy at the original root. -/
theorem exists_forall_subtree_toStrategicGame_nash_iff_exists_isSubgamePerfectOn
    (g : GameTree ι U) :
    (∃ σ : ι → PlayerStrategy ι U,
      ∀ s : GameTree ι U, Subtree s g →
        _root_.IsNashEquilibrium (toStrategicGame s) σ) ↔
      ∃ τ : Strategy ι U, IsSubgamePerfectOn τ g := by
  rw [exists_forall_subtree_toStrategicGame_nash_iff_exists_forall_subtree_isNashAt]
  constructor
  · rintro ⟨τ, hnash⟩
    exact ⟨τ, IsNashAt.toSubgamePerfectOn_of_forall_subtree_isNashAt hnash⟩
  · rintro ⟨τ, hspe⟩
    exact ⟨τ, hspe.forall_subtree_isNashAt⟩

/-- Existence of a root Nash equilibrium together with pure Nash equilibrium in
    every extracted proper-subgame game is equivalent to existence of a
    root-scoped subgame-perfect tree strategy. -/
theorem exists_toStrategicGame_nash_and_forall_properSubgame_toStrategicGame_nash_iff_exists_isSubgamePerfectOn
    (g : GameTree ι U) :
    (∃ σ : ι → PlayerStrategy ι U,
      _root_.IsNashEquilibrium (toStrategicGame g) σ ∧
        ∀ s : GameTree ι U, ProperSubgame s g →
          _root_.IsNashEquilibrium (toStrategicGame s) σ) ↔
      ∃ τ : Strategy ι U, IsSubgamePerfectOn τ g := by
  constructor
  · rintro ⟨σ, hnash, hproper⟩
    refine ⟨profileStrategy σ, ?_⟩
    exact IsNashAt.toSubgamePerfectOn_of_forall_properSubgame_isNashAt
      ((toStrategicGame_nash_iff_isNashAt g σ).mp hnash)
      (fun s hs => (toStrategicGame_nash_iff_isNashAt s σ).mp (hproper s hs))
  · rintro ⟨τ, hspe⟩
    refine ⟨fun _ : ι => (τ : PlayerStrategy ι U), ?_, ?_⟩
    · exact (toStrategicGame_nash_iff_isNashAt g _).mpr (by
        simpa using hspe.toNashAt)
    · intro s hs
      exact (toStrategicGame_nash_iff_isNashAt s _).mpr (by
        simpa using hspe.toNashAt_of_properSubgame hs)

/-- Existence of a root Nash equilibrium in the extracted strategic-form game
    together with root-scoped SPE on every proper subgame is equivalent to
    existence of a root-scoped subgame-perfect tree strategy. -/
theorem exists_toStrategicGame_nash_and_forall_properSubgame_isSubgamePerfectOn_iff_exists_isSubgamePerfectOn
    (g : GameTree ι U) :
    (∃ σ : ι → PlayerStrategy ι U,
      _root_.IsNashEquilibrium (toStrategicGame g) σ ∧
        ∀ s : GameTree ι U, ProperSubgame s g →
          IsSubgamePerfectOn (profileStrategy σ) s) ↔
      ∃ τ : Strategy ι U, IsSubgamePerfectOn τ g := by
  constructor
  · rintro ⟨σ, hnash, hproper⟩
    exact ⟨profileStrategy σ,
      IsNashAt.toSubgamePerfectOn_of_forall_properSubgame_isSubgamePerfectOn
        ((toStrategicGame_nash_iff_isNashAt g σ).mp hnash) hproper⟩
  · rintro ⟨τ, hspe⟩
    refine ⟨fun _ : ι => (τ : PlayerStrategy ι U), ?_, ?_⟩
    · exact (toStrategicGame_nash_iff_isNashAt g _).mpr (by
        simpa using hspe.toNashAt)
    · intro s hs
      simpa using hspe.of_properSubgame hs

/-- Pure Nash equilibrium in the extracted strategic-form game of every
    subtree gives root-scoped subgame perfection. -/
theorem toSubgamePerfectOn_of_forall_subtree_toStrategicGame_nash
    {g : GameTree ι U} {σ : ι → PlayerStrategy ι U}
    (hnash : ∀ s : GameTree ι U, Subtree s g →
      _root_.IsNashEquilibrium (toStrategicGame s) σ) :
    IsSubgamePerfectOn (profileStrategy σ) g :=
  IsNashAt.toSubgamePerfectOn_of_forall_subtree_isNashAt
    (fun s hsub => (toStrategicGame_nash_iff_isNashAt s σ).mp (hnash s hsub))

/-- Pure Nash equilibrium in the extracted strategic-form game of the root and
    every proper subgame gives root-scoped subgame perfection. -/
theorem toSubgamePerfectOn_of_toStrategicGame_nash_and_forall_properSubgame_toStrategicGame_nash
    {g : GameTree ι U} {σ : ι → PlayerStrategy ι U}
    (hnash : _root_.IsNashEquilibrium (toStrategicGame g) σ)
    (hproper : ∀ s : GameTree ι U, ProperSubgame s g →
      _root_.IsNashEquilibrium (toStrategicGame s) σ) :
    IsSubgamePerfectOn (profileStrategy σ) g :=
  IsNashAt.toSubgamePerfectOn_of_forall_properSubgame_isNashAt
    ((toStrategicGame_nash_iff_isNashAt g σ).mp hnash)
    (fun s hs => (toStrategicGame_nash_iff_isNashAt s σ).mp (hproper s hs))

/-- Pure Nash equilibrium in the extracted strategic-form root game, together
    with root-scoped subgame perfection on every proper subgame, gives
    root-scoped subgame perfection. -/
theorem toSubgamePerfectOn_of_toStrategicGame_nash_and_forall_properSubgame_isSubgamePerfectOn
    {g : GameTree ι U} {σ : ι → PlayerStrategy ι U}
    (hnash : _root_.IsNashEquilibrium (toStrategicGame g) σ)
    (hproper : ∀ s : GameTree ι U, ProperSubgame s g →
      IsSubgamePerfectOn (profileStrategy σ) s) :
    IsSubgamePerfectOn (profileStrategy σ) g :=
  IsNashAt.toSubgamePerfectOn_of_forall_properSubgame_isSubgamePerfectOn
    ((toStrategicGame_nash_iff_isNashAt g σ).mp hnash) hproper

/-- Root-scoped subgame perfection is equivalent to pure Nash equilibrium in
    the extracted strategic-form game of every subtree. -/
theorem isSubgamePerfectOn_iff_forall_subtree_toStrategicGame_nash
    {g : GameTree ι U} (σ : (toStrategicGame g).Profile) :
    IsSubgamePerfectOn (profileStrategy σ) g ↔
      ∀ s : GameTree ι U, Subtree s g →
        _root_.IsNashEquilibrium (toStrategicGame s) σ := by
  constructor
  · intro hspe
    exact hspe.forall_subtree_toStrategicGame_nash
  · intro hnash
    exact toSubgamePerfectOn_of_forall_subtree_toStrategicGame_nash hnash

/-- Root-scoped subgame perfection is equivalent to pure Nash equilibrium in
    the extracted strategic-form game at the root and at every proper subgame. -/
theorem isSubgamePerfectOn_iff_toStrategicGame_nash_and_forall_properSubgame_toStrategicGame_nash
    {g : GameTree ι U} (σ : (toStrategicGame g).Profile) :
    IsSubgamePerfectOn (profileStrategy σ) g ↔
      _root_.IsNashEquilibrium (toStrategicGame g) σ ∧
        ∀ s : GameTree ι U, ProperSubgame s g →
          _root_.IsNashEquilibrium (toStrategicGame s) σ := by
  constructor
  · intro hspe
    exact ⟨hspe.toStrategicGame_nash,
      hspe.forall_properSubgame_toStrategicGame_nash⟩
  · rintro ⟨hnash, hproper⟩
    exact
      toSubgamePerfectOn_of_toStrategicGame_nash_and_forall_properSubgame_toStrategicGame_nash
        hnash hproper

/-- Root-scoped subgame perfection is equivalent to pure Nash equilibrium in
    the extracted strategic-form game at the root, together with root-scoped
    subgame perfection on every proper subgame. -/
theorem isSubgamePerfectOn_iff_toStrategicGame_nash_and_forall_properSubgame_isSubgamePerfectOn
    {g : GameTree ι U} (σ : (toStrategicGame g).Profile) :
    IsSubgamePerfectOn (profileStrategy σ) g ↔
      _root_.IsNashEquilibrium (toStrategicGame g) σ ∧
        ∀ s : GameTree ι U, ProperSubgame s g →
          IsSubgamePerfectOn (profileStrategy σ) s := by
  constructor
  · intro hspe
    exact hspe.toStrategicGame_nash_and_forall_properSubgame_isSubgamePerfectOn
  · rintro ⟨hnash, hproper⟩
    exact
      toSubgamePerfectOn_of_toStrategicGame_nash_and_forall_properSubgame_isSubgamePerfectOn
        hnash hproper

/-- Root-scoped subgame perfection at a nonterminal node can be checked by
    pure Nash equilibrium in the extracted strategic-form game of the node,
    plus root-scoped subgame perfection on the head child and every tail
    child. -/
theorem isSubgamePerfectOn_Node_iff_toStrategicGame_nash_and_head_tail
    {σ : ι → PlayerStrategy ι U}
    {m : ι} {h : GameTree ι U} {t : List (GameTree ι U)} :
    IsSubgamePerfectOn (profileStrategy σ) (Node m h t) ↔
      _root_.IsNashEquilibrium (toStrategicGame (Node m h t)) σ ∧
        IsSubgamePerfectOn (profileStrategy σ) h ∧
          ∀ c ∈ t, IsSubgamePerfectOn (profileStrategy σ) c := by
  rw [isSubgamePerfectOn_Node_iff]
  constructor
  · rintro ⟨hnash, hhead, htail⟩
    exact ⟨(toStrategicGame_nash_iff_isNashAt (Node m h t) σ).mpr hnash,
      hhead, htail⟩
  · rintro ⟨hnash, hhead, htail⟩
    exact ⟨(toStrategicGame_nash_iff_isNashAt (Node m h t) σ).mp hnash,
      hhead, htail⟩

/-- Root-scoped subgame perfection at a nonterminal node gives pure Nash in the
    extracted strategic-form game of the node, together with root-scoped
    subgame perfection on the head child and every tail child. -/
theorem IsSubgamePerfectOn.toStrategicGame_nash_and_head_tail
    {σ : ι → PlayerStrategy ι U}
    {m : ι} {h : GameTree ι U} {t : List (GameTree ι U)}
    (hspe : IsSubgamePerfectOn (profileStrategy σ) (Node m h t)) :
    _root_.IsNashEquilibrium (toStrategicGame (Node m h t)) σ ∧
      IsSubgamePerfectOn (profileStrategy σ) h ∧
        ∀ c ∈ t, IsSubgamePerfectOn (profileStrategy σ) c :=
  (isSubgamePerfectOn_Node_iff_toStrategicGame_nash_and_head_tail).mp hspe

/-- Root-scoped subgame perfection at a nonterminal node can be checked by
    pure Nash equilibrium in the extracted strategic-form game of the node,
    plus root-scoped subgame perfection on every direct child. -/
theorem isSubgamePerfectOn_Node_iff_toStrategicGame_nash_and_children
    {σ : ι → PlayerStrategy ι U}
    {m : ι} {h : GameTree ι U} {t : List (GameTree ι U)} :
    IsSubgamePerfectOn (profileStrategy σ) (Node m h t) ↔
      _root_.IsNashEquilibrium (toStrategicGame (Node m h t)) σ ∧
        ∀ c ∈ children (Node m h t), IsSubgamePerfectOn (profileStrategy σ) c := by
  rw [isSubgamePerfectOn_Node_iff_children]
  constructor
  · rintro ⟨hnash, hchildren⟩
    exact ⟨(toStrategicGame_nash_iff_isNashAt (Node m h t) σ).mpr hnash,
      hchildren⟩
  · rintro ⟨hnash, hchildren⟩
    exact ⟨(toStrategicGame_nash_iff_isNashAt (Node m h t) σ).mp hnash,
      hchildren⟩

/-- Root-scoped subgame perfection at a nonterminal node gives pure Nash in the
    extracted strategic-form game of the node, together with root-scoped
    subgame perfection on every child in the public `children` list. -/
theorem IsSubgamePerfectOn.toStrategicGame_nash_and_children
    {σ : ι → PlayerStrategy ι U}
    {m : ι} {h : GameTree ι U} {t : List (GameTree ι U)}
    (hspe : IsSubgamePerfectOn (profileStrategy σ) (Node m h t)) :
    _root_.IsNashEquilibrium (toStrategicGame (Node m h t)) σ ∧
      ∀ c ∈ children (Node m h t), IsSubgamePerfectOn (profileStrategy σ) c :=
  (isSubgamePerfectOn_Node_iff_toStrategicGame_nash_and_children).mp hspe

/-- Pure Nash equilibrium in the extracted strategic-form game of a
    nonterminal node, together with root-scoped subgame perfection on every
    direct child, gives root-scoped subgame perfection at the node. -/
theorem toStrategicGame_nash_toSubgamePerfectOn_Node_of_children
    {σ : ι → PlayerStrategy ι U}
    {m : ι} {h : GameTree ι U} {t : List (GameTree ι U)}
    (hnash : _root_.IsNashEquilibrium (toStrategicGame (Node m h t)) σ)
    (hchildren :
      ∀ c ∈ children (Node m h t), IsSubgamePerfectOn (profileStrategy σ) c) :
    IsSubgamePerfectOn (profileStrategy σ) (Node m h t) :=
  (isSubgamePerfectOn_Node_iff_toStrategicGame_nash_and_children).mpr
    ⟨hnash, hchildren⟩

/-- Pure Nash equilibrium in the extracted strategic-form game of a
    nonterminal node, together with root-scoped subgame perfection on the head
    child and every tail child, gives root-scoped subgame perfection at the
    node. -/
theorem toStrategicGame_nash_toSubgamePerfectOn_Node
    {σ : ι → PlayerStrategy ι U}
    {m : ι} {h : GameTree ι U} {t : List (GameTree ι U)}
    (hnash : _root_.IsNashEquilibrium (toStrategicGame (Node m h t)) σ)
    (hhead : IsSubgamePerfectOn (profileStrategy σ) h)
    (htail : ∀ c ∈ t, IsSubgamePerfectOn (profileStrategy σ) c) :
    IsSubgamePerfectOn (profileStrategy σ) (Node m h t) :=
  (isSubgamePerfectOn_Node_iff_toStrategicGame_nash_and_head_tail).mpr
    ⟨hnash, hhead, htail⟩

/-- Existence of one normal-form profile satisfying the strategic-form root
    Nash and head/tail SPE check at a node is equivalent to existence of a
    root-scoped SPE tree strategy at that node. -/
theorem exists_toStrategicGame_nash_and_child_isSubgamePerfectOn_iff_exists_isSubgamePerfectOn_Node
    (m : ι) (h : GameTree ι U) (t : List (GameTree ι U)) :
    (∃ σ : ι → PlayerStrategy ι U,
      _root_.IsNashEquilibrium (toStrategicGame (Node m h t)) σ ∧
        IsSubgamePerfectOn (profileStrategy σ) h ∧
          ∀ c ∈ t, IsSubgamePerfectOn (profileStrategy σ) c) ↔
      ∃ τ : Strategy ι U, IsSubgamePerfectOn τ (Node m h t) := by
  constructor
  · rintro ⟨σ, hnash, hhead, htail⟩
    exact ⟨profileStrategy σ,
      toStrategicGame_nash_toSubgamePerfectOn_Node hnash hhead htail⟩
  · rintro ⟨τ, hspe⟩
    refine ⟨fun _ : ι => (τ : PlayerStrategy ι U), ?_, ?_, ?_⟩
    · exact (toStrategicGame_nash_iff_isNashAt (Node m h t) _).mpr (by
        simpa using hspe.toNashAt)
    · simpa using hspe.head
    · intro c hmem
      simpa using hspe.tail_mem hmem

/-- Existence of one normal-form profile satisfying the strategic-form root
    Nash and children SPE check at a node is equivalent to existence of a
    root-scoped SPE tree strategy at that node. -/
theorem exists_toStrategicGame_nash_and_children_isSubgamePerfectOn_iff_exists_isSubgamePerfectOn_Node
    (m : ι) (h : GameTree ι U) (t : List (GameTree ι U)) :
    (∃ σ : ι → PlayerStrategy ι U,
      _root_.IsNashEquilibrium (toStrategicGame (Node m h t)) σ ∧
        ∀ c ∈ children (Node m h t), IsSubgamePerfectOn (profileStrategy σ) c) ↔
      ∃ τ : Strategy ι U, IsSubgamePerfectOn τ (Node m h t) := by
  constructor
  · rintro ⟨σ, hnash, hchildren⟩
    exact ⟨profileStrategy σ,
      toStrategicGame_nash_toSubgamePerfectOn_Node_of_children hnash hchildren⟩
  · rintro ⟨τ, hspe⟩
    refine ⟨fun _ : ι => (τ : PlayerStrategy ι U), ?_, ?_⟩
    · exact (toStrategicGame_nash_iff_isNashAt (Node m h t) _).mpr (by
        simpa using hspe.toNashAt)
    · intro c hc
      simpa using hspe.child hc

/-- The backward-induction normal-form profile is a pure Nash equilibrium of
    the extracted strategic-form game. -/
theorem optStrategyProfile_toStrategicGame_nash (g : GameTree ι U) :
    _root_.IsNashEquilibrium (toStrategicGame g)
      (optStrategyProfile : (toStrategicGame g).Profile) :=
  (toStrategicGame_nash_iff_isNashAt g optStrategyProfile).mpr (by
    simpa using optStrategy_isNashAt (g := g))

/-- The backward-induction normal-form profile is pure Nash in the extracted
    strategic-form game of every subtree of a fixed root. -/
theorem optStrategyProfile_toStrategicGame_nash_on_subtree {s g : GameTree ι U}
    (hsub : Subtree s g) :
    _root_.IsNashEquilibrium (toStrategicGame s)
      (optStrategyProfile : (toStrategicGame s).Profile) :=
  (toStrategicGame_nash_iff_isNashAt s optStrategyProfile).mpr
    (optStrategy_isNashAt_subtree hsub)

/-- The backward-induction normal-form profile is pure Nash in the extracted
    strategic-form game of every proper subgame of a fixed root. -/
theorem optStrategyProfile_toStrategicGame_nash_on_properSubgame
    {s g : GameTree ι U} (hproper : ProperSubgame s g) :
    _root_.IsNashEquilibrium (toStrategicGame s)
      (optStrategyProfile : (toStrategicGame s).Profile) :=
  (toStrategicGame_nash_iff_isNashAt s optStrategyProfile).mpr
    (optStrategy_isNashAt_properSubgame hproper)

/-- Kuhn/backward induction gives a pure Nash equilibrium of the extracted
    strategic-form game. -/
theorem Kuhn_exists_toStrategicGame_nash (g : GameTree ι U) :
    ∃ σ : (toStrategicGame g).Profile,
      _root_.IsNashEquilibrium (toStrategicGame g) σ := by
  exact ⟨optStrategyProfile, optStrategyProfile_toStrategicGame_nash g⟩

/-- Kuhn/backward induction gives one pure normal-form profile that is Nash in
    the extracted strategic-form game of every subtree of a fixed root. -/
theorem Kuhn_exists_toStrategicGame_nash_on_subtrees (g : GameTree ι U) :
    ∃ σ : ι → PlayerStrategy ι U,
      ∀ s : GameTree ι U, Subtree s g →
        _root_.IsNashEquilibrium (toStrategicGame s) σ := by
  exact ⟨optStrategyProfile,
    fun _ hsub => optStrategyProfile_toStrategicGame_nash_on_subtree hsub⟩

/-- Kuhn/backward induction gives one pure normal-form profile that is Nash in
    the extracted strategic-form game of every proper subgame of a fixed root. -/
theorem Kuhn_exists_toStrategicGame_nash_on_properSubgames (g : GameTree ι U) :
    ∃ σ : ι → PlayerStrategy ι U,
      ∀ s : GameTree ι U, ProperSubgame s g →
        _root_.IsNashEquilibrium (toStrategicGame s) σ := by
  exact ⟨optStrategyProfile,
    fun _ hproper => optStrategyProfile_toStrategicGame_nash_on_properSubgame hproper⟩

/-- Kuhn/backward induction gives one pure normal-form profile that is Nash in
    the extracted strategic-form game of the root and of every proper subgame. -/
theorem Kuhn_exists_toStrategicGame_nash_and_toStrategicGame_nash_on_properSubgames
    (g : GameTree ι U) :
    ∃ σ : ι → PlayerStrategy ι U,
      _root_.IsNashEquilibrium (toStrategicGame g) σ ∧
        ∀ s : GameTree ι U, ProperSubgame s g →
          _root_.IsNashEquilibrium (toStrategicGame s) σ := by
  exact ⟨optStrategyProfile,
    optStrategyProfile_toStrategicGame_nash g,
    fun _ hproper => optStrategyProfile_toStrategicGame_nash_on_properSubgame hproper⟩

/-- Kuhn/backward induction gives one pure normal-form profile that is Nash in
    the extracted strategic-form game of the root and whose induced tree
    strategy is subgame-perfect on every proper subgame. -/
theorem Kuhn_exists_toStrategicGame_nash_and_SPE_on_properSubgames
    (g : GameTree ι U) :
    ∃ σ : ι → PlayerStrategy ι U,
      _root_.IsNashEquilibrium (toStrategicGame g) σ ∧
        ∀ s : GameTree ι U, ProperSubgame s g →
          IsSubgamePerfectOn (profileStrategy σ) s := by
  exact ⟨optStrategyProfile,
    optStrategyProfile_toStrategicGame_nash g,
    fun _ hproper => by
      simpa using optStrategy_isSubgamePerfectOn_properSubgame hproper⟩

/-- Kuhn/backward induction gives one pure normal-form profile that is Nash in
    every extracted strategic-form game. -/
theorem Kuhn_exists_forall_toStrategicGame_nash :
    ∃ σ : ι → PlayerStrategy ι U,
      ∀ g : GameTree ι U, _root_.IsNashEquilibrium (toStrategicGame g) σ := by
  exact ⟨optStrategyProfile, fun g => optStrategyProfile_toStrategicGame_nash g⟩

end GameTree
