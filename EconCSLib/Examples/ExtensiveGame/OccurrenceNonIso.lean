/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Compiler.GameTreeOccurrenceObserved

/-!
# EconCSLib.Examples.ExtensiveGame.OccurrenceNonIso

Regression for the endpoint-versus-occurrence compiler distinction documented
in `docs/design/efg-representation-compilation.md`.

The endpoint-sensitive compiler `GameTree.toObservedGame` and the
occurrence-sensitive compiler `GameTree.toOccurrenceObservedGame` are connected
by the directional certificate `ObservedGame.InformationRefinement`. This
module exhibits why the canonical certificate is not a strict information
relabeling: a finite `GameTree` contains one player-controlled subtree value at
two genuinely distinct history occurrences.

The occurrence compiler keeps these two histories apart (its information state
is the full history), while the endpoint compiler collapses them to a single
`NodeInfo`.  The forgetting map `GameTree.forgetOccurrenceInfo` therefore
identifies two distinct occurrence information states, so it is not injective,
and hence cannot be the information-state equivalence of a strict isomorphism.
That noninjectivity theorem alone does not rule out every conceivable
isomorphism.  The separate theorem `not_nonempty_iso` does so in the stated
endpoint-to-occurrence direction by using `ObservedGame.Iso.map_infoAt` and
injectivity of its history equivalence.

## The game

```
        root            (player 1)
       /    \
  repeated  middle       (middle: player 1)
    / \        |
  leaf leaf  repeated     (repeated: player 0)
              / \
            leaf leaf
```

`repeated` is a player-0 node.  It occurs directly under `root` and again under
`middle`, at two distinct histories with the same endpoint subtree value.

## Main results

* `Examples.OccurrenceNonIso.firstOcc_ne_secondOcc` — the two occurrences are
  distinct occurrence information states.
* `Examples.OccurrenceNonIso.forgetOccurrenceInfo_merges` — they are identified
  by the endpoint forgetting map.
* `Examples.OccurrenceNonIso.forgetOccurrenceInfo_not_injective` — the endpoint
  information-forgetting map is not injective, instantiating
  `GameTree.not_injective_forgetOccurrenceInfo_of_merged_histories`.
* `Examples.OccurrenceNonIso.separatingOccurrenceStrategy_distinguishes` — an
  occurrence strategy makes different choices at the two occurrences.
* `Examples.OccurrenceNonIso.endpointLift_same_choice` — every lifted endpoint
  strategy makes the same choice at both occurrences.
* `Examples.OccurrenceNonIso.not_nonempty_iso` — every strict observed-game
  isomorphism in the endpoint-to-occurrence direction is ruled out by the
  merged histories, using a separate structural argument.
* `Examples.OccurrenceNonIso.endpointOccurrenceRefinement_exists` — the
  concrete compilers carry the intended directional refinement certificate.
-/

namespace Examples.OccurrenceNonIso

open GameTree

/-- Two players; player `0` owns the repeated decision subtree. -/
abbrev Player := Fin 2

/-- The (irrelevant) common leaf payoff. -/
def leafPayoff : Player → ℤ := fun _ => 0

/-- A distinct alternative leaf payoff, making the repeated choice
nontrivial. -/
def alternativePayoff : Player → ℤ := fun _ => 1

/-- A player-`0` decision subtree that appears at two occurrences. -/
def repeated : GameTree Player ℤ :=
  .Node 0 (.Leaf leafPayoff) [.Leaf alternativePayoff]

/-- A player-`1` detour whose only child is `repeated`. -/
def middle : GameTree Player ℤ := .Node 1 repeated []

/-- The root: player `1` may move directly into `repeated`, or first into
`middle` and then into `repeated`. -/
def root : GameTree Player ℤ := .Node 1 repeated [middle]

/-- The action selecting `repeated` directly from `root`. -/
def rootToRepeated : (toExtensiveGame root).Action root :=
  ⟨repeated, List.mem_cons_self⟩

/-- The action selecting `middle` from `root`. -/
def rootToMiddle : (toExtensiveGame root).Action root :=
  ⟨middle, List.mem_cons_of_mem repeated List.mem_cons_self⟩

/-- The action selecting `repeated` from `middle`. -/
def middleToRepeated : (toExtensiveGame root).Action middle :=
  ⟨repeated, List.mem_cons_self⟩

/-- The length-`1` history reaching `repeated` directly from `root`. -/
def directHistory : (toExtensiveGame root).toArena.History root repeated :=
  (Arena.History.nil).snoc rootToRepeated

/-- The length-`2` history reaching `repeated` through `middle`. -/
def viaMiddleHistory : (toExtensiveGame root).toArena.History root repeated :=
  ((Arena.History.nil).snoc rootToMiddle).snoc middleToRepeated

/-- The repeated node has the legal action selecting `win`. -/
theorem repeated_nonterminal :
    ¬ (toExtensiveGame root).isTerminal repeated :=
  toExtensiveGame_not_isTerminal_node root 0
    (.Leaf leafPayoff) [.Leaf alternativePayoff]

/-- The repeated node is a genuine decision point. -/
theorem repeated_decision :
    (toExtensiveGame root).toArena.IsDecision repeated :=
  (toExtensiveGame root).toArena.isDecision_of_not_isTerminal
    repeated repeated_nonterminal

/-- The direct occurrence of player `0`'s decision at `repeated`. -/
def firstOcc : (toOccurrenceObservedGame root).InfoState (0 : Player) :=
  ⟨⟨repeated, directHistory⟩, rfl, repeated_decision⟩

/-- The occurrence of player `0`'s decision at `repeated` reached via `middle`. -/
def secondOcc : (toOccurrenceObservedGame root).InfoState (0 : Player) :=
  ⟨⟨repeated, viaMiddleHistory⟩, rfl, repeated_decision⟩

/-- The direct occurrence as a represented pure-strategy coordinate. -/
def firstRepresented :
    (toOccurrenceObservedGame root).RepresentedInfo (0 : Player) :=
  (toOccurrenceObservedGame root).representedInfoAt
    ⟨repeated, directHistory⟩ 0 rfl repeated_decision

/-- The detour occurrence as a represented pure-strategy coordinate. -/
def secondRepresented :
    (toOccurrenceObservedGame root).RepresentedInfo (0 : Player) :=
  (toOccurrenceObservedGame root).representedInfoAt
    ⟨repeated, viaMiddleHistory⟩ 0 rfl repeated_decision

/-- The two occurrences are genuinely distinct occurrence information states:
their underlying histories differ in length. -/
theorem firstOcc_ne_secondOcc : firstOcc ≠ secondOcc := by
  intro heq
  have hlen : directHistory.length = viaMiddleHistory.length :=
    congrArg
      (fun hf : (toExtensiveGame root).toArena.HistoryFrom root => hf.2.length)
      (congrArg Subtype.val heq)
  have hbad : (1 : ℕ) = 2 := hlen
  omega

/-- Both occurrences share the same endpoint subtree value `repeated`, so the
endpoint compiler merges them into a single `NodeInfo`. -/
theorem forgetOccurrenceInfo_merges :
    forgetOccurrenceInfo root (0 : Player) firstOcc =
      forgetOccurrenceInfo root 0 secondOcc :=
  forgetOccurrenceInfo_eq_of_endpoint_eq root 0 firstOcc secondOcc rfl

/-- **N-1.** The canonical endpoint information-forgetting map is not
injective, so it cannot serve as the information-state equivalence of a strict
isomorphism. This protects the directional refinement certificate from being
mistaken for a strict relabeling. -/
theorem forgetOccurrenceInfo_not_injective :
    ¬ Function.Injective (forgetOccurrenceInfo root (0 : Player)) :=
  not_injective_forgetOccurrenceInfo_of_merged_histories
    root 0 firstOcc secondOcc firstOcc_ne_secondOcc rfl

/-! ### Concrete strategy-space separation -/

/-- The first legal child at any player-`0` occurrence information state in
this example. -/
def firstLegalAction
    (information :
      (toOccurrenceObservedGame root).InfoState
        (0 : Player)) :
    (toOccurrenceObservedGame root).InfoAction 0 information := by
  rcases information with
    ⟨⟨endpoint, history⟩, hmover⟩
  cases endpoint with
  | Leaf payoff =>
      simp [toExtensiveGame] at hmover
  | Node mover head tail =>
      exact ⟨head, List.mem_cons_self⟩

/-- The alternative concrete action at the second occurrence. -/
def secondAlternativeAction :
    (toOccurrenceObservedGame root).InfoAction
      (0 : Player) secondOcc :=
  ⟨GameTree.Leaf alternativePayoff,
    List.mem_cons_of_mem (GameTree.Leaf leafPayoff)
      List.mem_cons_self⟩

-- Enumerate nonterminal histories without identifying repeated subtrees.
section OccurrenceDecision

private theorem decision_history_cases
    {state : (toExtensiveGame root).State}
    (history : (toExtensiveGame root).toArena.History root state) :
    (⟨state, history⟩ : (toExtensiveGame root).toArena.HistoryFrom root) =
        ⟨root, Arena.History.nil⟩ ∨
      (⟨state, history⟩ : (toExtensiveGame root).toArena.HistoryFrom root) =
        firstOcc.1 ∨
      (⟨state, history⟩ : (toExtensiveGame root).toArena.HistoryFrom root) =
        ⟨middle, Arena.History.nil.snoc rootToMiddle⟩ ∨
      (⟨state, history⟩ : (toExtensiveGame root).toArena.HistoryFrom root) =
        secondOcc.1 ∨
      ∃ payoff, state = .Leaf payoff := by
  induction history with
  | nil => exact Or.inl rfl
  | @snoc state history action ih =>
    rcases ih with hroot | hfirst | hmiddle | hsecond | ⟨payoff, rfl⟩
    · cases hroot
      rcases action with ⟨child, hchild⟩
      change child ∈ [repeated, middle] at hchild
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hchild
      rcases hchild with rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
    · cases hfirst
      rcases action with ⟨child, hchild⟩
      change child ∈ [.Leaf leafPayoff, .Leaf alternativePayoff] at hchild
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hchild
      rcases hchild with rfl | rfl <;>
        exact Or.inr (Or.inr (Or.inr (Or.inr ⟨_, rfl⟩)))
    · cases hmiddle
      rcases action with ⟨child, hchild⟩
      change child ∈ [repeated] at hchild
      simp only [List.mem_singleton] at hchild
      subst child
      exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    · cases hsecond
      rcases action with ⟨child, hchild⟩
      change child ∈ [.Leaf leafPayoff, .Leaf alternativePayoff] at hchild
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hchild
      rcases hchild with rfl | rfl <;>
        exact Or.inr (Or.inr (Or.inr (Or.inr ⟨_, rfl⟩)))
    · exact PEmpty.elim action

private theorem represented_eq_first_or_second
    (information : (toOccurrenceObservedGame root).RepresentedInfo (0 : Player)) :
    information = firstRepresented ∨ information = secondRepresented := by
  have hmover := information.1.2.1
  rcases decision_history_cases information.1.1.2 with h | h | h | h | ⟨payoff, h⟩
  · rw [congrArg Sigma.fst h] at hmover
    norm_num [toExtensiveGame, root] at hmover
  · exact Or.inl (Subtype.ext (Subtype.ext h))
  · rw [congrArg Sigma.fst h] at hmover
    norm_num [toExtensiveGame, middle] at hmover
  · exact Or.inr (Subtype.ext (Subtype.ext h))
  · rw [h] at hmover
    simp [toExtensiveGame] at hmover

-- Length distinguishes these occurrences because the exhaustive history
-- proof above rules out any other player-0 decision in this particular tree.
local instance secondOccurrenceDecidable
    (information : (toOccurrenceObservedGame root).RepresentedInfo (0 : Player)) :
    Decidable (information = secondRepresented) :=
  decidable_of_iff (information.1.1.2.length = 2) (by
    rcases represented_eq_first_or_second information with rfl | rfl
    · simp only [show firstRepresented.1.1.2.length = 1 from rfl]
      exact iff_of_false (by decide)
        (fun h => firstOcc_ne_secondOcc (congrArg Subtype.val h))
    · exact iff_of_true rfl rfl)

/-- Choose the alternative exactly at the second occurrence. -/
def separatingOccurrenceStrategy :
    (toOccurrenceObservedGame root).PureStrategy
      (0 : Player) := by
  intro information
  exact
    if h : information = secondRepresented then
      h ▸ secondAlternativeAction
    else
      firstLegalAction information.1

@[simp]
theorem separatingOccurrenceStrategy_first :
    separatingOccurrenceStrategy firstRepresented =
      (⟨.Leaf leafPayoff, List.mem_cons_self⟩ :
        (toOccurrenceObservedGame root).InfoAction
          (0 : Player) firstRepresented.1) := by
  rw [separatingOccurrenceStrategy]
  split
  · rename_i hsame
    exact (firstOcc_ne_secondOcc
      (congrArg Subtype.val hsame)).elim
  · rfl

@[simp]
theorem separatingOccurrenceStrategy_second :
    separatingOccurrenceStrategy secondRepresented =
      secondAlternativeAction := by
  rw [separatingOccurrenceStrategy, dif_pos rfl]

/-- The occurrence strategy makes observably different child choices at the
two histories with the same endpoint subtree. -/
theorem separatingOccurrenceStrategy_distinguishes :
    (separatingOccurrenceStrategy firstRepresented).1 ≠
      (separatingOccurrenceStrategy secondRepresented).1 := by
  rw [separatingOccurrenceStrategy_first,
    separatingOccurrenceStrategy_second]
  intro heq
  have hpayoff :
      leafPayoff = alternativePayoff :=
    GameTree.Leaf.inj heq
  have hatZero :=
    congrFun hpayoff (0 : Player)
  norm_num [leafPayoff, alternativePayoff] at hatZero

-- Execute the two choices at the same subtree reached along distinct paths.
example :
    (toExtensiveGame root).payoff
      (separatingOccurrenceStrategy firstRepresented).1 0 = 0 ∧
    (toExtensiveGame root).payoff
      (separatingOccurrenceStrategy secondRepresented).1 0 = 1 := by
  native_decide

end OccurrenceDecision

/-- Every endpoint strategy lifted through the canonical refinement makes the
same choice at both occurrences, because endpoint information has merged
them. -/
theorem endpointLift_same_choice
    (strategy :
      (toObservedGame root).PureStrategy
        (0 : Player)) :
    (liftEndpointPureStrategy root 0 strategy firstRepresented).1 =
      (liftEndpointPureStrategy root 0 strategy secondRepresented).1 := by
  unfold liftEndpointPureStrategy
  change
    (strategy
      ((endpointInformationRefinement root).toControlled
        |>.forgetRepresentedInfo 0 firstRepresented)).1 =
      (strategy
        ((endpointInformationRefinement root).toControlled
          |>.forgetRepresentedInfo 0 secondRepresented)).1
  congr 2

/-- Merged decision occurrences obstruct every strict observed-game isomorphism
from the endpoint compiler to the occurrence compiler, not only the canonical
occurrence-forgetting map.

An `ObservedGame.Iso` supplies an equivalence of complete histories together
with `map_infoAt`. The endpoint compiler assigns equal information states to
the two merged histories, while occurrence information determines its history,
so the two histories would have to coincide. -/
theorem not_nonempty_iso_toOccurrenceObservedGame_of_merged_histories
    {N U : Type*}
    (treeRoot : GameTree N U) (i : N)
    (first second :
      (toExtensiveGame treeRoot).toArena.HistoryFrom treeRoot)
    (hfirst : (toExtensiveGame treeRoot).mover first.1 = some i)
    (hfirst_nonterminal :
      ¬ (toExtensiveGame treeRoot).isTerminal first.1)
    (hsecond : (toExtensiveGame treeRoot).mover second.1 = some i)
    (hsecond_nonterminal :
      ¬ (toExtensiveGame treeRoot).isTerminal second.1)
    (hendpoint : first.1 = second.1)
    (hdifferent : first ≠ second) :
    ¬ Nonempty
        ((toObservedGame treeRoot).Iso
          (toOccurrenceObservedGame treeRoot)) := by
  rintro ⟨e⟩
  have htfirst :
      (toOccurrenceObservedGame treeRoot).base.mover
          (e.historyIso.stateEquiv first).1 = some i :=
    (e.map_mover first).trans hfirst
  have htsecond :
      (toOccurrenceObservedGame treeRoot).base.mover
          (e.historyIso.stateEquiv second).1 = some i :=
    (e.map_mover second).trans hsecond
  have htfirst_nonterminal :
      ¬ (toOccurrenceObservedGame treeRoot).base.isTerminal
        (e.historyIso.stateEquiv first).1 :=
    (not_congr (e.isTerminal_iff first)).mp hfirst_nonterminal
  have htsecond_nonterminal :
      ¬ (toOccurrenceObservedGame treeRoot).base.isTerminal
        (e.historyIso.stateEquiv second).1 :=
    (not_congr (e.isTerminal_iff second)).mp hsecond_nonterminal
  let hfirst_decision :=
    (toExtensiveGame treeRoot).toArena.isDecision_of_not_isTerminal
      first.1 hfirst_nonterminal
  let hsecond_decision :=
    (toExtensiveGame treeRoot).toArena.isDecision_of_not_isTerminal
      second.1 hsecond_nonterminal
  let htfirst_decision :=
    (toOccurrenceObservedGame treeRoot).base.toArena
      |>.isDecision_of_not_isTerminal
        (e.historyIso.stateEquiv first).1 htfirst_nonterminal
  let htsecond_decision :=
    (toOccurrenceObservedGame treeRoot).base.toArena
      |>.isDecision_of_not_isTerminal
        (e.historyIso.stateEquiv second).1 htsecond_nonterminal
  have hinfo :
      (toObservedGame treeRoot).infoAt first i hfirst
          hfirst_decision =
        (toObservedGame treeRoot).infoAt second i hsecond
          hsecond_decision :=
    forgetOccurrenceInfo_eq_of_endpoint_eq treeRoot i
      ⟨first, hfirst, hfirst_decision⟩
      ⟨second, hsecond, hsecond_decision⟩ hendpoint
  have hmapped :
      (toOccurrenceObservedGame treeRoot).infoAt
          (e.historyIso.stateEquiv first) i htfirst
            htfirst_decision =
        (toOccurrenceObservedGame treeRoot).infoAt
          (e.historyIso.stateEquiv second) i htsecond
            htsecond_decision := by
    rw [← e.map_infoAt first i hfirst hfirst_decision
        htfirst htfirst_decision,
      ← e.map_infoAt second i hsecond hsecond_decision
        htsecond htsecond_decision, hinfo]
  exact hdifferent
    (e.historyIso.stateEquiv.injective
      (toOccurrenceObservedGame_hasSingletonInformation treeRoot i
        _ _ htfirst htfirst_decision htsecond
          htsecond_decision hmapped))

/-- **N-1B.** No strict observed-game isomorphism from the endpoint compiler to
the occurrence compiler exists for this concrete tree.

This conclusion does not follow merely from
`forgetOccurrenceInfo_not_injective`: it rules out every candidate strict
isomorphism by the separate merged-history argument above. It prevents the
false generalization that a directional information refinement must be a
strict relabeling, while retaining the positive refinement certificate below.
The statement is directional and makes no claim about all compiler inputs. -/
theorem not_nonempty_iso :
    ¬ Nonempty
        ((toObservedGame root).Iso
          (toOccurrenceObservedGame root)) :=
  not_nonempty_iso_toOccurrenceObservedGame_of_merged_histories
    root 0 ⟨repeated, directHistory⟩ ⟨repeated, viaMiddleHistory⟩
    rfl repeated_nonterminal rfl repeated_nonterminal rfl
    (fun heq => firstOcc_ne_secondOcc (Subtype.ext heq))

/-- The endpoint compiler is concretely certified as the information-coarsened
source and the occurrence compiler as its directional refinement. -/
theorem endpointOccurrenceRefinement_exists :
    Nonempty
      ((toObservedGame root).InformationRefinement
        (toOccurrenceObservedGame root)) :=
  ⟨endpointInformationRefinement root⟩

end Examples.OccurrenceNonIso
