/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.Math.Probability.FiniteMarkovChain.Automaton

/-!
# Exact parity classification for finite rational Markov chains

This executable module treats a finite rational `Chain n m` as a Markov chain
on all `n + m` states.  An original terminal state is not deleted: it is a
permanent probability-one self loop.  Therefore its priority is seen
infinitely often, exactly as required by infinite-time semantics.

The convention is **min-parity**.  A bottom strongly connected component is
accepting when the minimum priority in that component is even.  This file
computes the positive-support graph, reachability, mutual reachability,
bottom-state classification and accepting bottom states.  It proves that
every total state reaches a classified bottom SCC, reduces the graph problem
to first entry into an accepting or rejecting bottom class, and solves the
resulting finite rational Bellman systems.

Reachability is implemented by the finite least-closed-set test: `j` is
reachable from `i` exactly when every edge-closed finite vertex set containing
`i` also contains `j`.  This deliberately simple implementation is
exponential in the number `N = n + m` of total states, with additional
polynomial recomputation across all reachability and bottom queries.  The
exact Cramer solver uses executable determinants; with the current Leibniz
determinant implementation its arithmetic work is factorial in `N` in the
worst case, before rational coefficient growth.  Warshall/Tarjan reachability
and fraction-free elimination may later improve those costs without changing
the public specifications.

The result is finite Markov-graph semantics.  No claim is made here that the
computed rational number equals a measure-theoretic omega-event.  Such an
identification belongs in a separate analytic semantics leaf.  In particular,
this module imports no measure theory and does not construct a path measure.

The construction applies directly to any finite product chain produced by
`FiniteMarkovChain.Automaton`; the priority function is simply supplied on the
product chain's total states.
-/

namespace FiniteMarkovChain.Chain

open Matrix
open scoped BigOperators

variable {n m : ℕ} (C : Chain n m)

/-! ## Total states and positive-support reachability -/

/-- All states of a chain, encoded in the flat finite type used by matrices. -/
abbrev TotalState (n m : ℕ) := Fin (n + m)

/-- Encode either an original transient or an original terminal state. -/
def encodeTotal : Fin n ⊕ Fin m → TotalState n m :=
  finSumFinEquiv

/-- Decode a total state into its original transient/terminal coordinate. -/
def decodeTotal : TotalState n m → Fin n ⊕ Fin m :=
  finSumFinEquiv.symm

@[simp]
theorem decodeTotal_encodeTotal (state : Fin n ⊕ Fin m) :
    decodeTotal (encodeTotal state) = state :=
  finSumFinEquiv.symm_apply_apply state

@[simp]
theorem encodeTotal_decodeTotal (state : TotalState n m) :
    encodeTotal (decodeTotal state) = state :=
  finSumFinEquiv.apply_symm_apply state

@[simp]
theorem decodeTotal_castAdd (state : Fin n) :
    decodeTotal (Fin.castAdd m state) = (Sum.inl state : Fin n ⊕ Fin m) := by
  change finSumFinEquiv.symm (finSumFinEquiv (Sum.inl state)) = Sum.inl state
  simp

@[simp]
theorem decodeTotal_natAdd (state : Fin m) :
    decodeTotal (Fin.natAdd n state) = (Sum.inr state : Fin n ⊕ Fin m) := by
  change finSumFinEquiv.symm (finSumFinEquiv (Sum.inr state)) = Sum.inr state
  simp

/-- Assemble a priority function from separate transient and terminal
priorities.  A terminal priority recurs forever because terminals stutter. -/
def totalPriority
    (transientPriority : Fin n → ℕ) (terminalPriority : Fin m → ℕ) :
    TotalState n m → ℕ :=
  fun state => Sum.elim transientPriority terminalPriority (decodeTotal state)

@[simp]
theorem totalPriority_transient
    (transientPriority : Fin n → ℕ) (terminalPriority : Fin m → ℕ)
    (state : Fin n) :
    totalPriority transientPriority terminalPriority (encodeTotal (Sum.inl state)) =
      transientPriority state := by
  simp [totalPriority]

@[simp]
theorem totalPriority_terminal
    (transientPriority : Fin n → ℕ) (terminalPriority : Fin m → ℕ)
    (state : Fin m) :
    totalPriority transientPriority terminalPriority (encodeTotal (Sum.inr state)) =
      terminalPriority state := by
  simp [totalPriority]

/-- Total transition matrix.  Original terminals stutter forever. -/
def totalTransition : Matrix (TotalState n m) (TotalState n m) ℚ≥0 :=
  fun source target =>
    match decodeTotal source, decodeTotal target with
    | .inl i, .inl j => C.transient i j
    | .inl i, .inr a => C.terminal i a
    | .inr _, .inl _ => 0
    | .inr a, .inr b => if a = b then 1 else 0

/-- Rational total transition matrix. -/
def totalQ : Matrix (TotalState n m) (TotalState n m) ℚ :=
  fun source target => C.totalTransition source target

/-- The positive-support directed edge relation. -/
def PositiveEdge (source target : TotalState n m) : Prop :=
  0 < C.totalTransition source target

instance decidablePositiveEdge (source target : TotalState n m) :
    Decidable (C.PositiveEdge source target) := by
  unfold PositiveEdge
  infer_instance

/-- Executable positive-support edge test. -/
def positiveEdge (source target : TotalState n m) : Bool :=
  decide (C.PositiveEdge source target)

@[simp]
theorem positiveEdge_eq_true_iff (source target : TotalState n m) :
    C.positiveEdge source target = true ↔ C.PositiveEdge source target := by
  simp [positiveEdge]

/-- Graph reachability as membership in every finite edge-closed set.

This least-closed-set formulation is finite and decidable because the vertex
type is finite.  It avoids exposing a caller-supplied path or SCC witness. -/
def Reachable (source target : TotalState n m) : Prop :=
  ∀ vertices : Finset (TotalState n m),
    source ∈ vertices →
    (∀ i, i ∈ vertices → ∀ j,
      C.PositiveEdge i j → j ∈ vertices) →
    target ∈ vertices

instance decidableReachable (source target : TotalState n m) :
    Decidable (C.Reachable source target) := by
  unfold Reachable
  infer_instance

/-- Executable finite reachability. -/
def reachable (source target : TotalState n m) : Bool :=
  decide (C.Reachable source target)

@[simp]
theorem reachable_eq_true_iff (source target : TotalState n m) :
    C.reachable source target = true ↔ C.Reachable source target := by
  simp [reachable]

theorem Reachable.refl (state : TotalState n m) :
    C.Reachable state state := by
  intro vertices hstate _
  exact hstate

theorem PositiveEdge.reachable {source target : TotalState n m}
    (edge : C.PositiveEdge source target) :
    C.Reachable source target := by
  intro vertices hsource hclosed
  exact hclosed source hsource target edge

theorem Reachable.trans {first second third : TotalState n m}
    (hfirst : C.Reachable first second)
    (hsecond : C.Reachable second third) :
    C.Reachable first third := by
  intro vertices hfirstMem hclosed
  exact hsecond vertices (hfirst vertices hfirstMem hclosed) hclosed

/-- Mutual reachability, the state-level representation of SCC membership. -/
def MutuallyReachable (left right : TotalState n m) : Prop :=
  C.Reachable left right ∧ C.Reachable right left

instance decidableMutuallyReachable (left right : TotalState n m) :
    Decidable (C.MutuallyReachable left right) := by
  unfold MutuallyReachable
  infer_instance

/-- Executable SCC-equivalence test. -/
def mutuallyReachable (left right : TotalState n m) : Bool :=
  C.reachable left right && C.reachable right left

@[simp]
theorem mutuallyReachable_eq_true_iff (left right : TotalState n m) :
    C.mutuallyReachable left right = true ↔
      C.MutuallyReachable left right := by
  simp [mutuallyReachable, MutuallyReachable]

theorem MutuallyReachable.refl (state : TotalState n m) :
    C.MutuallyReachable state state :=
  ⟨Reachable.refl C state, Reachable.refl C state⟩

theorem MutuallyReachable.symm {left right : TotalState n m}
    (h : C.MutuallyReachable left right) :
    C.MutuallyReachable right left :=
  And.symm h

theorem MutuallyReachable.trans {first second third : TotalState n m}
    (hfirst : C.MutuallyReachable first second)
    (hsecond : C.MutuallyReachable second third) :
    C.MutuallyReachable first third :=
  ⟨Reachable.trans C hfirst.1 hsecond.1,
    Reachable.trans C hsecond.2 hfirst.2⟩

/-- The automatically computed SCC containing a state. -/
def component (state : TotalState n m) : Finset (TotalState n m) :=
  Finset.univ.filter fun other => C.mutuallyReachable state other

@[simp]
theorem mem_component_iff (state other : TotalState n m) :
    other ∈ C.component state ↔ C.MutuallyReachable state other := by
  simp [component]

theorem mem_component_self (state : TotalState n m) :
    state ∈ C.component state := by
  rw [C.mem_component_iff]
  exact MutuallyReachable.refl C state

theorem component_eq_of_mutuallyReachable {left right : TotalState n m}
    (h : C.MutuallyReachable left right) :
    C.component left = C.component right := by
  ext state
  simp only [C.mem_component_iff]
  constructor
  · intro hleft
    exact MutuallyReachable.trans C (MutuallyReachable.symm C h) hleft
  · intro hright
    exact MutuallyReachable.trans C h hright

/-- All vertices reachable from `source`, computed without a supplied path. -/
def reachableSet (source : TotalState n m) : Finset (TotalState n m) :=
  Finset.univ.filter fun target => C.reachable source target

@[simp]
theorem mem_reachableSet_iff (source target : TotalState n m) :
    target ∈ C.reachableSet source ↔ C.Reachable source target := by
  simp [reachableSet]

theorem reachableSet_nonempty (source : TotalState n m) :
    (C.reachableSet source).Nonempty :=
  ⟨source, by
    rw [C.mem_reachableSet_iff]
    exact Reachable.refl C source⟩

theorem reachableSet_subset_of_reachable
    {source target : TotalState n m}
    (h : C.Reachable source target) :
    C.reachableSet target ⊆ C.reachableSet source := by
  intro state hstate
  rw [C.mem_reachableSet_iff] at hstate ⊢
  exact Reachable.trans C h hstate

/-- A state lies in a bottom SCC exactly when every positive outgoing edge
from every state in its SCC stays in that SCC. -/
def IsBottom (state : TotalState n m) : Prop :=
  ∀ source, C.MutuallyReachable state source →
    ∀ target, C.PositiveEdge source target →
      C.MutuallyReachable state target

instance decidableIsBottom (state : TotalState n m) :
    Decidable (C.IsBottom state) := by
  unfold IsBottom
  infer_instance

/-- Executable bottom-SCC classification. -/
def isBottom (state : TotalState n m) : Bool :=
  decide (C.IsBottom state)

@[simp]
theorem isBottom_eq_true_iff (state : TotalState n m) :
    C.isBottom state = true ↔ C.IsBottom state := by
  simp [isBottom]

/-- The local graph property certified by the bottom classifier. -/
theorem isBottom_edge_iff (state : TotalState n m) :
    C.isBottom state = true ↔
      ∀ source, C.MutuallyReachable state source →
        ∀ target, C.PositiveEdge source target →
          C.MutuallyReachable state target := by
  simp [IsBottom]

theorem IsBottom.of_mutuallyReachable {left right : TotalState n m}
    (hbottom : C.IsBottom left)
    (hsame : C.MutuallyReachable left right) :
    C.IsBottom right := by
  intro source hrightSource target hedge
  have hleftSource : C.MutuallyReachable left source :=
    MutuallyReachable.trans C hsame hrightSource
  have hleftTarget := hbottom source hleftSource target hedge
  exact MutuallyReachable.trans C (MutuallyReachable.symm C hsame) hleftTarget

/-- Every vertex of a finite directed graph reaches an automatically
classified bottom SCC. -/
theorem exists_reachable_bottom (source : TotalState n m) :
    ∃ bottom, C.Reachable source bottom ∧ C.IsBottom bottom := by
  obtain ⟨bottom, hbottomMem, hminimal⟩ :=
    (C.reachableSet source).exists_min_image
      (fun state => (C.reachableSet state).card)
      (C.reachableSet_nonempty source)
  have hsourceBottom : C.Reachable source bottom :=
    (C.mem_reachableSet_iff source bottom).mp hbottomMem
  refine ⟨bottom, hsourceBottom, ?_⟩
  intro inside hbottomInside target hedge
  have hbottomTarget : C.Reachable bottom target :=
    Reachable.trans C hbottomInside.1
      (PositiveEdge.reachable C hedge)
  have hsourceTarget : C.Reachable source target :=
    Reachable.trans C hsourceBottom hbottomTarget
  have htargetMem : target ∈ C.reachableSet source :=
    (C.mem_reachableSet_iff source target).mpr hsourceTarget
  have hcardForward :
      (C.reachableSet bottom).card ≤ (C.reachableSet target).card :=
    hminimal target htargetMem
  have hsubset : C.reachableSet target ⊆ C.reachableSet bottom :=
    C.reachableSet_subset_of_reachable hbottomTarget
  have hsets : C.reachableSet target = C.reachableSet bottom :=
    Finset.eq_of_subset_of_card_le hsubset hcardForward
  have htargetBottom : C.Reachable target bottom := by
    rw [← C.mem_reachableSet_iff, hsets]
    rw [C.mem_reachableSet_iff]
    exact Reachable.refl C bottom
  exact ⟨hbottomTarget, htargetBottom⟩

/-! ## Bottom components and minimum priorities -/

/-- Minimum priority of the SCC containing `state`.

The component is nonempty because it contains `state`, so this is total. -/
def componentMinPriority
    (priority : TotalState n m → ℕ) (state : TotalState n m) : ℕ :=
  let priorities := (C.component state).image priority
  priorities.min' ⟨priority state, Finset.mem_image.mpr
    ⟨state, C.mem_component_self state, rfl⟩⟩

/-- The computed minimum priority is attained inside the SCC. -/
theorem componentMinPriority_mem
    (priority : TotalState n m → ℕ) (state : TotalState n m) :
    ∃ member ∈ C.component state,
      priority member = C.componentMinPriority priority state := by
  let priorities := (C.component state).image priority
  have hnonempty : priorities.Nonempty :=
    ⟨priority state, Finset.mem_image.mpr
      ⟨state, C.mem_component_self state, rfl⟩⟩
  have hminimum : priorities.min' hnonempty ∈ priorities :=
    Finset.min'_mem priorities hnonempty
  obtain ⟨member, hmember, heq⟩ := Finset.mem_image.mp hminimum
  refine ⟨member, hmember, ?_⟩
  simpa [componentMinPriority, priorities] using heq

/-- The computed SCC priority is no larger than any member priority. -/
theorem componentMinPriority_le
    (priority : TotalState n m → ℕ)
    (state member : TotalState n m)
    (hmember : member ∈ C.component state) :
    C.componentMinPriority priority state ≤ priority member := by
  unfold componentMinPriority
  exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨member, hmember, rfl⟩)

theorem componentMinPriority_eq_of_mutuallyReachable
    (priority : TotalState n m → ℕ)
    {left right : TotalState n m}
    (h : C.MutuallyReachable left right) :
    C.componentMinPriority priority left =
      C.componentMinPriority priority right := by
  simp only [componentMinPriority, C.component_eq_of_mutuallyReachable h]

/-- Min-parity acceptance of a bottom state. -/
def IsAcceptingBottom
    (priority : TotalState n m → ℕ) (state : TotalState n m) : Prop :=
  C.IsBottom state ∧ C.componentMinPriority priority state % 2 = 0

/-- Executable accepting-BSCC state classifier. -/
def isAcceptingBottom
    (priority : TotalState n m → ℕ) (state : TotalState n m) : Bool :=
  C.isBottom state && decide (C.componentMinPriority priority state % 2 = 0)

@[simp]
theorem isAcceptingBottom_eq_true_iff
    (priority : TotalState n m → ℕ) (state : TotalState n m) :
    C.isAcceptingBottom priority state = true ↔
      C.IsAcceptingBottom priority state := by
  simp [isAcceptingBottom, IsAcceptingBottom]

@[simp]
theorem isAcceptingBottom_eq_false_iff
    (priority : TotalState n m → ℕ) (state : TotalState n m) :
    C.isAcceptingBottom priority state = false ↔
      ¬ C.IsAcceptingBottom priority state := by
  constructor
  · intro hfalse haccepting
    have htrue := (C.isAcceptingBottom_eq_true_iff priority state).mpr haccepting
    simp [hfalse] at htrue
  · intro hnot
    cases hvalue : C.isAcceptingBottom priority state with
    | false => rfl
    | true =>
        exact False.elim (hnot
          ((C.isAcceptingBottom_eq_true_iff priority state).mp hvalue))

/-- Automatically enumerated accepting-BSCC target states. -/
def acceptingBottomStates
    (priority : TotalState n m → ℕ) : Finset (TotalState n m) :=
  Finset.univ.filter fun state => C.isAcceptingBottom priority state

@[simp]
theorem mem_acceptingBottomStates_iff
    (priority : TotalState n m → ℕ) (state : TotalState n m) :
    state ∈ C.acceptingBottomStates priority ↔
      C.IsAcceptingBottom priority state := by
  simp [acceptingBottomStates]

/-- Automatically enumerated rejecting-BSCC target states. -/
def rejectingBottomStates
    (priority : TotalState n m → ℕ) : Finset (TotalState n m) :=
  Finset.univ.filter fun state =>
    C.isBottom state && !C.isAcceptingBottom priority state

@[simp]
theorem mem_rejectingBottomStates_iff
    (priority : TotalState n m → ℕ) (state : TotalState n m) :
    state ∈ C.rejectingBottomStates priority ↔
      C.IsBottom state ∧ ¬ C.IsAcceptingBottom priority state := by
  simp [rejectingBottomStates]

/-- Accepting bottom states are closed under every positive outgoing edge. -/
theorem IsAcceptingBottom.edge_closed
    (priority : TotalState n m → ℕ)
    {source target : TotalState n m}
    (haccepting : C.IsAcceptingBottom priority source)
    (hedge : C.PositiveEdge source target) :
    C.IsAcceptingBottom priority target := by
  have hsame : C.MutuallyReachable source target :=
    haccepting.1 source (MutuallyReachable.refl C source) target hedge
  refine ⟨IsBottom.of_mutuallyReachable C haccepting.1 hsame, ?_⟩
  rw [← C.componentMinPriority_eq_of_mutuallyReachable priority hsame]
  exact haccepting.2

/-- Boolean form of accepting-target closure. -/
theorem isAcceptingBottom_edge_closed
    (priority : TotalState n m → ℕ)
    {source target : TotalState n m}
    (haccepting : C.isAcceptingBottom priority source = true)
    (hedge : C.positiveEdge source target = true) :
    C.isAcceptingBottom priority target = true := by
  rw [C.isAcceptingBottom_eq_true_iff] at haccepting ⊢
  rw [C.positiveEdge_eq_true_iff] at hedge
  exact IsAcceptingBottom.edge_closed C priority haccepting hedge

/-- Original terminal states are permanent self loops in the total graph. -/
@[simp]
theorem totalTransition_terminal
    (terminal other : Fin m) :
    C.totalTransition (encodeTotal (Sum.inr terminal))
        (encodeTotal (Sum.inr other)) =
      if terminal = other then 1 else 0 := by
  simp [totalTransition]

@[simp]
theorem totalTransition_terminal_transient
    (terminal : Fin m) (transient : Fin n) :
    C.totalTransition (encodeTotal (Sum.inr terminal))
        (encodeTotal (Sum.inl transient)) = 0 := by
  simp [totalTransition]

/-- Every total-state transition row is normalized. -/
theorem totalTransition_normalized (source : TotalState n m) :
    ∑ target, C.totalTransition source target = 1 := by
  rw [← (finSumFinEquiv : Fin n ⊕ Fin m ≃ Fin (n + m)).sum_comp]
  rw [Fintype.sum_sum_type]
  cases hsource : decodeTotal source with
  | inl i =>
      have hencode : source = encodeTotal (Sum.inl i) := by
        rw [← hsource]
        exact (encodeTotal_decodeTotal source).symm
      subst source
      simpa [totalTransition] using C.normalized i
  | inr a =>
      have hencode : source = encodeTotal (Sum.inr a) := by
        rw [← hsource]
        exact (encodeTotal_decodeTotal source).symm
      subst source
      simp [totalTransition]

/-! ## Reduction to a two-outcome absorbing chain -/

/-- Transient block of the parity-to-BSCC reachability reduction.  A bottom
state exits immediately to its accepting or rejecting outcome; every other
state follows the original total transition row. -/
def parityTransient : Matrix (TotalState n m) (TotalState n m) ℚ≥0 :=
  fun source target =>
    if C.isBottom source then 0 else C.totalTransition source target

/-- Outcome block of the parity-to-BSCC reduction.  Outcome `0` is accepting
and outcome `1` is rejecting/nonaccepting. -/
def parityTerminal
    (priority : TotalState n m → ℕ) :
    Matrix (TotalState n m) (Fin 2) ℚ≥0 :=
  fun source outcome =>
    if C.isBottom source then
      if outcome = (if C.isAcceptingBottom priority source then 0 else 1) then 1 else 0
    else
      0

/-- Normalized reachability chain whose two terminal outcomes classify the
eventual bottom SCC. -/
def parityChain (priority : TotalState n m → ℕ) : Chain (n + m) 2 where
  transient := C.parityTransient
  terminal := C.parityTerminal priority
  normalized source := by
    cases hbottom : C.isBottom source with
    | false =>
        simp [parityTransient, parityTerminal, hbottom,
          C.totalTransition_normalized source]
    | true =>
        simp [parityTransient, parityTerminal, hbottom]
  reward outcome := if outcome = 0 then 1 else 0

/-- A bottom state exits the reduction chain in one step. -/
theorem parityChain_canReachTerminal_of_bottom
    (priority : TotalState n m → ℕ)
    (state : TotalState n m) (hbottom : C.IsBottom state) :
    (C.parityChain priority).canReachTerminal state = true := by
  rw [(C.parityChain priority).canReachTerminal_iff_eventually]
  refine ⟨1, ?_⟩
  have hbottomBool : C.isBottom state = true :=
    (C.isBottom_eq_true_iff state).mpr hbottom
  change (∑ target, ((C.parityChain priority).Q ^ 1) state target) < 1
  simp [Chain.Q, parityChain, parityTransient, hbottomBool]

/-- States failing to reach an outcome in the reduction chain are closed
under every positive edge of the original total graph. -/
theorem parityChain_unreachable_edge_closed
    (priority : TotalState n m → ℕ)
    {source target : TotalState n m}
    (hsource : (C.parityChain priority).canReachTerminal source = false)
    (hedge : C.PositiveEdge source target) :
    (C.parityChain priority).canReachTerminal target = false := by
  have hnotBottom : C.isBottom source = false := by
    by_contra h
    have htrue : C.isBottom source = true := by
      cases hvalue : C.isBottom source <;> simp_all
    have hbottom := (C.isBottom_eq_true_iff source).mp htrue
    have := C.parityChain_canReachTerminal_of_bottom priority source hbottom
    simp [hsource] at this
  by_contra htarget
  have htargetTrue :
      (C.parityChain priority).canReachTerminal target = true :=
    by cases hvalue : (C.parityChain priority).canReachTerminal target <;> simp_all
  obtain ⟨horizon, hfinish⟩ :=
    ((C.parityChain priority).canReachTerminal_iff_eventually target).mp
      htargetTrue
  have hq : 0 < (C.parityChain priority).Q source target := by
    change 0 < ((C.parityChain priority).transient source target : ℚ)
    simp only [parityChain, parityTransient, hnotBottom, Bool.false_eq_true,
      if_false]
    exact_mod_cast hedge
  have hsourceFinish :
      (C.parityChain priority).survival (horizon + 1) source < 1 :=
    ((C.parityChain priority).survival_succ_lt_one_iff horizon source).mpr
      (Or.inr ⟨target, hq, hfinish⟩)
  have hsourceTrue :
      (C.parityChain priority).canReachTerminal source = true :=
    ((C.parityChain priority).canReachTerminal_iff_eventually source).mpr
      ⟨horizon + 1, hsourceFinish⟩
  simp [hsource] at hsourceTrue

/-- Every state reaches one of the two parity outcomes.  Closed nonterminal
classes are not excluded: each is itself an accepting or rejecting BSCC. -/
theorem parityChain_canReachTerminal
    (priority : TotalState n m → ℕ)
    (source : TotalState n m) :
    (C.parityChain priority).canReachTerminal source = true := by
  obtain ⟨bottom, hreachable, hbottom⟩ := C.exists_reachable_bottom source
  by_contra hsource
  have hsourceFalse :
      (C.parityChain priority).canReachTerminal source = false :=
    Bool.eq_false_iff.mpr hsource
  let bad : Finset (TotalState n m) :=
    Finset.univ.filter fun state =>
      (C.parityChain priority).canReachTerminal state = false
  have hsourceMem : source ∈ bad := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ source, hsourceFalse⟩
  have hclosed : ∀ state, state ∈ bad → ∀ target,
      C.PositiveEdge state target → target ∈ bad := by
    intro state hstate target hedge
    have hstateFalse :
        (C.parityChain priority).canReachTerminal state = false := by
      exact (Finset.mem_filter.mp hstate).2
    have htargetFalse :=
      C.parityChain_unreachable_edge_closed priority hstateFalse hedge
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ target, htargetFalse⟩
  have hbottomMem : bottom ∈ bad :=
    hreachable bad hsourceMem hclosed
  have hbottomFalse :
      (C.parityChain priority).canReachTerminal bottom = false := by
    exact (Finset.mem_filter.mp hbottomMem).2
  have hbottomTrue :=
    C.parityChain_canReachTerminal_of_bottom priority bottom hbottom
  simp [hbottomFalse] at hbottomTrue

/-- The reduction chain passes the existing automatic finite-state
reachability check for every finite rational input chain. -/
theorem parityChain_autoCheck
    (priority : TotalState n m → ℕ) :
    (C.parityChain priority).autoCheck = true := by
  rw [(C.parityChain priority).autoCheck_iff_reaches]
  intro source
  exact ((C.parityChain priority).canReachTerminal_iff_eventually source).mp
    (C.parityChain_canReachTerminal priority source)

/-! ## Contraction and uniqueness of the Bellman solution -/

private theorem abs_Q_pow_mulVec_le_survival
    (D : Chain n m) (value : Fin n → ℚ) (bound : ℚ)
    (hvalue : ∀ state, |value state| ≤ bound)
    (horizon : ℕ) (source : Fin n) :
    |(D.Q ^ horizon *ᵥ value) source| ≤
      D.survival horizon source * bound := by
  calc
    |(D.Q ^ horizon *ᵥ value) source| =
        |∑ target, (D.Q ^ horizon) source target * value target| := rfl
    _ ≤ ∑ target, |(D.Q ^ horizon) source target * value target| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ target, (D.Q ^ horizon) source target * |value target| := by
      apply Finset.sum_congr rfl
      intro target _
      rw [abs_mul, abs_of_nonneg (D.pow_nonneg horizon source target)]
    _ ≤ ∑ target, (D.Q ^ horizon) source target * bound := by
      apply Finset.sum_le_sum
      intro target _
      exact mul_le_mul_of_nonneg_left (hvalue target)
        (D.pow_nonneg horizon source target)
    _ = D.survival horizon source * bound := by
      rw [Chain.survival, Finset.sum_mul]

private lemma eq_pow_mulVec_of_fixed (D : Chain n m) (difference : Fin n → ℚ)
    (hfixed : difference = D.Q *ᵥ difference) (horizon : ℕ) :
    difference = D.Q ^ horizon *ᵥ difference := by
  induction horizon with
  | zero => simp
  | succ horizon ih =>
      calc
        difference = D.Q *ᵥ difference := hfixed
        _ = D.Q *ᵥ (D.Q ^ horizon *ᵥ difference) :=
          congrArg (fun value => D.Q *ᵥ value) ih
        _ = D.Q ^ (horizon + 1) *ᵥ difference := by
          rw [Matrix.mulVec_mulVec, pow_succ']

private lemma eq_zero_of_fixed_of_autoCheck (D : Chain n m)
    (hcheck : D.autoCheck = true) (difference : Fin n → ℚ)
    (hfixed : difference = D.Q *ᵥ difference) : difference = 0 := by
  have hadmissible : D.admissible (n + 1) D.autoBound = true := hcheck
  obtain ⟨_, _, hc1, hrows⟩ := (D.admissible_iff (n + 1) D.autoBound).mp hadmissible
  cases isEmpty_or_nonempty (Fin n)
  · funext state
    exact isEmptyElim state
  · have huniv : (Finset.univ : Finset (Fin n)).Nonempty :=
      Finset.univ_nonempty
    obtain ⟨maxState, _, hmaxValue⟩ :=
      Finset.exists_mem_eq_sup' huniv fun state => |difference state|
    have hmax (state : Fin n) :
        |difference state| ≤ |difference maxState| := by
      rw [← hmaxValue]
      exact Finset.le_sup' (fun candidate => |difference candidate|)
        (Finset.mem_univ state)
    have hmaxZero : difference maxState = 0 := by
      by_contra hne
      have hpositive : 0 < |difference maxState| := abs_pos.mpr hne
      have hcontract := abs_Q_pow_mulVec_le_survival D difference
        |difference maxState| hmax (n + 1) maxState
      have hequalAbs :
          |difference maxState| =
            |(D.Q ^ (n + 1) *ᵥ difference) maxState| :=
        congrArg (fun value : ℚ => |value|)
          (congrFun (eq_pow_mulVec_of_fixed D difference hfixed (n + 1)) maxState)
      rw [← hequalAbs] at hcontract
      have hrow : D.survival (n + 1) maxState ≤
          (D.autoBound : ℚ) := hrows maxState
      have hbound :
          D.survival (n + 1) maxState * |difference maxState| ≤
            (D.autoBound : ℚ) * |difference maxState| :=
        mul_le_mul_of_nonneg_right hrow (abs_nonneg _)
      have hstrict :
          (D.autoBound : ℚ) * |difference maxState| <
            |difference maxState| := by
        nlinarith
      exact (not_lt_of_ge (hcontract.trans hbound)) hstrict
    funext state
    apply abs_eq_zero.mp
    apply le_antisymm
    · simpa [hmaxZero] using hmax state
    · exact abs_nonneg _

private lemma det_one_sub_Q_ne_zero_of_autoCheck (D : Chain n m)
    (hcheck : D.autoCheck = true) : (1 - D.Q).det ≠ 0 := by
  have hinjective : Function.Injective (1 - D.Q).mulVec := by
    intro left right hequal
    have hzero : (1 - D.Q) *ᵥ (left - right) = 0 := by
      rw [Matrix.mulVec_sub, hequal, sub_self]
    have hfixed : left - right = D.Q *ᵥ (left - right) := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec] at hzero
      exact sub_eq_zero.mp hzero
    exact sub_eq_zero.mp (eq_zero_of_fixed_of_autoCheck D hcheck _ hfixed)
  exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp
    (Matrix.mulVec_injective_iff_isUnit.mp hinjective))

/-- Purely rational nonsingularity of the generated parity Bellman matrix.
The proof uses the automatically computed strict survival contraction; no
analytic series, inverse, or caller certificate appears. -/
theorem parityMatrix_det_ne_zero
    (priority : TotalState n m → ℕ) :
    (1 - (C.parityChain priority).Q).det ≠ 0 :=
  det_one_sub_Q_ne_zero_of_autoCheck _ (C.parityChain_autoCheck priority)

private theorem bellman_solution_nonneg_of_autoCheck
    (D : Chain n m) (hcheck : D.autoCheck = true)
    (rhs value : Fin n → ℚ) (hrhs : ∀ state, 0 ≤ rhs state)
    (hvalue : value = rhs + D.Q *ᵥ value) :
    ∀ state, 0 ≤ value state := by
  intro state
  cases isEmpty_or_nonempty (Fin n)
  · exact isEmptyElim state
  · have huniv : (Finset.univ : Finset (Fin n)).Nonempty :=
      Finset.univ_nonempty
    obtain ⟨minState, _, hmin⟩ :=
      Finset.exists_min_image Finset.univ value huniv
    by_contra hnegative
    have hminNegative : value minState < 0 :=
      (hmin state (Finset.mem_univ state)).trans_lt (lt_of_not_ge hnegative)
    have hadmissible : D.admissible (n + 1) D.autoBound = true := hcheck
    obtain ⟨_, _, hc1, hrows⟩ :=
      (D.admissible_iff (n + 1) D.autoBound).mp hadmissible
    have hprefix :
        0 ≤ (∑ step ∈ Finset.range (n + 1), D.Q ^ step *ᵥ rhs) minState := by
      rw [Finset.sum_apply]
      apply Finset.sum_nonneg
      intro step _
      simp only [Matrix.mulVec, dotProduct]
      exact Finset.sum_nonneg fun target _ =>
        mul_nonneg (D.pow_nonneg step minState target) (hrhs target)
    have hremainder :
        D.survival (n + 1) minState * value minState ≤
          (D.Q ^ (n + 1) *ᵥ value) minState := by
      change (∑ target, (D.Q ^ (n + 1)) minState target) * value minState ≤
        ∑ target, (D.Q ^ (n + 1)) minState target * value target
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum fun target _ =>
        mul_le_mul_of_nonneg_left
          (hmin target (Finset.mem_univ target))
          (D.pow_nonneg (n + 1) minState target)
    have hunroll := congrFun (D.bellman_unroll rhs value hvalue (n + 1)) minState
    simp only [Pi.add_apply] at hunroll
    have hself : D.survival (n + 1) minState * value minState ≤
        value minState := by
      calc
        D.survival (n + 1) minState * value minState ≤
            (D.Q ^ (n + 1) *ᵥ value) minState := hremainder
        _ ≤ (∑ r ∈ Finset.range (n + 1), D.Q ^ r *ᵥ rhs) minState +
            (D.Q ^ (n + 1) *ᵥ value) minState := by linarith
        _ = value minState := hunroll.symm
    have hsurvival : D.survival (n + 1) minState < 1 :=
      (hrows minState).trans_lt hc1
    have hsurvivalNonneg := D.survival_nonneg (n + 1) minState
    have hstrict : value minState <
        D.survival (n + 1) minState * value minState := by
      nlinarith
    exact (not_lt_of_ge hself) hstrict

/-! ## Accepting and rejecting Bellman vectors -/

/-- Accepting-outcome Bellman right-hand side. -/
def parityAcceptRhs (priority : TotalState n m → ℕ) :
    TotalState n m → ℚ :=
  (C.parityChain priority).R *ᵥ fun outcome => if outcome = 0 then 1 else 0

/-- Rejecting/nonaccepting-outcome Bellman right-hand side. -/
def parityRejectRhs (priority : TotalState n m → ℕ) :
    TotalState n m → ℚ :=
  (C.parityChain priority).R *ᵥ fun outcome => if outcome = 1 then 1 else 0

/-- The accepting Bellman right-hand side is exactly terminal column zero of
the two-terminal parity reduction. -/
theorem parityAcceptRhs_eq_terminalColumn_zero
    (priority : TotalState n m → ℕ) :
    C.parityAcceptRhs priority =
      fun state => (C.parityChain priority).R state 0 := by
  funext state
  simp [parityAcceptRhs, Matrix.mulVec, dotProduct]

/-- The rejecting Bellman right-hand side is exactly terminal column one of
the two-terminal parity reduction. -/
theorem parityRejectRhs_eq_terminalColumn_one
    (priority : TotalState n m → ℕ) :
    C.parityRejectRhs priority =
      fun state => (C.parityChain priority).R state 1 := by
  funext state
  simp [parityRejectRhs, Matrix.mulVec, dotProduct]

/-- Direct Cramer vector for entry into an accepting bottom SCC. -/
def parityAcceptingVector
    (priority : TotalState n m → ℕ) : TotalState n m → ℚ :=
  let A := 1 - (C.parityChain priority).Q
  A.det⁻¹ • A.cramer (C.parityAcceptRhs priority)

/-- The accepting Cramer vector satisfies its exact rational system. -/
theorem parityAcceptingVector_system
    (priority : TotalState n m → ℕ) :
    (1 - (C.parityChain priority).Q) *ᵥ C.parityAcceptingVector priority =
      C.parityAcceptRhs priority := by
  have hdet := C.parityMatrix_det_ne_zero priority
  unfold parityAcceptingVector
  rw [Matrix.mulVec_smul, Matrix.mulVec_cramer, smul_smul,
    inv_mul_cancel₀ hdet, one_smul]

/-- The accepting vector in Bellman fixed-point form. -/
theorem parityAcceptingVector_bellman
    (priority : TotalState n m → ℕ) :
    C.parityAcceptingVector priority = C.parityAcceptRhs priority +
      (C.parityChain priority).Q *ᵥ C.parityAcceptingVector priority := by
  have hsystem := C.parityAcceptingVector_system priority
  rw [Matrix.sub_mulVec, Matrix.one_mulVec] at hsystem
  exact sub_eq_iff_eq_add.mp hsystem

theorem parityAcceptRhs_nonneg
    (priority : TotalState n m → ℕ)
    (state : TotalState n m) :
    0 ≤ C.parityAcceptRhs priority state := by
  simp only [parityAcceptRhs, Matrix.mulVec, dotProduct]
  exact Finset.sum_nonneg fun outcome _ =>
    mul_nonneg ((C.parityChain priority).R_nonneg state outcome)
      (by split <;> simp)

theorem parityRejectRhs_nonneg
    (priority : TotalState n m → ℕ)
    (state : TotalState n m) :
    0 ≤ C.parityRejectRhs priority state := by
  simp only [parityRejectRhs, Matrix.mulVec, dotProduct]
  exact Finset.sum_nonneg fun outcome _ =>
    mul_nonneg ((C.parityChain priority).R_nonneg state outcome)
      (by split <;> simp)

/-- An accepting bottom state has immediate accepting exit mass one. -/
theorem parityAcceptRhs_eq_one_of_acceptingBottom
    (priority : TotalState n m → ℕ)
    (state : TotalState n m)
    (haccepting : C.IsAcceptingBottom priority state) :
    C.parityAcceptRhs priority state = 1 := by
  have hbottom : C.isBottom state = true :=
    (C.isBottom_eq_true_iff state).mpr haccepting.1
  have hacceptingBool : C.isAcceptingBottom priority state = true :=
    (C.isAcceptingBottom_eq_true_iff priority state).mpr haccepting
  simp [parityAcceptRhs, Chain.R, parityChain, parityTerminal, Matrix.mulVec,
    dotProduct, hbottom, hacceptingBool]

/-- A rejecting bottom state has immediate accepting exit mass zero. -/
theorem parityAcceptRhs_eq_zero_of_rejectingBottom
    (priority : TotalState n m → ℕ)
    (state : TotalState n m)
    (hbottom : C.IsBottom state)
    (hrejecting : ¬ C.IsAcceptingBottom priority state) :
    C.parityAcceptRhs priority state = 0 := by
  have hbottomBool : C.isBottom state = true :=
    (C.isBottom_eq_true_iff state).mpr hbottom
  have hacceptingBool : C.isAcceptingBottom priority state = false :=
    (C.isAcceptingBottom_eq_false_iff priority state).mpr hrejecting
  simp [parityAcceptRhs, Chain.R, parityChain, parityTerminal, Matrix.mulVec,
    dotProduct, hbottomBool, hacceptingBool]

/-- Accepting and rejecting one-step exits, together with the transient row,
partition the complete normalized row. -/
theorem parity_rhs_row_identity
    (priority : TotalState n m → ℕ)
    (state : TotalState n m) :
    C.parityAcceptRhs priority state + C.parityRejectRhs priority state +
      ((C.parityChain priority).Q *ᵥ fun _ => 1) state = 1 := by
  have hrow := (C.parityChain priority).row_sum state
  simpa [parityAcceptRhs, parityRejectRhs, Matrix.mulVec, dotProduct,
    add_comm, add_left_comm, add_assoc]
    using hrow

/-- Explicit mass of rejecting bottom SCCs.  This includes every closed
nonterminal class whose minimum recurring priority is odd. -/
def parityNonacceptingVector
    (priority : TotalState n m → ℕ) : TotalState n m → ℚ :=
  fun state => 1 - C.parityAcceptingVector priority state

/-- The complementary vector satisfies the rejecting Bellman equation. -/
theorem parityNonacceptingVector_bellman
    (priority : TotalState n m → ℕ) :
    C.parityNonacceptingVector priority = C.parityRejectRhs priority +
      (C.parityChain priority).Q *ᵥ C.parityNonacceptingVector priority := by
  funext state
  have haccept := congrFun (C.parityAcceptingVector_bellman priority) state
  simp only [Pi.add_apply, Matrix.mulVec, dotProduct] at haccept
  have hrow := C.parity_rhs_row_identity priority state
  simp only [parityNonacceptingVector, Matrix.mulVec, dotProduct, mul_sub,
    mul_one, Finset.sum_sub_distrib, Pi.add_apply]
  simp only [Matrix.mulVec, dotProduct, mul_one] at hrow
  linarith

/-- Rejecting Cramer system, derived from exact complementarity. -/
theorem parityNonacceptingVector_system
    (priority : TotalState n m → ℕ) :
    (1 - (C.parityChain priority).Q) *ᵥ C.parityNonacceptingVector priority =
      C.parityRejectRhs priority := by
  rw [Matrix.sub_mulVec, Matrix.one_mulVec]
  exact sub_eq_iff_eq_add.mpr
    (C.parityNonacceptingVector_bellman priority)

/-- The direct accepting Cramer vector is exactly the reachability
solver's first-terminal vector on the two-terminal parity reduction.

All states of the reduction can reach a terminal, so the reachability solver's
automatic pruning leaves both its transient matrix and right-hand side
unchanged.  This is an equality between finite rational algorithms; it makes
no claim about an infinite-path event measure. -/
theorem parityAcceptingVector_eq_terminalProbability_zero
    (priority : TotalState n m → ℕ) :
    C.parityAcceptingVector priority =
      (C.parityChain priority).terminalProbability 0 := by
  rw [parityAcceptingVector,
    C.parityAcceptRhs_eq_terminalColumn_zero priority]
  unfold terminalProbability solveReachable reachabilityMatrix
  rw [show (C.parityChain priority).reachableQ =
      (C.parityChain priority).Q by
    funext source target
    exact (C.parityChain priority).reachableQ_of_reachable source target
      (C.parityChain_canReachTerminal priority source)
      (C.parityChain_canReachTerminal priority target)]
  rw [show (C.parityChain priority).reachableRhs
      (fun state => (C.parityChain priority).R state 0) =
        (fun state => (C.parityChain priority).R state 0) by
    funext state
    simp [Chain.reachableRhs,
      C.parityChain_canReachTerminal priority state]]

/-- The complementary rejecting vector is the reachability solver's
second-terminal vector on the same parity reduction.

As for the accepting vector, this theorem identifies two finite Cramer
computations.  It does not add measure-theoretic omega-event semantics. -/
theorem parityNonacceptingVector_eq_terminalProbability_one
    (priority : TotalState n m → ℕ) :
    C.parityNonacceptingVector priority =
      (C.parityChain priority).terminalProbability 1 := by
  let D := C.parityChain priority
  let A := 1 - D.Q
  have hy :
      A *ᵥ (A.det⁻¹ • A.cramer (C.parityRejectRhs priority)) =
        C.parityRejectRhs priority := by
    rw [Matrix.mulVec_smul, Matrix.mulVec_cramer, smul_smul,
      inv_mul_cancel₀ (C.parityMatrix_det_ne_zero priority), one_smul]
  have hvector :
      C.parityNonacceptingVector priority =
        A.det⁻¹ • A.cramer (C.parityRejectRhs priority) := by
    apply solveLinear_unique A (C.parityMatrix_det_ne_zero priority)
    exact (C.parityNonacceptingVector_system priority).trans hy.symm
  rw [hvector, C.parityRejectRhs_eq_terminalColumn_one priority]
  unfold terminalProbability solveReachable reachabilityMatrix
  rw [show D.reachableQ = D.Q by
    funext source target
    exact D.reachableQ_of_reachable source target
      (C.parityChain_canReachTerminal priority source)
      (C.parityChain_canReachTerminal priority target)]
  rw [show D.reachableRhs (fun state => D.R state 1) =
      (fun state => D.R state 1) by
    funext state
    simp [D, Chain.reachableRhs,
      C.parityChain_canReachTerminal priority state]]

/-- The accepting Bellman solution is unique. -/
theorem parityAcceptingVector_unique
    (priority : TotalState n m → ℕ)
    {candidate : TotalState n m → ℚ}
    (hcandidate : candidate = C.parityAcceptRhs priority +
      (C.parityChain priority).Q *ᵥ candidate) :
    candidate = C.parityAcceptingVector priority := by
  have hsystem :
      (1 - (C.parityChain priority).Q) *ᵥ candidate =
        C.parityAcceptRhs priority := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    exact sub_eq_iff_eq_add.mpr hcandidate
  exact solveLinear_unique _ (C.parityMatrix_det_ne_zero priority)
    (hsystem.trans (C.parityAcceptingVector_system priority).symm)

/-- The rejecting/nonaccepting Bellman solution is unique. -/
theorem parityNonacceptingVector_unique
    (priority : TotalState n m → ℕ)
    {candidate : TotalState n m → ℚ}
    (hcandidate : candidate = C.parityRejectRhs priority +
      (C.parityChain priority).Q *ᵥ candidate) :
    candidate = C.parityNonacceptingVector priority := by
  have hsystem :
      (1 - (C.parityChain priority).Q) *ᵥ candidate =
        C.parityRejectRhs priority := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    exact sub_eq_iff_eq_add.mpr hcandidate
  exact solveLinear_unique _ (C.parityMatrix_det_ne_zero priority)
    (hsystem.trans (C.parityNonacceptingVector_system priority).symm)

theorem parityAcceptingVector_nonneg
    (priority : TotalState n m → ℕ)
    (state : TotalState n m) :
    0 ≤ C.parityAcceptingVector priority state := by
  exact bellman_solution_nonneg_of_autoCheck
    (C.parityChain priority) (C.parityChain_autoCheck priority)
    (C.parityAcceptRhs priority) (C.parityAcceptingVector priority)
    (C.parityAcceptRhs_nonneg priority)
    (C.parityAcceptingVector_bellman priority) state

theorem parityNonacceptingVector_nonneg
    (priority : TotalState n m → ℕ)
    (state : TotalState n m) :
    0 ≤ C.parityNonacceptingVector priority state := by
  exact bellman_solution_nonneg_of_autoCheck
    (C.parityChain priority) (C.parityChain_autoCheck priority)
    (C.parityRejectRhs priority) (C.parityNonacceptingVector priority)
    (C.parityRejectRhs_nonneg priority)
    (C.parityNonacceptingVector_bellman priority) state

theorem parityAcceptingVector_le_one
    (priority : TotalState n m → ℕ)
    (state : TotalState n m) :
    C.parityAcceptingVector priority state ≤ 1 := by
  have := C.parityNonacceptingVector_nonneg priority state
  simpa [parityNonacceptingVector] using this

/-- Acceptance is already decided on an accepting bottom SCC. -/
theorem parityAcceptingVector_eq_one_of_acceptingBottom
    (priority : TotalState n m → ℕ)
    (state : TotalState n m)
    (haccepting : C.IsAcceptingBottom priority state) :
    C.parityAcceptingVector priority state = 1 := by
  have hbottom : C.isBottom state = true :=
    (C.isBottom_eq_true_iff state).mpr haccepting.1
  have hcontinuation :
      ((C.parityChain priority).Q *ᵥ
        C.parityAcceptingVector priority) state = 0 := by
    simp [Matrix.mulVec, dotProduct, Chain.Q, parityChain,
      parityTransient, hbottom]
  have hbellman := congrFun (C.parityAcceptingVector_bellman priority) state
  simp only [Pi.add_apply, hcontinuation, add_zero] at hbellman
  rw [C.parityAcceptRhs_eq_one_of_acceptingBottom priority state haccepting]
    at hbellman
  exact hbellman

/-- Acceptance is zero on a rejecting bottom SCC. -/
theorem parityAcceptingVector_eq_zero_of_rejectingBottom
    (priority : TotalState n m → ℕ)
    (state : TotalState n m)
    (hbottomProp : C.IsBottom state)
    (hrejecting : ¬ C.IsAcceptingBottom priority state) :
    C.parityAcceptingVector priority state = 0 := by
  have hbottom : C.isBottom state = true :=
    (C.isBottom_eq_true_iff state).mpr hbottomProp
  have hcontinuation :
      ((C.parityChain priority).Q *ᵥ
        C.parityAcceptingVector priority) state = 0 := by
    simp [Matrix.mulVec, dotProduct, Chain.Q, parityChain,
      parityTransient, hbottom]
  have hbellman := congrFun (C.parityAcceptingVector_bellman priority) state
  simp only [Pi.add_apply, hcontinuation, add_zero] at hbellman
  rw [C.parityAcceptRhs_eq_zero_of_rejectingBottom priority state
    hbottomProp hrejecting] at hbellman
  exact hbellman

theorem parityNonacceptingVector_le_one
    (priority : TotalState n m → ℕ)
    (state : TotalState n m) :
    C.parityNonacceptingVector priority state ≤ 1 := by
  have := C.parityAcceptingVector_nonneg priority state
  simp [parityNonacceptingVector]
  exact this

/-- A total exact parity solution.  Both masses are explicit, lie in `[0,1]`,
sum to one, and satisfy their own rational Bellman systems. -/
structure ParitySolution (priority : TotalState n m → ℕ) where
  /-- Probability of entering an accepting bottom SCC. -/
  accepting : TotalState n m → ℚ
  /-- Probability of entering a rejecting bottom SCC, including every closed
  nonterminating class whose min priority is odd. -/
  nonaccepting : TotalState n m → ℚ
  accepting_nonneg : ∀ state, 0 ≤ accepting state
  accepting_le_one : ∀ state, accepting state ≤ 1
  nonaccepting_nonneg : ∀ state, 0 ≤ nonaccepting state
  nonaccepting_le_one : ∀ state, nonaccepting state ≤ 1
  complementary : ∀ state, accepting state + nonaccepting state = 1
  accepting_system :
    (1 - (C.parityChain priority).Q) *ᵥ accepting = C.parityAcceptRhs priority
  nonaccepting_system :
    (1 - (C.parityChain priority).Q) *ᵥ nonaccepting = C.parityRejectRhs priority

/-! ## Executable result and correctness -/

/-- Automatically solve the parity Bellman system.  The caller supplies no
SCC list, candidate probability vector, inverse, or determinant certificate.
The construction is total for every normalized finite rational chain. -/
def solveParity
    (priority : TotalState n m → ℕ) :
    C.ParitySolution priority where
  accepting := C.parityAcceptingVector priority
  nonaccepting := C.parityNonacceptingVector priority
  accepting_nonneg := C.parityAcceptingVector_nonneg priority
  accepting_le_one := C.parityAcceptingVector_le_one priority
  nonaccepting_nonneg := C.parityNonacceptingVector_nonneg priority
  nonaccepting_le_one := C.parityNonacceptingVector_le_one priority
  complementary := fun state => by simp [parityNonacceptingVector]
  accepting_system := C.parityAcceptingVector_system priority
  nonaccepting_system := C.parityNonacceptingVector_system priority

/-- Exact accepting-BSCC first-entry probability at a start state. -/
def parityProbability
    (priority : TotalState n m → ℕ) (start : TotalState n m) :
    ℚ :=
  (C.solveParity priority).accepting start

/-- Explicit rejecting/nonaccepting mass at a start state. -/
def parityNonacceptingProbability
    (priority : TotalState n m → ℕ) (start : TotalState n m) :
    ℚ :=
  (C.solveParity priority).nonaccepting start

/-- The reported accepting value is terminal-zero first-entry value in the
finite two-terminal parity reduction. -/
theorem parityProbability_eq_terminalProbability_zero
    (priority : TotalState n m → ℕ) (start : TotalState n m) :
    C.parityProbability priority start =
      (C.parityChain priority).terminalProbability 0 start := by
  simpa [parityProbability, solveParity] using
    congrFun (C.parityAcceptingVector_eq_terminalProbability_zero priority)
      start

/-- The reported nonaccepting value is terminal-one first-entry value in the
finite two-terminal parity reduction. -/
theorem parityNonacceptingProbability_eq_terminalProbability_one
    (priority : TotalState n m → ℕ) (start : TotalState n m) :
    C.parityNonacceptingProbability priority start =
      (C.parityChain priority).terminalProbability 1 start := by
  simpa [parityNonacceptingProbability, solveParity] using
    congrFun (C.parityNonacceptingVector_eq_terminalProbability_one priority)
      start

theorem parityProbability_bounds
    (priority : TotalState n m → ℕ) (start : TotalState n m) :
    0 ≤ C.parityProbability priority start ∧
      C.parityProbability priority start ≤ 1 :=
  ⟨(C.solveParity priority).accepting_nonneg start,
    (C.solveParity priority).accepting_le_one start⟩

theorem parityNonacceptingProbability_bounds
    (priority : TotalState n m → ℕ) (start : TotalState n m) :
    0 ≤ C.parityNonacceptingProbability priority start ∧
      C.parityNonacceptingProbability priority start ≤ 1 :=
  ⟨(C.solveParity priority).nonaccepting_nonneg start,
    (C.solveParity priority).nonaccepting_le_one start⟩

theorem parityProbabilities_complementary
    (priority : TotalState n m → ℕ) (start : TotalState n m) :
    C.parityProbability priority start +
      C.parityNonacceptingProbability priority start = 1 :=
  (C.solveParity priority).complementary start

/-- Every returned accepting vector satisfies the exact Bellman equation. -/
theorem solveParity_accepting_bellman
    (priority : TotalState n m → ℕ)
    : (C.solveParity priority).accepting = C.parityAcceptRhs priority +
      (C.parityChain priority).Q *ᵥ (C.solveParity priority).accepting := by
  have hsystem := (C.solveParity priority).accepting_system
  rw [Matrix.sub_mulVec, Matrix.one_mulVec] at hsystem
  exact sub_eq_iff_eq_add.mp hsystem

/-- Every returned nonaccepting vector satisfies its exact Bellman equation. -/
theorem solveParity_nonaccepting_bellman
    (priority : TotalState n m → ℕ)
    : (C.solveParity priority).nonaccepting = C.parityRejectRhs priority +
      (C.parityChain priority).Q *ᵥ (C.solveParity priority).nonaccepting := by
  have hsystem := (C.solveParity priority).nonaccepting_system
  rw [Matrix.sub_mulVec, Matrix.one_mulVec] at hsystem
  exact sub_eq_iff_eq_add.mp hsystem

/-- Consolidated total correctness theorem for the executable solver. -/
theorem solveParity_correct
    (priority : TotalState n m → ℕ) :
    (∀ state,
      0 ≤ (C.solveParity priority).accepting state ∧
      (C.solveParity priority).accepting state ≤ 1 ∧
      0 ≤ (C.solveParity priority).nonaccepting state ∧
      (C.solveParity priority).nonaccepting state ≤ 1 ∧
      (C.solveParity priority).accepting state +
        (C.solveParity priority).nonaccepting state = 1) ∧
    (C.solveParity priority).accepting = C.parityAcceptRhs priority +
      (C.parityChain priority).Q *ᵥ (C.solveParity priority).accepting ∧
    (C.solveParity priority).nonaccepting = C.parityRejectRhs priority +
      (C.parityChain priority).Q *ᵥ (C.solveParity priority).nonaccepting ∧
    (∀ candidate,
      candidate = C.parityAcceptRhs priority +
        (C.parityChain priority).Q *ᵥ candidate →
      candidate = (C.solveParity priority).accepting) ∧
    (∀ candidate,
      candidate = C.parityRejectRhs priority +
        (C.parityChain priority).Q *ᵥ candidate →
      candidate = (C.solveParity priority).nonaccepting) := by
  refine ⟨fun state => ⟨
      (C.solveParity priority).accepting_nonneg state,
      (C.solveParity priority).accepting_le_one state,
      (C.solveParity priority).nonaccepting_nonneg state,
      (C.solveParity priority).nonaccepting_le_one state,
      (C.solveParity priority).complementary state⟩,
    C.solveParity_accepting_bellman priority,
    C.solveParity_nonaccepting_bellman priority, ?_, ?_⟩
  · intro candidate hcandidate
    simpa [solveParity] using
      C.parityAcceptingVector_unique priority hcandidate
  · intro candidate hcandidate
    simpa [solveParity] using
      C.parityNonacceptingVector_unique priority hcandidate

end FiniteMarkovChain.Chain
