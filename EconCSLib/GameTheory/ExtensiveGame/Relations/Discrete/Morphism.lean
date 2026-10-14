/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Execution.StoppedExecution

/-!
# EconCSLib.GameTheory.ExtensiveGame.Relations.Discrete.Morphism

Strict morphisms, relational simulations, weak simulations, and history
transport for `Arena`.

These interfaces intentionally distinguish three strengths:

* `Arena.Hom` maps every source step to one target step.
* `Arena.Iso` uses equivalences on states and dependent action types.
* `Arena.Simulation` relates states and only asks that each source step can be
  matched by some target step; `Arena.Bisimulation` adds the converse.
* `Arena.WeakSimulation` permits one source step to be represented by a finite
  target history, including administrative stuttering; `WeakBisimulation`
  adds the converse.

Strict morphisms induce functions on typed histories.  Relational simulations
instead give existence of a matching target history.  Exact stopped-execution
naturality additionally requires terminality and the two history policies to
be preserved.

Strict Arena isomorphisms support identity, composition, and reversal; the
inverse action map includes the required dependent transport along the inverse
state equivalence.
-/

namespace Arena

universe uAAction uAState uBAction uBState

/-- A strict one-step morphism of Arenas. -/
structure Hom
    (A : Arena.{uAAction, uAState})
    (B : Arena.{uBAction, uBState}) where
  /-- Map source states to target states. -/
  state : A.State → B.State
  /-- Map each dependent source action to a legal target action. -/
  action : (s : A.State) → A.Action s → B.Action (state s)
  /-- State and action maps commute with one-step transition. -/
  map_next :
    ∀ (s : A.State) (a : A.Action s),
      state (A.next s a) = B.next (state s) (action s a)

namespace Hom

variable {A B C : Arena}

/-- Strict Arena morphisms are equal when their state and dependent action
maps are equal. -/
@[ext]
theorem ext (f g : A.Hom B)
    (hstate : f.state = g.state)
    (haction : HEq f.action g.action) :
    f = g := by
  cases f
  cases g
  cases hstate
  cases haction
  rfl

/-- Identity strict Arena morphism. -/
def id (A : Arena) : A.Hom A where
  state := _root_.id
  action := fun _ => _root_.id
  map_next := by
    intro s a
    rfl

/-- Composition of strict Arena morphisms. -/
def comp (g : B.Hom C) (f : A.Hom B) : A.Hom C where
  state := g.state ∘ f.state
  action := fun s a => g.action (f.state s) (f.action s a)
  map_next := by
    intro s a
    calc
      (g.state ∘ f.state) (A.next s a) =
          g.state (f.state (A.next s a)) := rfl
      _ = g.state (B.next (f.state s) (f.action s a)) :=
        congrArg g.state (f.map_next s a)
      _ = C.next (g.state (f.state s))
          (g.action (f.state s) (f.action s a)) :=
        g.map_next (f.state s) (f.action s a)

@[simp]
theorem id_state (s : A.State) : (Hom.id A).state s = s := rfl

@[simp]
theorem id_action (s : A.State) (a : A.Action s) :
    (Hom.id A).action s a = a := rfl

@[simp]
theorem comp_state (g : B.Hom C) (f : A.Hom B) (s : A.State) :
    (g.comp f).state s = g.state (f.state s) := rfl

@[simp]
theorem comp_action (g : B.Hom C) (f : A.Hom B)
    (s : A.State) (a : A.Action s) :
    (g.comp f).action s a = g.action (f.state s) (f.action s a) := rfl

/-- Identity is a left unit for strict Arena morphism composition. -/
@[simp]
theorem id_comp (f : A.Hom B) :
    f.comp (Hom.id A) = f := by
  apply Hom.ext
  · rfl
  · apply heq_of_eq
    funext state action
    rfl

/-- Identity is a right unit for strict Arena morphism composition. -/
@[simp]
theorem comp_id (f : A.Hom B) :
    (Hom.id B).comp f = f := by
  apply Hom.ext
  · rfl
  · apply heq_of_eq
    funext state action
    rfl

/-- Composition of strict Arena morphisms is associative. -/
theorem comp_assoc {D : Arena}
    (h : C.Hom D) (g : B.Hom C) (f : A.Hom B) :
    (h.comp g).comp f = h.comp (g.comp f) := by
  apply Hom.ext
  · rfl
  · apply heq_of_eq
    funext state action
    rfl

/-- Strictly map a typed source history to a typed target history. -/
def mapHistory (f : A.Hom B) {start s : A.State} :
    A.History start s → B.History (f.state start) (f.state s)
  | .nil => .nil
  | @History.snoc _ _ _ current action => by
      rw [f.map_next]
      exact (f.mapHistory current).snoc (f.action _ action)

@[simp]
theorem mapHistory_nil (f : A.Hom B) (start : A.State) :
    f.mapHistory (History.nil : A.History start start) = History.nil := rfl

/-- Mapping a snoc history is the mapped snoc, transported only at the endpoint
index.  The explicit normal form prevents the implementation proof generated
by `rw` from leaking into downstream proofs. -/
theorem mapHistory_snoc (f : A.Hom B) {start s : A.State}
    (history : A.History start s) (action : A.Action s) :
    f.mapHistory (history.snoc action) =
      (f.map_next s action).symm ▸
        (f.mapHistory history).snoc (f.action s action) := by
  simp only [mapHistory]
  apply eq_of_heq
  exact
    (cast_heq _ ((f.mapHistory history).snoc (f.action s action))).trans
      (rec_heq_of_heq _ HEq.rfl).symm

/-- Mapping commutes with transport of the endpoint index.  This isolates the
dependent cast generated by `map_next` from downstream functoriality proofs. -/
theorem mapHistory_cast (f : A.Hom B) {start s t : A.State}
    (h : s = t) (history : A.History start s) :
    f.mapHistory (h ▸ history) =
      congrArg f.state h ▸ f.mapHistory history := by
  cases h
  rfl

/-- Map a history bundled with its endpoint. -/
def mapHistoryFrom (f : A.Hom B) {start : A.State}
    (h : A.HistoryFrom start) :
    B.HistoryFrom (f.state start) :=
  ⟨f.state h.1, f.mapHistory h.2⟩

@[simp]
theorem mapHistoryFrom_fst (f : A.Hom B) {start : A.State}
    (h : A.HistoryFrom start) :
    (f.mapHistoryFrom h).1 = f.state h.1 := rfl

@[simp]
theorem mapHistoryFrom_nil (f : A.Hom B) (start : A.State) :
    f.mapHistoryFrom (HistoryFrom.nil A start) =
      HistoryFrom.nil B (f.state start) := rfl

/-- Mapping a snoc history agrees with taking the mapped target step. -/
theorem mapHistoryFrom_snoc (f : A.Hom B) {start s : A.State}
    (h : A.History start s) (a : A.Action s) :
    f.mapHistoryFrom ⟨A.next s a, h.snoc a⟩ =
      ⟨B.next (f.state s) (f.action s a),
        (f.mapHistory h).snoc (f.action s a)⟩ := by
  apply Sigma.ext (f.map_next s a)
  simp [mapHistoryFrom, mapHistory]

/-- Identity mapping leaves every typed history unchanged. -/
@[simp]
theorem id_mapHistory {start finish : A.State}
    (history : A.History start finish) :
    (Hom.id A).mapHistory history = history := by
  induction history with
  | nil => rfl
  | snoc history action ih =>
      simp [mapHistory, ih]

/-- Mapping a typed history is functorial under strict morphism composition. -/
@[simp]
theorem comp_mapHistory
    (g : B.Hom C) (f : A.Hom B)
    {start finish : A.State}
    (history : A.History start finish) :
    (g.comp f).mapHistory history =
      g.mapHistory (f.mapHistory history) := by
  induction history with
  | nil => rfl
  | snoc history action ih =>
      rw [mapHistory_snoc, mapHistory_snoc, mapHistory_cast,
        mapHistory_snoc, ih]
      apply eq_of_heq
      exact
        (rec_heq_of_heq _ HEq.rfl).trans
          (rec_heq_of_heq _ (rec_heq_of_heq _ HEq.rfl)).symm

/-- Identity mapping leaves bundled histories unchanged. -/
@[simp]
theorem id_mapHistoryFrom {start : A.State}
    (history : A.HistoryFrom start) :
    (Hom.id A).mapHistoryFrom history = history := by
  rcases history with ⟨finish, history⟩
  simp [mapHistoryFrom]

/-- Mapping a bundled history is functorial under strict morphism
composition. -/
@[simp]
theorem comp_mapHistoryFrom
    (g : B.Hom C) (f : A.Hom B)
    {start : A.State}
    (history : A.HistoryFrom start) :
    (g.comp f).mapHistoryFrom history =
      g.mapHistoryFrom (f.mapHistoryFrom history) := by
  rcases history with ⟨finish, history⟩
  simp [mapHistoryFrom]

/-- A strict morphism reflects terminality: a target-terminal mapped state
cannot have a source action. -/
theorem isTerminal_of_map_isTerminal (f : A.Hom B) {s : A.State}
    (hterminal : B.IsTerminal (f.state s)) :
    A.IsTerminal s :=
  ⟨fun action => hterminal.false (f.action s action)⟩

/-- A strict morphism maps genuine decision states to genuine decision
states. -/
theorem isDecision (f : A.Hom B) {s : A.State}
    (hdecision : A.IsDecision s) :
    B.IsDecision (f.state s) :=
  hdecision.map (f.action s)

/-- Exact terminality preservation along a strict Arena morphism. -/
def PreservesTerminal (f : A.Hom B) : Prop :=
  ∀ s : A.State, A.IsTerminal s ↔ B.IsTerminal (f.state s)

/-- Source and target history policies commute along a strict morphism.

The terminal proofs are quantified explicitly because the policies are
dependent functions; proof irrelevance ensures the property does not depend on
which proofs are supplied. -/
def PoliciesRelated (f : A.Hom B) {start : A.State}
    (source : A.HistoryPolicy start)
    (target : B.HistoryPolicy (f.state start)) : Prop :=
  ∀ (h : A.HistoryFrom start)
    (hsource : ¬ A.IsTerminal h.1)
    (htarget : ¬ B.IsTerminal (f.state h.1)),
    target (f.mapHistoryFrom h) htarget =
      f.action h.1 (source h hsource)

/-- Strict history mapping commutes with terminal-aware stopped execution when
the morphism preserves terminality and the two policies are related. -/
theorem map_stoppedHistoryFrom
    [(s : A.State) → Decidable (A.IsTerminal s)]
    [(t : B.State) → Decidable (B.IsTerminal t)]
    (f : A.Hom B) (hterminal : f.PreservesTerminal)
    {start : A.State}
    (source : A.HistoryPolicy start)
    (target : B.HistoryPolicy (f.state start))
    (hpolicy : f.PoliciesRelated source target)
    (current : A.HistoryFrom start) :
    ∀ fuel,
      f.mapHistoryFrom (A.stoppedHistoryFrom source current fuel) =
        B.stoppedHistoryFrom target (f.mapHistoryFrom current) fuel := by
  intro fuel
  induction fuel generalizing current with
  | zero =>
      rfl
  | succ fuel ih =>
      by_cases hsource : A.IsTerminal current.1
      · have htarget :
            B.IsTerminal (f.state current.1) :=
          (hterminal current.1).mp hsource
        rw [A.stoppedHistoryFrom_succ_of_terminal
          source current fuel hsource]
        rw [B.stoppedHistoryFrom_succ_of_terminal
          target (f.mapHistoryFrom current) fuel htarget]
      · have htarget :
            ¬ B.IsTerminal (f.state current.1) := by
          intro h
          exact hsource ((hterminal current.1).mpr h)
        rw [A.stoppedHistoryFrom_succ_of_not_terminal
          source current fuel hsource]
        rw [B.stoppedHistoryFrom_succ_of_not_terminal
          target (f.mapHistoryFrom current) fuel htarget]
        rw [ih]
        apply congrArg (fun next =>
          B.stoppedHistoryFrom target next fuel)
        rw [hpolicy current hsource htarget]
        exact f.mapHistoryFrom_snoc current.2 (source current hsource)

/-- Strict history mapping commutes with execution from the empty history. -/
theorem map_stoppedHistory
    [(s : A.State) → Decidable (A.IsTerminal s)]
    [(t : B.State) → Decidable (B.IsTerminal t)]
    (f : A.Hom B) (hterminal : f.PreservesTerminal)
    {start : A.State}
    (source : A.HistoryPolicy start)
    (target : B.HistoryPolicy (f.state start))
    (hpolicy : f.PoliciesRelated source target)
    (fuel : ℕ) :
    f.mapHistoryFrom (A.stoppedHistory source fuel) =
      B.stoppedHistory target fuel := by
  simpa [stoppedHistory] using
    f.map_stoppedHistoryFrom hterminal source target hpolicy
      (HistoryFrom.nil A start) fuel

end Hom

/-- The history unfolding projects strictly back to its compact Arena by
forgetting the path and retaining its endpoint. -/
def unfoldProjection (A : Arena) (start : A.State) :
    (A.unfoldFrom start).Hom A where
  state := fun history => history.1
  action := fun _ action => action
  map_next := by
    intro history action
    rfl

/-- Forgetting histories preserves terminality exactly. -/
theorem unfoldProjection_preservesTerminal (A : Arena) (start : A.State) :
    (A.unfoldProjection start).PreservesTerminal := by
  intro history
  rfl

/-! ### Strict Arena isomorphisms -/

/-- A strict Arena isomorphism: equivalences on states and each dependent
action type, commuting with transition. -/
structure Iso
    (A : Arena.{uAAction, uAState})
    (B : Arena.{uBAction, uBState}) where
  /-- Equivalence of state spaces. -/
  stateEquiv : A.State ≃ B.State
  /-- Equivalence of legal actions at corresponding states. -/
  actionEquiv :
    (s : A.State) → A.Action s ≃ B.Action (stateEquiv s)
  /-- Transition commutes with the two equivalences. -/
  map_next :
    ∀ (s : A.State) (a : A.Action s),
      stateEquiv (A.next s a) =
        B.next (stateEquiv s) (actionEquiv s a)

namespace Iso

variable {A B : Arena}

/-- Strict Arena isomorphisms are equal when their state equivalence and
dependent action-equivalence family are equal. -/
@[ext]
theorem ext (e f : A.Iso B)
    (hstate : e.stateEquiv = f.stateEquiv)
    (haction : HEq e.actionEquiv f.actionEquiv) :
    e = f := by
  cases e
  cases f
  cases hstate
  cases haction
  rfl

/-- Identity strict Arena isomorphism. -/
def refl (A : Arena) : A.Iso A where
  stateEquiv := Equiv.refl _
  actionEquiv := fun _ => Equiv.refl _
  map_next := by
    intro s a
    rfl

/-- Compose strict Arena isomorphisms. -/
def trans {C : Arena} (e : A.Iso B) (f : B.Iso C) : A.Iso C where
  stateEquiv := e.stateEquiv.trans f.stateEquiv
  actionEquiv := fun s =>
    (e.actionEquiv s).trans (f.actionEquiv (e.stateEquiv s))
  map_next := by
    intro s a
    calc
      f.stateEquiv (e.stateEquiv (A.next s a)) =
          f.stateEquiv
            (B.next (e.stateEquiv s) (e.actionEquiv s a)) :=
        congrArg f.stateEquiv (e.map_next s a)
      _ = C.next (f.stateEquiv (e.stateEquiv s))
          (f.actionEquiv (e.stateEquiv s) (e.actionEquiv s a)) :=
        f.map_next (e.stateEquiv s) (e.actionEquiv s a)

/-- The inverse dependent action equivalence at a target state. -/
def inverseActionEquiv (e : A.Iso B) (target : B.State) :
    B.Action target ≃ A.Action (e.stateEquiv.symm target) :=
  (Equiv.cast
      (congrArg B.Action
        (e.stateEquiv.apply_symm_apply target))).symm.trans
    (e.actionEquiv (e.stateEquiv.symm target)).symm

private theorem next_cast (B : Arena)
    {source target : B.State}
    (hstate : source = target)
    (action : B.Action target) :
    B.next target action =
      B.next source
        (cast (congrArg B.Action hstate).symm action) := by
  subst target
  rfl

/-- Reverse a strict Arena isomorphism. -/
def symm (e : A.Iso B) : B.Iso A where
  stateEquiv := e.stateEquiv.symm
  actionEquiv := e.inverseActionEquiv
  map_next := by
    intro target action
    apply e.stateEquiv.injective
    rw [e.stateEquiv.apply_symm_apply]
    rw [e.map_next]
    simpa [inverseActionEquiv] using
      (next_cast B
        (e.stateEquiv.apply_symm_apply target)
        action)

/-- Identity is a left unit for strict Arena isomorphism composition. -/
@[simp]
theorem refl_trans (e : A.Iso B) :
    (Iso.refl A).trans e = e := by
  apply Iso.ext
  · apply Equiv.ext
    intro state
    rfl
  · apply heq_of_eq
    funext state
    apply Equiv.ext
    intro action
    rfl

/-- Identity is a right unit for strict Arena isomorphism composition. -/
@[simp]
theorem trans_refl (e : A.Iso B) :
    e.trans (Iso.refl B) = e := by
  apply Iso.ext
  · apply Equiv.ext
    intro state
    rfl
  · apply heq_of_eq
    funext state
    apply Equiv.ext
    intro action
    rfl

/-- Composition of strict Arena isomorphisms is associative. -/
theorem trans_assoc {C D : Arena}
    (e : A.Iso B) (f : B.Iso C) (g : C.Iso D) :
    (e.trans f).trans g = e.trans (f.trans g) := by
  apply Iso.ext
  · apply Equiv.ext
    intro state
    rfl
  · apply heq_of_eq
    funext state
    apply Equiv.ext
    intro action
    rfl

/-- Forget invertibility and retain the forward strict morphism. -/
def toHom (e : A.Iso B) : A.Hom B where
  state := e.stateEquiv
  action := fun s a => e.actionEquiv s a
  map_next := e.map_next

/-- Arena isomorphisms preserve and reflect terminality. -/
theorem isTerminal_iff (e : A.Iso B) (s : A.State) :
    A.IsTerminal s ↔ B.IsTerminal (e.stateEquiv s) := by
  constructor
  · intro hsource
    exact ⟨fun targetAction =>
      hsource.false ((e.actionEquiv s).symm targetAction)⟩
  · exact e.toHom.isTerminal_of_map_isTerminal

/-- Arena isomorphisms preserve and reflect genuine decision states. -/
theorem isDecision_iff (e : A.Iso B) (s : A.State) :
    A.IsDecision s ↔ B.IsDecision (e.stateEquiv s) := by
  constructor
  · exact e.toHom.isDecision
  · intro htarget
    exact htarget.map (e.actionEquiv s).symm

/-- The underlying strict morphism of an Arena isomorphism preserves
terminality exactly. -/
theorem toHom_preservesTerminal (e : A.Iso B) :
    e.toHom.PreservesTerminal :=
  e.isTerminal_iff

end Iso

/-! ### Relational simulation -/

/-- A forward relational simulation: every related source step has a matching
target step.  The relation can express quotients, auxiliary target state, or
other non-functional correspondences. -/
structure Simulation
    (A : Arena.{uAAction, uAState})
    (B : Arena.{uBAction, uBState}) where
  /-- Relation between source and target states. -/
  Rel : A.State → B.State → Prop
  /-- Match every source step by one target step. -/
  match_step :
    ∀ {s : A.State} {t : B.State}, Rel s t →
      ∀ a : A.Action s,
        ∃ b : B.Action t, Rel (A.next s a) (B.next t b)

namespace Simulation

variable {A B : Arena}

/-- A related target terminal state forces the source state to be terminal. -/
theorem isTerminal_of_target (R : A.Simulation B)
    {s : A.State} {t : B.State} (hst : R.Rel s t)
    (ht : B.IsTerminal t) :
    A.IsTerminal s := by
  refine ⟨fun action => ?_⟩
  obtain ⟨targetAction, _⟩ := R.match_step hst action
  exact ht.false targetAction

/-- A forward simulation maps every finite source history to some target
history with a related endpoint. -/
theorem exists_history (R : A.Simulation B)
    {sourceStart sourceEnd : A.State} {targetStart : B.State}
    (hstart : R.Rel sourceStart targetStart)
    (history : A.History sourceStart sourceEnd) :
    ∃ targetEnd : B.State,
      Nonempty (B.History targetStart targetEnd) ∧
      R.Rel sourceEnd targetEnd := by
  induction history with
  | nil =>
      exact ⟨targetStart, ⟨History.nil⟩, hstart⟩
  | @snoc source currentHistory action ih =>
      obtain ⟨target, ⟨targetHistory⟩, hrelated⟩ := ih
      obtain ⟨targetAction, hnext⟩ :=
        R.match_step hrelated action
      exact
        ⟨B.next target targetAction,
          ⟨targetHistory.snoc targetAction⟩, hnext⟩

end Simulation

/-- Every strict Arena morphism induces its graph simulation. -/
def Hom.toSimulation {A B : Arena} (f : A.Hom B) :
    A.Simulation B where
  Rel := fun source target => f.state source = target
  match_step := by
    intro source target hrelated action
    subst target
    exact ⟨f.action source action, f.map_next source action⟩

/-- A relational bisimulation: related states can match one another's steps in
both directions. -/
structure Bisimulation
    (A : Arena.{uAAction, uAState})
    (B : Arena.{uBAction, uBState})
    extends A.Simulation B where
  /-- Match every target step by one source step. -/
  match_step_back :
    ∀ {s : A.State} {t : B.State}, Rel s t →
      ∀ b : B.Action t,
        ∃ a : A.Action s, Rel (A.next s a) (B.next t b)

namespace Bisimulation

variable {A B : Arena}

/-- Reverse a bisimulation by transposing its state relation. -/
def symm (R : A.Bisimulation B) : B.Bisimulation A where
  Rel := fun t s => R.Rel s t
  match_step := R.match_step_back
  match_step_back := R.match_step

/-- Related states in a bisimulation are terminal simultaneously. -/
theorem isTerminal_iff (R : A.Bisimulation B)
    {s : A.State} {t : B.State} (hst : R.Rel s t) :
    A.IsTerminal s ↔ B.IsTerminal t := by
  constructor
  · exact R.symm.toSimulation.isTerminal_of_target hst
  · exact R.toSimulation.isTerminal_of_target hst

end Bisimulation

/-- Every strict Arena isomorphism induces a bisimulation on the graph of its
state equivalence. -/
def Iso.toBisimulation {A B : Arena} (e : A.Iso B) :
    A.Bisimulation B where
  Rel := fun source target => e.stateEquiv source = target
  match_step := by
    intro source target hrelated action
    subst target
    exact ⟨e.actionEquiv source action, e.map_next source action⟩
  match_step_back := by
    intro source target hrelated targetAction
    subst target
    refine ⟨(e.actionEquiv source).symm targetAction, ?_⟩
    calc
      e.stateEquiv
          (A.next source ((e.actionEquiv source).symm targetAction)) =
          B.next (e.stateEquiv source)
            (e.actionEquiv source
              ((e.actionEquiv source).symm targetAction)) :=
        e.map_next source ((e.actionEquiv source).symm targetAction)
      _ = B.next (e.stateEquiv source) targetAction := by
        rw [(e.actionEquiv source).apply_symm_apply]

/-! ### Weak and stuttering simulation -/

/-- A weak forward simulation between Arenas.

Every source step may be implemented by a finite target history.  The matching
history may be empty, allowing genuine stuttering.  Termination is required to
agree at related macro states; this prevents a serialization from silently
turning a completed source trajectory into an unfinished target trajectory, or
vice versa. -/
structure WeakSimulation
    (A : Arena.{uAAction, uAState})
    (B : Arena.{uBAction, uBState}) where
  /-- Relation between source states and target macro states. -/
  Rel : A.State → B.State → Prop
  /-- Match every source step by a finite target execution fragment. -/
  match_step :
    ∀ {s : A.State} {t : B.State}, Rel s t →
      ∀ a : A.Action s,
        ∃ u : B.State,
          Nonempty (B.History t u) ∧ Rel (A.next s a) u
  /-- Related macro states terminate simultaneously. -/
  terminal_iff :
    ∀ {s : A.State} {t : B.State}, Rel s t →
      (A.IsTerminal s ↔ B.IsTerminal t)

namespace WeakSimulation

variable {A B : Arena}

/-- A weak simulation is progressing when every source step has a match using
at least one target transition.  FOSG serializations should normally prove
this stronger property; the underlying weak interface still permits zero-step
matches for abstraction and silent-step quotienting. -/
def Progressing (R : A.WeakSimulation B) : Prop :=
  ∀ {s : A.State} {t : B.State}, R.Rel s t →
    ∀ a : A.Action s,
      ∃ u : B.State, ∃ history : B.History t u,
        0 < history.length ∧ R.Rel (A.next s a) u

/-- A weak simulation maps every finite source history to a finite target
history with a related endpoint. -/
theorem exists_history (R : A.WeakSimulation B)
    {sourceStart sourceEnd : A.State} {targetStart : B.State}
    (hstart : R.Rel sourceStart targetStart)
    (history : A.History sourceStart sourceEnd) :
    ∃ targetEnd : B.State,
      Nonempty (B.History targetStart targetEnd) ∧
      R.Rel sourceEnd targetEnd := by
  induction history with
  | nil =>
      exact ⟨targetStart, ⟨History.nil⟩, hstart⟩
  | @snoc source currentHistory action ih =>
      obtain ⟨target, ⟨targetHistory⟩, hrelated⟩ := ih
      obtain ⟨nextTarget, ⟨stepHistory⟩, hnext⟩ :=
        R.match_step hrelated action
      exact
        ⟨nextTarget, ⟨targetHistory.append stepHistory⟩, hnext⟩

end WeakSimulation

/-- A one-step simulation with exact terminal agreement induces a weak
simulation whose matching fragments all have length one. -/
def Simulation.toWeakSimulation {A B : Arena} (R : A.Simulation B)
    (hterminal :
      ∀ {s : A.State} {t : B.State}, R.Rel s t →
        (A.IsTerminal s ↔ B.IsTerminal t)) :
    A.WeakSimulation B where
  Rel := R.Rel
  match_step := by
    intro source target hrelated action
    obtain ⟨targetAction, hnext⟩ := R.match_step hrelated action
    exact
      ⟨B.next target targetAction,
        ⟨History.nil.snoc targetAction⟩, hnext⟩
  terminal_iff := hterminal

/-- A terminal-preserving strict morphism induces a progressing weak
simulation. -/
def Hom.toWeakSimulation {A B : Arena} (f : A.Hom B)
    (hterminal : f.PreservesTerminal) :
    A.WeakSimulation B :=
  f.toSimulation.toWeakSimulation fun hrelated => by
    subst_vars
    exact hterminal _

/-- The weak simulation induced by a strict morphism uses a nonempty,
one-transition target fragment for every source step. -/
theorem Hom.toWeakSimulation_progressing {A B : Arena} (f : A.Hom B)
    (hterminal : f.PreservesTerminal) :
    (f.toWeakSimulation hterminal).Progressing := by
  intro source target hrelated action
  subst target
  refine
    ⟨B.next (f.state source) (f.action source action),
      History.nil.snoc (f.action source action), ?_, f.map_next source action⟩
  simp

/-- A weak bisimulation matches finite execution fragments in both
directions. -/
structure WeakBisimulation
    (A : Arena.{uAAction, uAState})
    (B : Arena.{uBAction, uBState})
    extends A.WeakSimulation B where
  /-- Match every target step by a finite source execution fragment. -/
  match_step_back :
    ∀ {s : A.State} {t : B.State}, Rel s t →
      ∀ b : B.Action t,
        ∃ u : A.State,
          Nonempty (A.History s u) ∧ Rel u (B.next t b)

namespace WeakBisimulation

variable {A B : Arena}

/-- Reverse a weak bisimulation by transposing its state relation. -/
def symm (R : A.WeakBisimulation B) : B.WeakBisimulation A where
  Rel := fun target source => R.Rel source target
  match_step := R.match_step_back
  terminal_iff := fun hrelated => (R.terminal_iff hrelated).symm
  match_step_back := R.match_step

end WeakBisimulation

/-- Every one-step bisimulation induces a weak bisimulation with no
stuttering. -/
def Bisimulation.toWeakBisimulation {A B : Arena}
    (R : A.Bisimulation B) :
    A.WeakBisimulation B where
  Rel := R.Rel
  match_step := by
    intro source target hrelated action
    obtain ⟨targetAction, hnext⟩ := R.match_step hrelated action
    exact
      ⟨B.next target targetAction,
        ⟨History.nil.snoc targetAction⟩, hnext⟩
  terminal_iff := R.isTerminal_iff
  match_step_back := by
    intro source target hrelated targetAction
    obtain ⟨sourceAction, hnext⟩ :=
      R.match_step_back hrelated targetAction
    exact
      ⟨A.next source sourceAction,
        ⟨History.nil.snoc sourceAction⟩, hnext⟩

end Arena
