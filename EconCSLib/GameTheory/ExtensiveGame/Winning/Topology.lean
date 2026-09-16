/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Winning.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Topology.Defs.Filter

/-!
# Prefix topology and measurable complete-play objectives

This module equips the measure-free `CompletePlayFromHistory` API with
operational prefix cylinders, prefix-open/closed predicates, finite-prefix
decision witnesses, and generated topology/measurable-space interfaces.

The definitions do not assert determinacy.  Open and closed objectives are the
input boundary for future Gale--Stewart theorems under their proper
perfect-information and no-chance hypotheses.  Arbitrary winning sets,
totality, and imperfect-information games receive no determinacy conclusion.

`PrefixDecision` from `Winning.Basic` certifies that every play reaches a
sound persistent winning history.  Under exclusivity, it yields a
finite-prefix decision witness and hence prefix openness for each player's
winning event.

## Main definitions

* `CompletePlayFromHistory.AgreeThrough`.
* `CompletePlayAgreementCylinderFrom`.
* `Arena.Set.IsPrefixOpenOn` and `Arena.Set.IsPrefixClosedOn`.
* `Arena.Set.HasFinitePrefixDecisionOn`.
* `CompletePlayFromHistory.prefixTopology`.
* `CompletePlayFromHistory.prefixMeasurableSpace`.
* `WinningConditionFrom.IsPrefixOpen` and `.IsPrefixClosed`.
-/

namespace Arena

variable {A : Arena} {start : A.State}
  {current : A.HistoryFrom start}

namespace CompletePlayFromHistory

/-- Two complete plays agree through coordinate `bound`, inclusive. -/
def AgreeThrough
    (bound : ℕ)
    (first second :
      A.CompletePlayFromHistory current) : Prop :=
  ∀ n, n ≤ bound →
    first.historyAt n = second.historyAt n

namespace AgreeThrough

/-- Prefix agreement is reflexive. -/
theorem refl (bound : ℕ)
    (play : A.CompletePlayFromHistory current) :
    AgreeThrough bound play play := by
  intro n hn
  rfl

/-- Prefix agreement is symmetric. -/
theorem symm {bound : ℕ}
    {first second :
      A.CompletePlayFromHistory current}
    (hagree : AgreeThrough bound first second) :
    AgreeThrough bound second first := by
  intro n hn
  exact (hagree n hn).symm

/-- Prefix agreement is transitive. -/
theorem trans {bound : ℕ}
    {first second third :
      A.CompletePlayFromHistory current}
    (hfirst : AgreeThrough bound first second)
    (hsecond : AgreeThrough bound second third) :
    AgreeThrough bound first third := by
  intro n hn
  exact (hfirst n hn).trans (hsecond n hn)

/-- Agreement through a longer prefix implies agreement through every shorter
prefix. -/
theorem mono {first second :
    A.CompletePlayFromHistory current}
    {short long : ℕ}
    (hagree : AgreeThrough long first second)
    (hle : short ≤ long) :
    AgreeThrough short first second := by
  intro n hn
  exact hagree n (hn.trans hle)

end AgreeThrough

end CompletePlayFromHistory

/-- The cylinder of plays agreeing with `play` through one finite prefix. -/
def CompletePlayAgreementCylinderFrom
    (A : Arena) {start : A.State}
    {current : A.HistoryFrom start}
    (play : A.CompletePlayFromHistory current)
    (bound : ℕ) :
    Set (A.CompletePlayFromHistory current) :=
  {other |
    CompletePlayFromHistory.AgreeThrough
      bound play other}

/-- The coordinate cylinder fixing exactly one complete history at one event
time. -/
def CompletePlayCylinderAtFrom
    (A : Arena) {start : A.State}
    {current : A.HistoryFrom start}
    (time : ℕ) (history : A.HistoryFrom start) :
    Set (A.CompletePlayFromHistory current) :=
  {play | play.historyAt time = history}

/-- The earlier visit-cylinder is the countable union of exact-coordinate
cylinders. -/
theorem completePlayCylinderFrom_eq_iUnion
    (current history : A.HistoryFrom start) :
    A.CompletePlayCylinderFrom current history =
      ⋃ time : ℕ,
        A.CompletePlayCylinderAtFrom
          (current := current) time history := by
  ext play
  simp [CompletePlayCylinderFrom,
    CompletePlayCylinderAtFrom]

namespace Set

/-- Membership in a complete-play event has a finite positive prefix witness.
-/
def IsPrefixOpenOn
    (event :
      Set (A.CompletePlayFromHistory current)) : Prop :=
  ∀ play, play ∈ event →
    ∃ bound,
      A.CompletePlayAgreementCylinderFrom play bound ⊆
        event

/-- A complete-play event is prefix closed when its complement is prefix
open. -/
def IsPrefixClosedOn
    (event :
      Set (A.CompletePlayFromHistory current)) : Prop :=
  Set.IsPrefixOpenOn eventᶜ

/-- Membership and nonmembership are both decided by some finite prefix,
chosen separately for each complete play. -/
def HasFinitePrefixDecisionOn
    (event :
      Set (A.CompletePlayFromHistory current)) : Prop :=
  ∀ play, ∃ bound,
    ∀ other,
      CompletePlayFromHistory.AgreeThrough
          bound play other →
        (other ∈ event ↔ play ∈ event)

/-- A finite-prefix decision witness gives prefix openness. -/
theorem HasFinitePrefixDecisionOn.isPrefixOpenOn
    {event :
      Set (A.CompletePlayFromHistory current)}
    (hdecision : Set.HasFinitePrefixDecisionOn event) :
    Set.IsPrefixOpenOn event := by
  intro play hplay
  rcases hdecision play with ⟨bound, hbound⟩
  refine ⟨bound, ?_⟩
  intro other hagree
  exact (hbound other hagree).2 hplay

/-- A finite-prefix decision witness also gives prefix closedness. -/
theorem HasFinitePrefixDecisionOn.isPrefixClosedOn
    {event :
      Set (A.CompletePlayFromHistory current)}
    (hdecision : Set.HasFinitePrefixDecisionOn event) :
    Set.IsPrefixClosedOn event := by
  apply
    HasFinitePrefixDecisionOn.isPrefixOpenOn
      (event := eventᶜ)
  intro play
  rcases hdecision play with ⟨bound, hbound⟩
  refine ⟨bound, ?_⟩
  intro other hagree
  simpa only [Set.mem_compl_iff] using
    not_congr (hbound other hagree)

end Set

namespace CompletePlayFromHistory

/-- Generating family of finite agreement cylinders. -/
def prefixCylinderGenerator
    (A : Arena) {start : A.State}
    (current : A.HistoryFrom start) :
    Set (Set (A.CompletePlayFromHistory current)) :=
  {event | ∃ play bound,
    event =
      A.CompletePlayAgreementCylinderFrom play bound}

/-- Topology generated by finite agreement cylinders. -/
@[implicit_reducible]
def prefixTopology
    (A : Arena) {start : A.State}
    (current : A.HistoryFrom start) :
    TopologicalSpace
      (A.CompletePlayFromHistory current) :=
  TopologicalSpace.generateFrom
    (prefixCylinderGenerator A current)

/-- Every finite agreement cylinder is open in the generated prefix
topology. -/
theorem isOpen_agreementCylinder
    (play : A.CompletePlayFromHistory current)
    (bound : ℕ) :
    @IsOpen
        (A.CompletePlayFromHistory current)
        (prefixTopology A current)
        (A.CompletePlayAgreementCylinderFrom
          play bound) := by
  apply TopologicalSpace.isOpen_generateFrom_of_mem
  exact ⟨play, bound, rfl⟩

/-- Operational finite-prefix openness is exactly openness in the generated
prefix topology. -/
theorem isPrefixOpenOn_iff_isOpen
    (event :
      Set (A.CompletePlayFromHistory current)) :
    Set.IsPrefixOpenOn event ↔
      @IsOpen
        (A.CompletePlayFromHistory current)
        (prefixTopology A current) event := by
  classical
  letI : TopologicalSpace
      (A.CompletePlayFromHistory current) :=
    prefixTopology A current
  constructor
  · intro hopen
    let bound :
        {play : A.CompletePlayFromHistory current //
          play ∈ event} → ℕ :=
      fun play => Classical.choose
        (hopen play.1 play.2)
    have hcylinder :
        ∀ play :
          {play : A.CompletePlayFromHistory current //
            play ∈ event},
          A.CompletePlayAgreementCylinderFrom
              play.1 (bound play) ⊆ event :=
      fun play =>
        Classical.choose_spec (hopen play.1 play.2)
    have hevent :
        event =
          ⋃ play :
            {play : A.CompletePlayFromHistory current //
              play ∈ event},
            A.CompletePlayAgreementCylinderFrom
              play.1 (bound play) := by
      ext play
      constructor
      · intro hplay
        apply Set.mem_iUnion.2
        refine ⟨⟨play, hplay⟩, ?_⟩
        exact
          CompletePlayFromHistory.AgreeThrough.refl
            (bound ⟨play, hplay⟩) play
      · intro hplay
        rcases Set.mem_iUnion.1 hplay with
          ⟨source, hsource⟩
        exact hcylinder source hsource
    rw [hevent]
    exact isOpen_iUnion fun play =>
      isOpen_agreementCylinder
        (A := A) play.1 (bound play)
  · intro hopen
    change
      TopologicalSpace.GenerateOpen
        (prefixCylinderGenerator A current) event
      at hopen
    induction hopen with
    | basic basic hbasic =>
        rcases hbasic with ⟨center, bound, rfl⟩
        intro play hplay
        refine ⟨bound, ?_⟩
        intro other hother
        exact hplay.trans hother
    | univ =>
        intro play _hplay
        exact ⟨0, Set.subset_univ _⟩
    | inter first second _ _ hfirst hsecond =>
        intro play hplay
        rcases hfirst play hplay.1 with
          ⟨firstBound, hfirstBound⟩
        rcases hsecond play hplay.2 with
          ⟨secondBound, hsecondBound⟩
        refine ⟨max firstBound secondBound, ?_⟩
        intro other hagree
        exact
          ⟨hfirstBound
              (hagree.mono (Nat.le_max_left _ _)),
            hsecondBound
              (hagree.mono (Nat.le_max_right _ _))⟩
    | sUnion family hopenFamily ih =>
        intro play hplay
        rcases Set.mem_sUnion.1 hplay with
          ⟨member, hmember, hplayMember⟩
        rcases ih member hmember play hplayMember with
          ⟨bound, hbound⟩
        exact
          ⟨bound,
            hbound.trans
              (Set.subset_sUnion_of_mem hmember)⟩

/-- Exact-coordinate cylinders are open in the prefix topology. -/
theorem isOpen_coordinateCylinder
    (time : ℕ) (history : A.HistoryFrom start) :
    @IsOpen
        (A.CompletePlayFromHistory current)
        (prefixTopology A current)
        (A.CompletePlayCylinderAtFrom
          (current := current) time history) := by
  letI : TopologicalSpace
      (A.CompletePlayFromHistory current) :=
    prefixTopology A current
  rw [← isPrefixOpenOn_iff_isOpen]
  intro play hplay
  refine ⟨time, ?_⟩
  intro other hagree
  change other.historyAt time = history
  exact (hagree time (Nat.le_refl time)).symm.trans hplay

/-- Visit cylinders are open, hence measurable, because they are countable
unions of exact-coordinate cylinders. -/
theorem isOpen_visitCylinder
    (history : A.HistoryFrom start) :
    @IsOpen
        (A.CompletePlayFromHistory current)
        (prefixTopology A current)
        (A.CompletePlayCylinderFrom current history) := by
  letI : TopologicalSpace
      (A.CompletePlayFromHistory current) :=
    prefixTopology A current
  rw [completePlayCylinderFrom_eq_iUnion]
  exact isOpen_iUnion fun time =>
    isOpen_coordinateCylinder
      (A := A) (current := current) time history

/-- Measurable space generated by finite agreement cylinders. -/
@[implicit_reducible]
def prefixMeasurableSpace
    (A : Arena) {start : A.State}
    (current : A.HistoryFrom start) :
    MeasurableSpace
      (A.CompletePlayFromHistory current) :=
  MeasurableSpace.generateFrom
    (prefixCylinderGenerator A current)

/-- Explicit measurability predicate for the generated discrete-path
sigma-algebra, without installing a global instance on bundled plays. -/
def IsPrefixMeasurable
    (event :
      Set (A.CompletePlayFromHistory current)) : Prop :=
  (prefixMeasurableSpace A current).MeasurableSet'
    event

/-- Every finite agreement cylinder is measurable in the generated
prefix sigma-algebra. -/
theorem isPrefixMeasurable_agreementCylinder
    (play : A.CompletePlayFromHistory current)
    (bound : ℕ) :
    IsPrefixMeasurable
      (A.CompletePlayAgreementCylinderFrom
        play bound) := by
  exact
    MeasurableSpace.measurableSet_generateFrom
      ⟨play, bound, rfl⟩

/-- A countable union of prefix-measurable events remains prefix measurable.
-/
theorem isPrefixMeasurable_iUnion
    (events :
      ℕ → Set (A.CompletePlayFromHistory current))
    (hmeasurable :
      ∀ n, IsPrefixMeasurable (events n)) :
    IsPrefixMeasurable (⋃ n, events n) :=
  (prefixMeasurableSpace A current).measurableSet_iUnion
    events hmeasurable

/-- The generated prefix measurable space is the Borel sigma-algebra of the
prefix topology whenever that topology is second countable. -/
theorem prefixMeasurableSpace_eq_borel
    (hsecond :
      @SecondCountableTopology
        (A.CompletePlayFromHistory current)
        (prefixTopology A current)) :
    prefixMeasurableSpace A current =
      @borel
        (A.CompletePlayFromHistory current)
        (prefixTopology A current) := by
  letI : TopologicalSpace
      (A.CompletePlayFromHistory current) :=
    prefixTopology A current
  letI : SecondCountableTopology
      (A.CompletePlayFromHistory current) :=
    hsecond
  exact
    (borel_eq_generateFrom_of_subbasis
      (s := prefixCylinderGenerator A current)
      rfl).symm

/-- Exact-coordinate cylinders are prefix measurable. -/
theorem isPrefixMeasurable_coordinateCylinder
    (hsecond :
      @SecondCountableTopology
        (A.CompletePlayFromHistory current)
        (prefixTopology A current))
    (time : ℕ) (history : A.HistoryFrom start) :
    IsPrefixMeasurable
      (A.CompletePlayCylinderAtFrom
        (current := current) time history) := by
  letI : TopologicalSpace
      (A.CompletePlayFromHistory current) :=
    prefixTopology A current
  letI : SecondCountableTopology
      (A.CompletePlayFromHistory current) :=
    hsecond
  letI : MeasurableSpace
      (A.CompletePlayFromHistory current) :=
    borel _
  letI : BorelSpace
      (A.CompletePlayFromHistory current) :=
    ⟨rfl⟩
  change
    (prefixMeasurableSpace A current).MeasurableSet'
      (A.CompletePlayCylinderAtFrom
        (current := current) time history)
  rw [prefixMeasurableSpace_eq_borel
    (A := A) (current := current) hsecond]
  exact
    (isOpen_coordinateCylinder
      (A := A) (current := current) time history).measurableSet

/-- Visit cylinders are prefix measurable. -/
theorem isPrefixMeasurable_visitCylinder
    (hsecond :
      @SecondCountableTopology
        (A.CompletePlayFromHistory current)
        (prefixTopology A current))
    (history : A.HistoryFrom start) :
    IsPrefixMeasurable
      (A.CompletePlayCylinderFrom current history) := by
  rw [completePlayCylinderFrom_eq_iUnion]
  exact isPrefixMeasurable_iUnion
    (fun time =>
      A.CompletePlayCylinderAtFrom
        (current := current) time history)
    (fun time =>
      isPrefixMeasurable_coordinateCylinder
        (A := A) (current := current)
        hsecond time history)

end CompletePlayFromHistory

namespace WinningConditionFrom

variable {N : Type*}

/-- Every player's winning event is prefix open. -/
def IsPrefixOpen
    (W : A.WinningConditionFrom current N) : Prop :=
  ∀ i, Set.IsPrefixOpenOn (W i)

/-- Every player's winning event is prefix closed. -/
def IsPrefixClosed
    (W : A.WinningConditionFrom current N) : Prop :=
  ∀ i, Set.IsPrefixClosedOn (W i)

/-- Every player's winning event has a finite membership-decision witness. -/
def HasFinitePrefixDecision
    (W : A.WinningConditionFrom current N) : Prop :=
  ∀ i, Set.HasFinitePrefixDecisionOn (W i)

/-- Every player's winning event is measurable in the generated prefix
sigma-algebra. -/
def IsPrefixMeasurable
    (W : A.WinningConditionFrom current N) : Prop :=
  ∀ i,
    CompletePlayFromHistory.IsPrefixMeasurable
      (W i)

/-- Under exclusivity, the existing winner-prefix certificate decides
membership in every player's winning event by a finite prefix. -/
theorem PrefixDecision.hasFinitePrefixDecision
    {W : A.WinningConditionFrom current N}
    (certificate : W.PrefixDecision)
    (hexclusive : W.IsExclusive) :
    W.HasFinitePrefixDecision := by
  intro i play
  rcases certificate.complete play with
    ⟨bound, winner, hwinner⟩
  have hplayWinner : play ∈ W winner :=
    certificate.sound winner (play.historyAt bound)
      hwinner ⟨bound, rfl⟩
  refine ⟨bound, ?_⟩
  intro other hagree
  have hotherHistory :
      other.historyAt bound =
        play.historyAt bound :=
    (hagree bound (Nat.le_refl bound)).symm
  have hotherWinner : other ∈ W winner :=
    certificate.sound winner (play.historyAt bound)
      hwinner ⟨bound, hotherHistory⟩
  constructor
  · intro hotherI
    have hsame : winner = i :=
      hexclusive other hotherWinner hotherI
    simpa [hsame] using hplayWinner
  · intro hplayI
    have hsame : winner = i :=
      hexclusive play hplayWinner hplayI
    simpa [hsame] using hotherWinner

/-- A sound exclusive prefix-decision certificate makes every winning event
prefix open. -/
theorem PrefixDecision.isPrefixOpen
    {W : A.WinningConditionFrom current N}
    (certificate : W.PrefixDecision)
    (hexclusive : W.IsExclusive) :
    W.IsPrefixOpen :=
  fun i =>
    Set.HasFinitePrefixDecisionOn.isPrefixOpenOn
      (certificate.hasFinitePrefixDecision
        hexclusive i)

/-- A sound exclusive prefix-decision certificate makes every winning event
prefix closed as well. -/
theorem PrefixDecision.isPrefixClosed
    {W : A.WinningConditionFrom current N}
    (certificate : W.PrefixDecision)
    (hexclusive : W.IsExclusive) :
    W.IsPrefixClosed :=
  fun i =>
    Set.HasFinitePrefixDecisionOn.isPrefixClosedOn
      (certificate.hasFinitePrefixDecision
        hexclusive i)

end WinningConditionFrom

end Arena
