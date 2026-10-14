/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Simulation.Continuation.Path
import EconCSLib.GameTheory.ExtensiveGame.Simulation.Equilibrium.Outcome

/-!
# Continuation.Observed — absolute-prefix and fresh-restart outcomes

This module gives observed measurable-kernel profiles a constructive
continuation interface that preserves the original event clock and every
recorded past action occurrence. A dependent base history is first encoded as
its canonical joint event prefix. Mathlib's Ionescu--Tulcea trajectory then
continues from that prefix at the history's absolute depth.

This is deliberately not a conditioning API. No theorem here identifies a
constructive continuation law at `root` with a regular conditional
distribution of a law started at the empty history. Such an identification
needs an explicit conditioning theorem and is especially delicate at
histories of zero probability.

The main definitions are:

* `KernelBehavioralProfile.continuationStatePathMeasure`, the absolute-clock,
  full-prefix continuation law;
* `BoundedPathUtility.IsNashOnPresentation`, constructive Nash
  optimality at every presentation-designated continuation root under that
  absolute-prefix semantics;
* `ProfileAssembly.EventuallyTerminatesUnderContinuationDeviationsAt`, the
  termination certificate for baseline and unilateral continuation laws;
* `KernelBehavioralProfile.freshRestartStatePathMeasure`, the law obtained by
  starting the executor at a supplied complete history with event time reset
  to zero;
* `BoundedPathUtility.IsNashOnFreshRestarts`, constructive Nash optimality at
  every root selected by a predicate under that semantics;
* `BoundedPathUtility.IsNashOnDesignatedFreshRestarts`, the corresponding
  all-designated-root predicate;
* `ProfileAssembly.EventuallyTerminatesUnderFreshRestartDeviationsAt`, the
  termination certificate needed to compare eventual terminal payoffs under
  every constructive unilateral fresh-clock deviation;
* `BoundedTerminalPayoffExtension.IsNashAtFreshRestart` and
  `.IsNashOnDesignatedFreshRestarts`, the corresponding almost-sure
  terminal-payoff solution concepts.

The fresh-restart qualifier matters. Presentations may use time-dependent
information spaces, abstract actions, realizations, and kernels. Restarting
at a history of depth `d` invokes their time-zero components, whereas
`continuationStatePathMeasure` invokes the time-`d` component on the complete
canonical prefix. Consequently the fresh-restart predicates are not
identified with the unqualified continuation predicates without a separate
clock/prefix compatibility theorem.

The joint measurable `PlayerKernelProfile` remains intact. It is not replaced
by an arbitrary product of player strategies, since such a product need not
define one jointly measurable player kernel on an uncountable player carrier.
-/

open MeasureTheory ProbabilityTheory

namespace ExtensiveGame.ObservedGame

universe uN

variable {N : Type uN}
variable {G : ObservedGame N ℝ}

namespace MeasurableHistoryModel

variable (model : MeasurableHistoryModel G)

/-- Joint state/action event prefix canonically encoded by one dependent base
history.

Coordinate zero is the empty complete history with no incoming action. Every
successor coordinate stores the extended complete history and the concrete
action bundle selected at the preceding complete history. -/
def canonicalEventPrefixOfHistory
    {state : G.base.State}
    (history :
      G.base.toArena.History G.base.init state) :
    model.toArena.ContinuationPrefix history.length :=
  match history with
  | .nil =>
      fun _ =>
        model.toArena.initialEvent
          (Arena.HistoryFrom.nil
            G.base.toArena G.base.init)
  | @Arena.History.snoc _ _ previous path action =>
      fun index =>
        if hindex : index.1 ≤ path.length then
          canonicalEventPrefixOfHistory path
            ⟨index.1, Finset.mem_Iic.mpr hindex⟩
        else
          (⟨G.base.next previous action,
              path.snoc action⟩,
            .inr
              (⟨⟨previous, path⟩, action⟩ :
                model.toArena.ActionBundle))

/-- Absolute event time of the canonical continuation prefix represented by a
complete history. -/
def canonicalContinuationStart
    (root : CompleteHistory G) :
    ℕ :=
  root.2.length

/-- Canonical absolute-time action-occurrence prefix represented by a complete
history. -/
def canonicalContinuationPrefix
    (root : CompleteHistory G) :
    model.toArena.ContinuationPrefix
      (canonicalContinuationStart root) :=
  canonicalEventPrefixOfHistory
    (model := model) root.2

/-- The empty complete history has absolute continuation time zero. -/
@[simp]
theorem canonicalContinuationStart_init :
    canonicalContinuationStart
        (Arena.HistoryFrom.nil
          G.base.toArena G.base.init) =
      0 :=
  rfl

/-- The canonical prefix of the empty complete history is the singleton
initial event. -/
@[simp]
theorem canonicalContinuationPrefix_init :
    model.canonicalContinuationPrefix
        (Arena.HistoryFrom.nil
          G.base.toArena G.base.init) =
      (fun _ : Finset.Iic 0 =>
        model.toArena.initialEvent
          (Arena.HistoryFrom.nil
            G.base.toArena G.base.init)) :=
  rfl

/-- Extending a history preserves every earlier event coordinate of its
canonical prefix. -/
theorem canonicalEventPrefixOfHistory_snoc_of_le
    {previous : G.base.State}
    (path :
      G.base.toArena.History G.base.init previous)
    (action : G.base.Action previous)
    (index : Finset.Iic path.length) :
    model.canonicalEventPrefixOfHistory
        (path.snoc action)
        ⟨index.1,
          Finset.mem_Iic.mpr
            ((Finset.mem_Iic.mp index.2).trans
              (Nat.le_succ path.length))⟩ =
      model.canonicalEventPrefixOfHistory path index := by
  simp only [canonicalEventPrefixOfHistory]
  simp only [dif_pos (Finset.mem_Iic.mp index.2)]

/-- The newest event of a nonempty canonical prefix records exactly the
incoming action occurrence and the history it extends. -/
@[simp]
theorem latestEvent_canonicalEventPrefixOfHistory_snoc
    {previous : G.base.State}
    (path :
      G.base.toArena.History G.base.init previous)
    (action : G.base.Action previous) :
    MeasurableKernelArena.latestEvent
        (path.snoc action).length
        (model.canonicalEventPrefixOfHistory
          (path.snoc action)) =
      (⟨G.base.next previous action,
          path.snoc action⟩,
        .inr
          (⟨⟨previous, path⟩, action⟩ :
            model.toArena.ActionBundle)) := by
  simp only [
    MeasurableKernelArena.latestEvent,
    canonicalEventPrefixOfHistory]
  have hnot :
      ¬ (path.snoc action).length ≤ path.length := by
    simp
  rw [dif_neg hnot]

/-- The canonical prefix's latest event state is exactly the complete history
used to build it. -/
@[simp]
theorem latestEventState_canonicalEventPrefixOfHistory
    {state : G.base.State}
    (history :
      G.base.toArena.History G.base.init state) :
    MeasurableKernelArena.latestEventState
        history.length
        (model.canonicalEventPrefixOfHistory history) =
      (⟨state, history⟩ : CompleteHistory G) := by
  induction history with
  | nil =>
      rfl
  | @snoc previous path action ih =>
      simp only [
        canonicalEventPrefixOfHistory,
        MeasurableKernelArena.latestEventState,
        MeasurableKernelArena.latestEvent]
      have hnot :
          ¬ (path.snoc action).length ≤ path.length := by
        simp
      rw [dif_neg hnot]
      rfl

/-- The canonical complete-history continuation prefix ends at the supplied
root. -/
@[simp]
theorem latestEventState_canonicalContinuationPrefix
    (root : CompleteHistory G) :
    MeasurableKernelArena.latestEventState
        (canonicalContinuationStart root)
        (model.canonicalContinuationPrefix root) =
      root := by
  rcases root with ⟨state, history⟩
  exact
    model.latestEventState_canonicalEventPrefixOfHistory
      history

end MeasurableHistoryModel

namespace MeasurableKernelPresentation
namespace KernelBehavioralProfile

variable
  {model : MeasurableHistoryModel G}
  {presentation : G.MeasurableKernelPresentation model}

/-- Absolute-prefix continuation event-path law of an observed profile.

Unlike fresh restart, this law starts Mathlib's trajectory at the complete
canonical event prefix of `root`, so future kernels retain both the original
event clock and every recorded past action occurrence. -/
noncomputable def continuationEventPathMeasure
    (profile : presentation.KernelBehavioralProfile)
    (root : CompleteHistory G) :
    Measure (ℕ → model.toArena.PathEvent) :=
  profile.compiledPolicy.tailEventPathMeasureFromPrefix
    model.toArena_terminalSet_measurable
    (MeasurableHistoryModel.canonicalContinuationStart root)
    (model.canonicalContinuationPrefix root)

/-- Absolute-prefix continuation state-path law, tail-indexed from the
continuation root. -/
noncomputable def continuationStatePathMeasure
    (profile : presentation.KernelBehavioralProfile)
    (root : CompleteHistory G) :
    Measure (ℕ → model.toArena.State) :=
  profile.compiledPolicy.tailStatePathMeasureFromPrefix
    model.toArena_terminalSet_measurable
    (MeasurableHistoryModel.canonicalContinuationStart root)
    (model.canonicalContinuationPrefix root)

/-- Every absolute-prefix continuation state law is a probability measure. -/
instance continuationStatePathMeasure_isProbability
    (profile : presentation.KernelBehavioralProfile)
    (root : CompleteHistory G) :
    IsProbabilityMeasure
      (profile.continuationStatePathMeasure root) := by
  unfold continuationStatePathMeasure
  infer_instance

/-- Coordinate zero of the absolute-prefix continuation state path is exactly
the supplied complete-history root. -/
@[simp]
theorem continuationStatePathMeasure_coordinate_zero
    (profile : presentation.KernelBehavioralProfile)
    (root : CompleteHistory G) :
    @Measure.map
        (ℕ → model.toArena.State) model.toArena.State
        inferInstance model.toArena.stateMeasurable
        (fun path => path 0)
        (profile.continuationStatePathMeasure root) =
      @Measure.dirac
        model.toArena.State model.toArena.stateMeasurable root := by
  unfold continuationStatePathMeasure
  rw [
    MeasurableKernelArena.EventHistoryActionPolicy.tailStatePathMeasureFromPrefix_coordinate_zero,
    model.latestEventState_canonicalContinuationPrefix]

/-- At a nonterminal continuation root, future state coordinate one is the
history transition integrated against the profile's absolute-time action law
on the complete canonical prefix. -/
theorem continuationStatePathMeasure_coordinate_one_of_nonterminal
    (profile : presentation.KernelBehavioralProfile)
    (root : CompleteHistory G)
    (hnonterminal :
      ¬ G.base.isTerminal root.1) :
    @Measure.map
        (ℕ → model.toArena.State) model.toArena.State
        inferInstance model.toArena.stateMeasurable
        (fun path => path 1)
        (profile.continuationStatePathMeasure root) =
      model.toArena.transition ∘ₘ
        profile.compiledPolicy.kernel
          (MeasurableHistoryModel.canonicalContinuationStart root)
          (model.canonicalContinuationPrefix root) := by
  unfold continuationStatePathMeasure
  apply
    profile.compiledPolicy.tailStatePathMeasureFromPrefix_coordinate_one_of_nonterminal
      model.toArena_terminalSet_measurable
      (MeasurableHistoryModel.canonicalContinuationStart root)
      (model.canonicalContinuationPrefix root)
  simpa only [
    model.latestEventState_canonicalContinuationPrefix] using
      hnonterminal

/-- At the empty initial history, absolute-prefix continuation is exactly the
existing time-zero state-path law. -/
theorem continuationStatePathMeasure_init
    (profile : presentation.KernelBehavioralProfile) :
    profile.continuationStatePathMeasure
        (Arena.HistoryFrom.nil G.base.toArena G.base.init) =
      profile.statePathMeasure
        (Arena.HistoryFrom.nil G.base.toArena G.base.init) := by
  unfold
    continuationStatePathMeasure
    MeasurableKernelArena.EventHistoryActionPolicy.tailStatePathMeasureFromPrefix
    MeasurableKernelArena.EventHistoryActionPolicy.tailEventPathMeasureFromPrefix
    MeasurableKernelArena.EventHistoryActionPolicy.absolutePathMeasureFromPrefix
    statePathMeasure
    MeasurableKernelArena.EventHistoryActionPolicy.statePathMeasure
    MeasurableKernelArena.EventHistoryActionPolicy.pathMeasure
  simp only [
    MeasurableHistoryModel.canonicalContinuationStart_init,
    MeasurableHistoryModel.canonicalContinuationPrefix_init]
  have hshift :
      MeasurableKernelArena.EventHistoryActionPolicy.tailEventPath
          (A := model.toArena) 0 =
        id := by
    funext path offset
    simp [
      MeasurableKernelArena.EventHistoryActionPolicy.tailEventPath]
  rw [hshift, Measure.map_id]
  rfl

/-- Almost-sure terminal absorption under the canonical absolute-prefix
continuation law from `root`. -/
def TerminatesInContinuationAlmostSurely
    (profile : presentation.KernelBehavioralProfile)
    (root : CompleteHistory G) :
    Prop :=
  ∀ᵐ path ∂profile.continuationStatePathMeasure root,
    EventuallyAbsorbsAtTerminal
      (G := G) (model := model) path

/-- Complete state-path law obtained by constructively restarting the
executor at `root`.

This is definitionally the existing root-parameterized path law. The separate
name records its continuation interpretation without asserting any
conditional-probability identity. -/
noncomputable def freshRestartStatePathMeasure
    (profile : presentation.KernelBehavioralProfile)
    (root : CompleteHistory G) :
    Measure (ℕ → model.toArena.State) :=
  profile.statePathMeasure root

/-- The time-zero state marginal of a restart law is the supplied root. -/
@[simp]
theorem freshRestartStateCoordinateMeasure_zero
    (profile : presentation.KernelBehavioralProfile)
    (root : CompleteHistory G) :
    @Measure.map
        (ℕ → model.toArena.State) model.toArena.State
        inferInstance model.toArena.stateMeasurable
        (fun path => path 0)
        (profile.freshRestartStatePathMeasure root) =
      @Measure.dirac
        model.toArena.State model.toArena.stateMeasurable root := by
  unfold freshRestartStatePathMeasure
  change
    profile.compiledPolicy.stateCoordinateMeasure
        model.toArena_terminalSet_measurable root 0 =
      @Measure.dirac
        model.toArena.State model.toArena.stateMeasurable root
  rw [
    MeasurableKernelArena.EventHistoryActionPolicy.stateCoordinateMeasure_eq_coordinateMeasure_map_state,
    MeasurableKernelArena.EventHistoryActionPolicy.coordinateMeasure_zero,
    Measure.map_dirac'
      MeasurableKernelArena.PathEvent.measurable_state]
  rfl

end KernelBehavioralProfile
end MeasurableKernelPresentation

namespace MeasurableHistoryModel
namespace BoundedPathUtility

variable
  {model : MeasurableHistoryModel G}
  (evaluation : MeasurableHistoryModel.BoundedPathUtility model)

/-- Expected bounded path utility under the absolute-prefix continuation law.
-/
noncomputable def continuationExpectedUtility
    {presentation : G.MeasurableKernelPresentation model}
    (profile : presentation.KernelBehavioralProfile)
    (root : CompleteHistory G)
    (i : N) :
    ℝ :=
  ∫ path, evaluation.utility i path
    ∂profile.continuationStatePathMeasure root

/-- Bounded path utility is integrable under every absolute-prefix
continuation law. -/
theorem continuationUtility_integrable
    {presentation : G.MeasurableKernelPresentation model}
    (profile : presentation.KernelBehavioralProfile)
    (root : CompleteHistory G)
    (i : N) :
    Integrable
      (evaluation.utility i)
      (profile.continuationStatePathMeasure root) := by
  apply
    (integrable_const (evaluation.bound : ℝ)).mono
      (evaluation.utility_measurable i).aestronglyMeasurable
  exact
    Filter.Eventually.of_forall fun path => by
      simpa using evaluation.norm_utility_le i path

/-- Absolute-prefix continuation expected utility never exceeds the uniform
bound. -/
theorem continuationExpectedUtility_le_bound
    {presentation : G.MeasurableKernelPresentation model}
    (profile : presentation.KernelBehavioralProfile)
    (root : CompleteHistory G)
    (i : N) :
    evaluation.continuationExpectedUtility profile root i ≤
      (evaluation.bound : ℝ) := by
  unfold continuationExpectedUtility
  calc
    (∫ path, evaluation.utility i path
        ∂profile.continuationStatePathMeasure root) ≤
        ∫ _path, (evaluation.bound : ℝ)
          ∂profile.continuationStatePathMeasure root := by
      apply integral_mono_ae
      · exact
          evaluation.continuationUtility_integrable
            profile root i
      · exact integrable_const _
      · exact
          Filter.Eventually.of_forall fun path =>
            (Real.le_norm_self
              (evaluation.utility i path)).trans
                (evaluation.norm_utility_le i path)
    _ = (evaluation.bound : ℝ) := by simp

/-- Constructive Nash optimality under the absolute-prefix continuation from
one complete history. -/
def IsNashAtContinuation
    {presentation : G.MeasurableKernelPresentation model}
    (assembly : presentation.ProfileAssembly)
    (root : CompleteHistory G)
    (profile : assembly.PlayerKernelProfile) :
    Prop :=
  ∀ (who : N)
    (strategy : assembly.PlayerStrategy who),
    evaluation.continuationExpectedUtility
        (assembly.toKernelBehavioralProfile
          (MeasurableKernelPresentation.ProfileAssembly.PlayerKernelProfile.deviate
            (assembly := assembly)
            profile who strategy))
        root who ≤
      evaluation.continuationExpectedUtility
        (assembly.toKernelBehavioralProfile profile)
        root who

/-- A profile attaining the uniform utility bound for every player at one
continuation root is Nash there against every admitted measurable unilateral
deviation. -/
theorem isNashAtContinuation_of_expectedUtility_eq_bound
    {presentation : G.MeasurableKernelPresentation model}
    (assembly : presentation.ProfileAssembly)
    (root : CompleteHistory G)
    (profile : assembly.PlayerKernelProfile)
    (hoptimal :
      ∀ who,
        evaluation.continuationExpectedUtility
            (assembly.toKernelBehavioralProfile profile)
            root who =
          (evaluation.bound : ℝ)) :
    evaluation.IsNashAtContinuation
      assembly root profile := by
  intro who strategy
  calc
    evaluation.continuationExpectedUtility
        (assembly.toKernelBehavioralProfile
          (MeasurableKernelPresentation.ProfileAssembly.PlayerKernelProfile.deviate
            (assembly := assembly)
            profile who strategy))
        root who ≤
      (evaluation.bound : ℝ) :=
        evaluation.continuationExpectedUtility_le_bound
          _ root who
    _ =
      evaluation.continuationExpectedUtility
        (assembly.toKernelBehavioralProfile profile)
        root who :=
          (hoptimal who).symm

/-- Constructive Nash optimality under absolute-prefix continuation at every
root selected by `roots`. -/
def IsNashOnContinuations
    {presentation : G.MeasurableKernelPresentation model}
    (assembly : presentation.ProfileAssembly)
    (roots : CompleteHistory G → Prop)
    (profile : assembly.PlayerKernelProfile) :
    Prop :=
  ∀ root, roots root →
    evaluation.IsNashAtContinuation
      assembly root profile

/-- Testing a larger root predicate implies absolute-prefix continuation Nash
optimality on every smaller root predicate. -/
theorem IsNashOnContinuations.mono
    {presentation : G.MeasurableKernelPresentation model}
    {assembly : presentation.ProfileAssembly}
    {sourceRoots targetRoots : CompleteHistory G → Prop}
    {profile : assembly.PlayerKernelProfile}
    (hnash :
      evaluation.IsNashOnContinuations
        assembly sourceRoots profile)
    (hroots :
      ∀ root, targetRoots root → sourceRoots root) :
    evaluation.IsNashOnContinuations
      assembly targetRoots profile := by
  intro root hroot
  exact hnash root (hroots root hroot)

/-- Measurable-kernel Nash optimality on an explicit root presentation under
canonical absolute-prefix continuation semantics. -/
def IsNashOnPresentation
    {presentation : G.MeasurableKernelPresentation model}
    (assembly : presentation.ProfileAssembly)
    (roots : G.RootPresentation)
    (profile : assembly.PlayerKernelProfile) :
    Prop :=
  evaluation.IsNashOnContinuations
    assembly roots.IsRoot profile

/-- Measurable-kernel subgame perfection under absolute-prefix continuation
semantics on an explicit, possibly conservative, lawful subgame system. -/
def IsSubgamePerfectOn
    {presentation : G.MeasurableKernelPresentation model}
    (assembly : presentation.ProfileAssembly)
    (system : G.SubgameSystem)
    (profile : assembly.PlayerKernelProfile) :
    Prop :=
  evaluation.IsNashOnContinuations
    assembly system.IsRoot profile

/-- Standard measurable-kernel SPE under absolute-prefix continuation
semantics on every structurally lawful subgame root. -/
def IsStandardSubgamePerfect
    {presentation : G.MeasurableKernelPresentation model}
    (assembly : presentation.ProfileAssembly)
    (system : G.CompleteSubgameSystem)
    (profile : assembly.PlayerKernelProfile) :
    Prop :=
  evaluation.IsSubgamePerfectOn
    assembly system.toSubgameSystem profile

/-- Absolute-prefix designated-root Nash is exactly constructive continuation
Nash optimality at every presentation-designated root. -/
theorem isNashOnPresentation_iff
    {presentation : G.MeasurableKernelPresentation model}
    (assembly : presentation.ProfileAssembly)
    (roots : G.RootPresentation)
    (profile : assembly.PlayerKernelProfile) :
    evaluation.IsNashOnPresentation assembly roots profile ↔
      ∀ root, roots.IsRoot root →
        evaluation.IsNashAtContinuation
          assembly root profile :=
  Iff.rfl

/-- Absolute-prefix Nash on all presentation-designated continuations implies
continuation Nash optimality at the initial empty history. -/
theorem IsNashOnPresentation.isNashAtContinuation_init
    {presentation : G.MeasurableKernelPresentation model}
    {assembly : presentation.ProfileAssembly}
    {roots : G.RootPresentation}
    {profile : assembly.PlayerKernelProfile}
    (hspe : evaluation.IsNashOnPresentation assembly roots profile) :
    evaluation.IsNashAtContinuation assembly
      (Arena.HistoryFrom.nil G.base.toArena G.base.init)
      profile :=
  hspe _ roots.init_isRoot

/-- At the empty root, absolute-prefix continuation expected utility is the
existing time-zero expected utility. -/
theorem continuationExpectedUtility_init
    {presentation : G.MeasurableKernelPresentation model}
    (profile : presentation.KernelBehavioralProfile)
    (i : N) :
    evaluation.continuationExpectedUtility profile
        (Arena.HistoryFrom.nil G.base.toArena G.base.init) i =
      evaluation.expectedUtility profile
        (Arena.HistoryFrom.nil G.base.toArena G.base.init) i := by
  unfold
    continuationExpectedUtility expectedUtility
    PathUtility.expectedUtility
  rw [profile.continuationStatePathMeasure_init]

/-- Expected bounded utility never exceeds the advertised uniform bound. -/
theorem expectedUtility_le_bound
    {presentation : G.MeasurableKernelPresentation model}
    (profile : presentation.KernelBehavioralProfile)
    (root : CompleteHistory G)
    (i : N) :
    evaluation.expectedUtility profile root i ≤
      (evaluation.bound : ℝ) := by
  unfold expectedUtility PathUtility.expectedUtility
  letI :
      IsProbabilityMeasure
        (profile.statePathMeasure root) := by
    infer_instance
  calc
    (∫ path, evaluation.utility i path
        ∂profile.statePathMeasure root) ≤
        ∫ _path, (evaluation.bound : ℝ)
          ∂profile.statePathMeasure root := by
      apply integral_mono_ae
      · exact evaluation.integrableAt profile root i
      · exact integrable_const _
      · exact Filter.Eventually.of_forall fun path =>
          (Real.le_norm_self (evaluation.utility i path)).trans
            (evaluation.norm_utility_le i path)
    _ = (evaluation.bound : ℝ) := by simp

/-- Constructive Nash optimality at every restart root selected by `roots`. -/
def IsNashOnFreshRestarts
    {presentation : G.MeasurableKernelPresentation model}
    (assembly : presentation.ProfileAssembly)
    (roots : CompleteHistory G → Prop)
    (profile : assembly.PlayerKernelProfile) :
    Prop :=
  ∀ root, roots root →
    evaluation.IsNashAt assembly root profile

/-- Restricting the tested root predicate preserves continuation-wise Nash
optimality. -/
theorem IsNashOnFreshRestarts.mono
    {presentation : G.MeasurableKernelPresentation model}
    {assembly : presentation.ProfileAssembly}
    {sourceRoots targetRoots : CompleteHistory G → Prop}
    {profile : assembly.PlayerKernelProfile}
    (hnash :
      evaluation.IsNashOnFreshRestarts assembly sourceRoots profile)
    (hroots : ∀ root, targetRoots root → sourceRoots root) :
    evaluation.IsNashOnFreshRestarts
      assembly targetRoots profile := by
  intro root hroot
  exact hnash root (hroots root hroot)

/-- Measurable-kernel optimality on an explicit root presentation under
constructive fresh-clock restart semantics.

One jointly measurable complete profile must be Nash after restarting at
every designated root exposed by the observed game. Deviations use the
existing measurable single-player replacement kernels. -/
def IsNashOnFreshRestartPresentation
    {presentation : G.MeasurableKernelPresentation model}
    (assembly : presentation.ProfileAssembly)
    (roots : G.RootPresentation)
    (profile : assembly.PlayerKernelProfile) :
    Prop :=
  evaluation.IsNashOnFreshRestarts
    assembly roots.IsRoot profile

/-- Measurable-kernel subgame perfection under fresh-clock restart semantics
on an explicit, possibly conservative, lawful subgame system. -/
def IsFreshRestartSubgamePerfectOn
    {presentation : G.MeasurableKernelPresentation model}
    (assembly : presentation.ProfileAssembly)
    (system : G.SubgameSystem)
    (profile : assembly.PlayerKernelProfile) :
    Prop :=
  evaluation.IsNashOnFreshRestarts
    assembly system.IsRoot profile

/-- Standard measurable-kernel SPE under fresh-clock restart semantics on
every structurally lawful subgame root. -/
def IsFreshRestartStandardSubgamePerfect
    {presentation : G.MeasurableKernelPresentation model}
    (assembly : presentation.ProfileAssembly)
    (system : G.CompleteSubgameSystem)
    (profile : assembly.PlayerKernelProfile) :
    Prop :=
  evaluation.IsFreshRestartSubgamePerfectOn
    assembly system.toSubgameSystem profile

/-- Fresh-restart designated-root Nash is exactly rootwise constructive Nash
optimality at the observed game's designated roots. -/
theorem isNashOnFreshRestartPresentation_iff
    {presentation : G.MeasurableKernelPresentation model}
    (assembly : presentation.ProfileAssembly)
    (roots : G.RootPresentation)
    (profile : assembly.PlayerKernelProfile) :
    evaluation.IsNashOnFreshRestartPresentation assembly roots profile ↔
      ∀ root, roots.IsRoot root →
        evaluation.IsNashAt assembly root profile :=
  Iff.rfl

/-- Fresh-restart Nash on all presentation-designated roots implies Nash
optimality at the initial empty history. -/
theorem IsNashOnFreshRestartPresentation.isNashAt_init
    {presentation : G.MeasurableKernelPresentation model}
    {assembly : presentation.ProfileAssembly}
    {roots : G.RootPresentation}
    {profile : assembly.PlayerKernelProfile}
    (hspe :
      evaluation.IsNashOnFreshRestartPresentation assembly roots profile) :
    evaluation.IsNashAt assembly
      (Arena.HistoryFrom.nil G.base.toArena G.base.init)
      profile :=
  hspe _ roots.init_isRoot

end BoundedPathUtility
end MeasurableHistoryModel

namespace MeasurableKernelPresentation
namespace ProfileAssembly

variable
  {model : MeasurableHistoryModel G}
  {presentation : G.MeasurableKernelPresentation model}
  (assembly : presentation.ProfileAssembly)

/-- Almost-sure terminal absorption of a profile and every constructive
unilateral deviation under the canonical absolute-prefix continuation from
one root. -/
structure EventuallyTerminatesUnderContinuationDeviationsAt
    (profile : assembly.PlayerKernelProfile)
    (root : CompleteHistory G) : Prop where
  /-- The baseline continuation eventually absorbs at a terminal history. -/
  profile_terminates :
    MeasurableKernelPresentation.KernelBehavioralProfile.TerminatesInContinuationAlmostSurely
        (assembly.toKernelBehavioralProfile profile) root
  /-- Every admitted unilateral continuation deviation eventually absorbs at
  a terminal history. -/
  deviation_terminates :
    ∀ (who : N) (strategy : assembly.PlayerStrategy who),
      MeasurableKernelPresentation.KernelBehavioralProfile.TerminatesInContinuationAlmostSurely
          (assembly.toKernelBehavioralProfile
            (PlayerKernelProfile.deviate
              (assembly := assembly)
              profile who strategy))
          root

/-- Almost-sure terminal absorption of a profile and every constructive
unilateral deviation after restarting at one root.

The deviating termination field is essential: an expected terminal-payoff
comparison is not silently assigned to a deviation that can fail to
terminate. -/
structure EventuallyTerminatesUnderFreshRestartDeviationsAt
    (profile : assembly.PlayerKernelProfile)
    (root : CompleteHistory G) : Prop where
  /-- The baseline profile eventually absorbs at a terminal history. -/
  profile_terminates :
    MeasurableKernelPresentation.KernelBehavioralProfile.TerminatesAlmostSurely
      (assembly.toKernelBehavioralProfile profile) root
  /-- Every admitted unilateral deviation eventually absorbs at a terminal
  history. -/
  deviation_terminates :
    ∀ (who : N) (strategy : assembly.PlayerStrategy who),
      MeasurableKernelPresentation.KernelBehavioralProfile.TerminatesAlmostSurely
        (assembly.toKernelBehavioralProfile
          (PlayerKernelProfile.deviate
            (assembly := assembly)
            profile who strategy))
        root

end ProfileAssembly
end MeasurableKernelPresentation

namespace MeasurableHistoryModel
namespace BoundedTerminalPayoffExtension

variable
  {model : MeasurableHistoryModel G}
  (terminalPayoff :
    MeasurableHistoryModel.BoundedTerminalPayoffExtension G model)

/-- Under absolute-prefix almost-sure terminal absorption, stopped utility
converges almost everywhere to eventual terminal utility. -/
theorem stoppedUtility_tendsto_eventualUtility_ae_continuation
    [(state : G.base.State) → Decidable (G.base.isTerminal state)]
    {presentation : G.MeasurableKernelPresentation model}
    (profile : presentation.KernelBehavioralProfile)
    (root : CompleteHistory G)
    (hterminates :
      profile.TerminatesInContinuationAlmostSurely root)
    (i : N) :
    ∀ᵐ path ∂profile.continuationStatePathMeasure root,
      Filter.Tendsto
        (fun horizon =>
          terminalPayoff.toTerminalPayoffExtension.stoppedUtility
            horizon i path)
        Filter.atTop
        (nhds (terminalPayoff.eventualUtility i path)) := by
  filter_upwards [hterminates] with path habsorbs
  exact
    terminalPayoff.stoppedUtility_tendsto_eventualUtility
      i path habsorbs

/-- Eventual terminal utility is almost-everywhere strongly measurable under
an absolute-prefix continuation termination certificate. -/
theorem eventualUtility_aestronglyMeasurable_continuation
    {presentation : G.MeasurableKernelPresentation model}
    (profile : presentation.KernelBehavioralProfile)
    (root : CompleteHistory G)
    (hterminates :
      profile.TerminatesInContinuationAlmostSurely root)
    (i : N) :
    AEStronglyMeasurable
      (terminalPayoff.eventualUtility i)
      (profile.continuationStatePathMeasure root) := by
  classical
  exact
    aestronglyMeasurable_of_tendsto_ae
      Filter.atTop
      (fun horizon =>
        (terminalPayoff.toTerminalPayoffExtension.stoppedUtility_measurable
          horizon i).aestronglyMeasurable)
      (terminalPayoff.stoppedUtility_tendsto_eventualUtility_ae_continuation
        profile root hterminates i)

/-- Bounded eventual terminal utility is integrable under an
almost-surely-terminating absolute-prefix continuation law. -/
theorem eventualUtility_integrable_continuation
    {presentation : G.MeasurableKernelPresentation model}
    (profile : presentation.KernelBehavioralProfile)
    (root : CompleteHistory G)
    (hterminates :
      profile.TerminatesInContinuationAlmostSurely root)
    (i : N) :
    Integrable
      (terminalPayoff.eventualUtility i)
      (profile.continuationStatePathMeasure root) := by
  apply
    (integrable_const (terminalPayoff.bound : ℝ)).mono
      (terminalPayoff.eventualUtility_aestronglyMeasurable_continuation
        profile root hterminates i)
  exact Filter.Eventually.of_forall fun path => by
    simpa using terminalPayoff.norm_eventualUtility_le i path

/-- Expected eventual terminal utility under an absolute-prefix continuation
termination certificate. -/
noncomputable def continuationExpectedEventualUtility
    {presentation : G.MeasurableKernelPresentation model}
    (profile : presentation.KernelBehavioralProfile)
    (root : CompleteHistory G)
    (_hterminates :
      profile.TerminatesInContinuationAlmostSurely root)
    (i : N) :
    ℝ :=
  ∫ path, terminalPayoff.eventualUtility i path
    ∂profile.continuationStatePathMeasure root

/-- Expected absolute-prefix stopped utility converges to expected eventual
terminal utility under almost-sure continuation absorption. -/
theorem continuationExpectedUtility_tendsto_expectedEventualUtility
    [(state : G.base.State) → Decidable (G.base.isTerminal state)]
    {presentation : G.MeasurableKernelPresentation model}
    (profile : presentation.KernelBehavioralProfile)
    (root : CompleteHistory G)
    (hterminates :
      profile.TerminatesInContinuationAlmostSurely root)
    (i : N) :
    Filter.Tendsto
      (fun horizon =>
        (terminalPayoff.stoppedBoundedPathUtility horizon).continuationExpectedUtility
          profile root i)
      Filter.atTop
      (nhds
        (terminalPayoff.continuationExpectedEventualUtility
          profile root hterminates i)) := by
  unfold
    MeasurableHistoryModel.BoundedPathUtility.continuationExpectedUtility
    continuationExpectedEventualUtility
  apply
    tendsto_integral_of_dominated_convergence
      (fun _ => (terminalPayoff.bound : ℝ))
  · intro horizon
    exact
      (terminalPayoff.toTerminalPayoffExtension.stoppedUtility_measurable
        horizon i).aestronglyMeasurable
  · exact integrable_const _
  · intro horizon
    exact Filter.Eventually.of_forall fun path => by
      simpa using
        (terminalPayoff.stoppedBoundedPathUtility horizon).norm_utility_le
          i path
  · exact
      terminalPayoff.stoppedUtility_tendsto_eventualUtility_ae_continuation
        profile root hterminates i

/-- Constructive continuation Nash optimality for expected eventual terminal
payoff. -/
def IsNashAtContinuation
    {presentation : G.MeasurableKernelPresentation model}
    (assembly : presentation.ProfileAssembly)
    (root : CompleteHistory G)
    (profile : assembly.PlayerKernelProfile)
    (hterminates :
      assembly.EventuallyTerminatesUnderContinuationDeviationsAt
        profile root) :
    Prop :=
  ∀ (who : N) (strategy : assembly.PlayerStrategy who),
    terminalPayoff.continuationExpectedEventualUtility
        (assembly.toKernelBehavioralProfile
          (MeasurableKernelPresentation.ProfileAssembly.PlayerKernelProfile.deviate
            (assembly := assembly)
            profile who strategy))
        root
        (hterminates.deviation_terminates who strategy)
        who ≤
      terminalPayoff.continuationExpectedEventualUtility
        (assembly.toKernelBehavioralProfile profile)
        root hterminates.profile_terminates who

/-- Absolute-prefix terminal-payoff continuation Nash is independent of the
proof objects used to certify almost-sure termination. -/
theorem isNashAtContinuation_proof_irrel
    {presentation : G.MeasurableKernelPresentation model}
    (assembly : presentation.ProfileAssembly)
    (root : CompleteHistory G)
    (profile : assembly.PlayerKernelProfile)
    (hfirst hsecond :
      assembly.EventuallyTerminatesUnderContinuationDeviationsAt
        profile root) :
    terminalPayoff.IsNashAtContinuation
        assembly root profile hfirst ↔
      terminalPayoff.IsNashAtContinuation
        assembly root profile hsecond := by
  rfl

/-- Nash optimality on presentation-designated continuations for expected
eventual terminal payoff under canonical absolute-prefix semantics. -/
def IsNashOnPresentation
    {presentation : G.MeasurableKernelPresentation model}
    (assembly : presentation.ProfileAssembly)
    (roots : G.RootPresentation)
    (profile : assembly.PlayerKernelProfile)
    (hterminates :
      ∀ root, roots.IsRoot root →
        assembly.EventuallyTerminatesUnderContinuationDeviationsAt
          profile root) :
    Prop :=
  ∀ root, ∀ hroot : roots.IsRoot root,
    terminalPayoff.IsNashAtContinuation
      assembly root profile
      (hterminates root hroot)

/-- Expected-eventual-terminal-payoff subgame perfection under absolute-prefix
semantics on an explicit, possibly conservative, lawful subgame system. -/
def IsSubgamePerfectOn
    {presentation : G.MeasurableKernelPresentation model}
    (assembly : presentation.ProfileAssembly)
    (system : G.SubgameSystem)
    (profile : assembly.PlayerKernelProfile)
    (hterminates :
      ∀ root, system.IsRoot root →
        assembly.EventuallyTerminatesUnderContinuationDeviationsAt
          profile root) :
    Prop :=
  ∀ root, ∀ hroot : system.IsRoot root,
    terminalPayoff.IsNashAtContinuation
      assembly root profile
      (hterminates root hroot)

/-- Standard expected-eventual-terminal-payoff SPE under absolute-prefix
semantics on every structurally lawful subgame root. -/
def IsStandardSubgamePerfect
    {presentation : G.MeasurableKernelPresentation model}
    (assembly : presentation.ProfileAssembly)
    (system : G.CompleteSubgameSystem)
    (profile : assembly.PlayerKernelProfile)
    (hterminates :
      ∀ root, system.toSubgameSystem.IsRoot root →
        assembly.EventuallyTerminatesUnderContinuationDeviationsAt
          profile root) :
    Prop :=
  terminalPayoff.IsSubgamePerfectOn assembly
    system.toSubgameSystem profile hterminates

/-- Absolute-prefix designated-root terminal-payoff Nash implies continuation
Nash optimality at the initial history. -/
theorem IsNashOnPresentation.isNashAtContinuation_init
    {presentation : G.MeasurableKernelPresentation model}
    {assembly : presentation.ProfileAssembly}
    {roots : G.RootPresentation}
    {profile : assembly.PlayerKernelProfile}
    {hterminates :
      ∀ root, roots.IsRoot root →
        assembly.EventuallyTerminatesUnderContinuationDeviationsAt
          profile root}
    (hspe :
      terminalPayoff.IsNashOnPresentation
        assembly roots profile hterminates) :
    terminalPayoff.IsNashAtContinuation assembly
      (Arena.HistoryFrom.nil G.base.toArena G.base.init)
      profile
      (hterminates
        (Arena.HistoryFrom.nil G.base.toArena G.base.init)
        roots.init_isRoot) :=
  hspe _ roots.init_isRoot

/-- Constructive Nash optimality for expected eventual terminal payoff after
restarting at one root.

The certificate covers both the baseline and every admitted deviation, so
each expected eventual payoff in the comparison is mathematically justified.
-/
def IsNashAtFreshRestart
    {presentation : G.MeasurableKernelPresentation model}
    (assembly : presentation.ProfileAssembly)
    (root : CompleteHistory G)
    (profile : assembly.PlayerKernelProfile)
    (hterminates :
      assembly.EventuallyTerminatesUnderFreshRestartDeviationsAt
        profile root) :
    Prop :=
  ∀ (who : N) (strategy : assembly.PlayerStrategy who),
    terminalPayoff.expectedEventualUtility
        (assembly.toKernelBehavioralProfile
          (MeasurableKernelPresentation.ProfileAssembly.PlayerKernelProfile.deviate
            (assembly := assembly)
            profile who strategy))
        root
        (hterminates.deviation_terminates who strategy)
        who ≤
      terminalPayoff.expectedEventualUtility
        (assembly.toKernelBehavioralProfile profile)
        root hterminates.profile_terminates who

/-- The terminal-payoff Nash predicate is independent of the chosen
termination proof. -/
theorem isNashAtFreshRestart_proof_irrel
    {presentation : G.MeasurableKernelPresentation model}
    (assembly : presentation.ProfileAssembly)
    (root : CompleteHistory G)
    (profile : assembly.PlayerKernelProfile)
    (hfirst hsecond :
      assembly.EventuallyTerminatesUnderFreshRestartDeviationsAt
        profile root) :
    terminalPayoff.IsNashAtFreshRestart
        assembly root profile hfirst ↔
      terminalPayoff.IsNashAtFreshRestart
        assembly root profile hsecond := by
  rfl

/-- Nash optimality on presentation-designated fresh restarts for expected
eventual terminal payoff. -/
def IsNashOnFreshRestartPresentation
    {presentation : G.MeasurableKernelPresentation model}
    (assembly : presentation.ProfileAssembly)
    (roots : G.RootPresentation)
    (profile : assembly.PlayerKernelProfile)
    (hterminates :
      ∀ root, roots.IsRoot root →
        assembly.EventuallyTerminatesUnderFreshRestartDeviationsAt
          profile root) :
    Prop :=
  ∀ root, ∀ hroot : roots.IsRoot root,
      terminalPayoff.IsNashAtFreshRestart assembly root profile
      (hterminates root hroot)

/-- Expected-eventual-terminal-payoff subgame perfection under fresh restart
on an explicit, possibly conservative, lawful subgame system. -/
def IsFreshRestartSubgamePerfectOn
    {presentation : G.MeasurableKernelPresentation model}
    (assembly : presentation.ProfileAssembly)
    (system : G.SubgameSystem)
    (profile : assembly.PlayerKernelProfile)
    (hterminates :
      ∀ root, system.IsRoot root →
        assembly.EventuallyTerminatesUnderFreshRestartDeviationsAt
          profile root) :
    Prop :=
  ∀ root, ∀ hroot : system.IsRoot root,
    terminalPayoff.IsNashAtFreshRestart assembly root profile
      (hterminates root hroot)

/-- Standard expected-eventual-terminal-payoff SPE under fresh restart on
every structurally lawful subgame root. -/
def IsFreshRestartStandardSubgamePerfect
    {presentation : G.MeasurableKernelPresentation model}
    (assembly : presentation.ProfileAssembly)
    (system : G.CompleteSubgameSystem)
    (profile : assembly.PlayerKernelProfile)
    (hterminates :
      ∀ root, system.toSubgameSystem.IsRoot root →
        assembly.EventuallyTerminatesUnderFreshRestartDeviationsAt
          profile root) :
    Prop :=
  terminalPayoff.IsFreshRestartSubgamePerfectOn assembly
    system.toSubgameSystem profile hterminates

/-- Eventual-terminal-payoff designated-root Nash implies the corresponding
initial-history Nash property. -/
theorem IsNashOnFreshRestartPresentation.isNashAt_init
    {presentation : G.MeasurableKernelPresentation model}
    {assembly : presentation.ProfileAssembly}
    {roots : G.RootPresentation}
    {profile : assembly.PlayerKernelProfile}
    {hterminates :
      ∀ root, roots.IsRoot root →
        assembly.EventuallyTerminatesUnderFreshRestartDeviationsAt
          profile root}
    (hspe :
      terminalPayoff.IsNashOnFreshRestartPresentation
        assembly roots profile hterminates) :
    terminalPayoff.IsNashAtFreshRestart assembly
      (Arena.HistoryFrom.nil G.base.toArena G.base.init)
      profile
      (hterminates
        (Arena.HistoryFrom.nil G.base.toArena G.base.init)
        roots.init_isRoot) :=
  hspe _ roots.init_isRoot

end BoundedTerminalPayoffExtension
end MeasurableHistoryModel

end ExtensiveGame.ObservedGame
