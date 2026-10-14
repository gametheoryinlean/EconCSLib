/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.Examples.ExtensiveGame.FiniteExecutionIntegral
import EconCSLib.Examples.ExtensiveGame.ObservedMeasurableKernelAlmostSureOutcomeBoundary

/-!
# Effective truncation certificates for eventual terminal payoff

This opt-in prototype computes a rational stopped expectation and an error
radius from `Arena.noneMass`. It retains the finite-budget search and also
executes `leastHorizon` / `approximate` without a budget at positive tolerance.
The semantic target is the existing zero-guarded `eventualUtility` under the
actual history `Kernel.traj` used in `FiniteExecutionIntegral`.

Terminal absorption makes the error zero on already terminal coordinates;
on unfinished coordinates stopped utility is zero, so the error is at most
the terminal bound, giving `M * q_H` rather than a two-payoff difference bound.
Almost-sure eventual termination supplies measurability and integrability.
Continuity from above of the measurable decreasing no-hit events proves
vanishing unfinished mass from almost-sure reachability. This supplies the
proof-only termination argument for exact sequential `Nat.find` search.
No uniform termination bound, convergence rate, or finite expected hitting
time is required. Tolerance zero remains confined to the budgeted interface.
Numerical operations use exact rational arithmetic, complete histories, and
the existing finite executor; the integrals occur only in proofs.

The algorithms require no ambient enumeration or countability. The automatic
path-legality and integral-correctness theorems use countable discrete complete
histories to make the varying history relation measurable. Their process
premise is almost-sure terminal reachability, proved in the repeat-or-stop
regression from its geometric unfinished mass. The pointwise inequality and
eventual-integrability lemma also apply to general measurable history models.
-/

open MeasureTheory ProbabilityTheory

namespace Examples.ExtensiveGame.FiniteTruncation

open FiniteExecutionIntegral (stoppedExpectedPayoff historyLaw_eq_coordinate
  integrable_historyPayoff integral_historyPayoff integral_stoppedUtility)

local macro "historyPath(" arena:term ", " start:term ", " policy:term ", " current:term ")" :
    term =>
  `(@Kernel.traj (fun _ => ($arena).HistoryFrom $start) (fun _ => ⊤)
    ((Arena.StochasticHistoryPolicy.toKernelPolicy $policy).toMeasurable.pathStepKernel
      (Arena.historyKernelArena $arena $start).toMeasurable_measurableSet_terminalSet)
    (fun time => MeasurableKernelArena.ActionPolicy.pathStepKernel_isMarkov
      (Arena.StochasticHistoryPolicy.toKernelPolicy $policy).toMeasurable
      (Arena.historyKernelArena $arena $start).toMeasurable_measurableSet_terminalSet time)
    0 (fun _ => $current))

local notation "μ[" atoms "]" =>
  List.foldr (fun (atom : _ × ℚ≥0) rest =>
    ((Prod.snd atom : ℚ≥0) : ENNReal) • Measure.dirac (Prod.fst atom) + rest) 0 atoms

section Computation

variable {A : Arena} {start : A.State}
variable [(state : A.State) → Decidable (A.IsTerminal state)]

/-- Rational center and nonnegative rational error radius. Unfinished
histories contribute zero to the center and their mass times `bound` to the radius. -/
def estimate (policy : A.StochasticHistoryPolicy start) (current : A.HistoryFrom start)
    (payoff : A.HistoryFrom start → ℚ) (bound : ℚ≥0) (horizon : ℕ) : ℚ × ℚ≥0 :=
  (stoppedExpectedPayoff policy current horizon payoff,
    bound * Arena.noneMass policy current horizon)

/-- Search horizons `0, ..., budget - 1` for the requested error tolerance.
The budget counts candidate horizons, including zero. `none` means only that
none of these candidates meets the tolerance, not that execution never terminates. -/
def searchHorizon (policy : A.StochasticHistoryPolicy start) (current : A.HistoryFrom start)
    (bound tolerance : ℚ≥0) (budget : ℕ) : Option ℕ :=
  (List.range budget).find? (fun horizon =>
    decide (bound * Arena.noneMass policy current horizon ≤ tolerance))

/-- Return the selected horizon together with its exact center and radius.
The payoff is evaluated only at the selected horizon. -/
def search (policy : A.StochasticHistoryPolicy start) (current : A.HistoryFrom start)
    (payoff : A.HistoryFrom start → ℚ) (bound tolerance : ℚ≥0) (budget : ℕ) :
    Option (ℕ × ℚ × ℚ≥0) :=
  (searchHorizon policy current bound tolerance budget).map fun horizon =>
    (horizon, estimate policy current payoff bound horizon)

/-- A successful search stays inside its budget and meets the rational tolerance. -/
theorem searchHorizon_sound (policy : A.StochasticHistoryPolicy start)
    (current : A.HistoryFrom start) (bound tolerance : ℚ≥0) (budget horizon : ℕ)
    (h : searchHorizon policy current bound tolerance budget = some horizon) :
    horizon < budget ∧ bound * Arena.noneMass policy current horizon ≤ tolerance := by
  refine ⟨List.mem_range.mp (List.mem_of_find?_eq_some h), ?_⟩
  have hp := List.find?_some (p := fun n =>
    decide (bound * Arena.noneMass policy current n ≤ tolerance)) h
  exact of_decide_eq_true hp

/-- Exhaustion is exactly failure of the finitely many tested inequalities.
It makes no claim about any later horizon or eventual termination. -/
theorem searchHorizon_eq_none_iff (policy : A.StochasticHistoryPolicy start)
    (current : A.HistoryFrom start) (bound tolerance : ℚ≥0) (budget : ℕ) :
    searchHorizon policy current bound tolerance budget = none ↔
      ∀ horizon < budget, tolerance < bound * Arena.noneMass policy current horizon := by
  simp [searchHorizon, List.find?_eq_none]

/-- Every returned tuple contains the actual computed center and a radius
within the tolerance, at a horizon strictly below the candidate budget. -/
theorem search_sound (policy : A.StochasticHistoryPolicy start)
    (current : A.HistoryFrom start) (payoff : A.HistoryFrom start → ℚ)
    (bound tolerance : ℚ≥0) (budget horizon : ℕ) (center : ℚ) (radius : ℚ≥0)
    (h : search policy current payoff bound tolerance budget = some (horizon, center, radius)) :
    horizon < budget ∧ estimate policy current payoff bound horizon = (center, radius) ∧
      radius ≤ tolerance := by
  obtain ⟨n, hn, heq⟩ := Option.map_eq_some_iff.mp h
  have hsound := searchHorizon_sound policy current bound tolerance budget n hn
  cases heq
  exact ⟨hsound.1, rfl, hsound.2⟩

end Computation

section EventualUtility

open _root_.ExtensiveGame.ObservedGame
open MeasurableHistoryModel
open MeasurableKernelPresentation.KernelBehavioralProfile

variable {N : Type*} {G : _root_.ExtensiveGame.ObservedGame N ℝ}
variable {model : MeasurableHistoryModel G}
variable [(state : G.base.State) → Decidable (G.base.isTerminal state)]

/-- Once a terminal coordinate is reached on an absorbing path, the existing
eventual utility already equals that coordinate's stopped utility. Absorption
is required at every terminal visit, not merely after some later terminal hit. -/
theorem eventual_eq_stopped_of_terminal (extension : BoundedTerminalPayoffExtension G model)
    (player : N) (path : ℕ → model.toArena.State) (horizon : ℕ)
    (habsorbing : ∀ time, G.base.isTerminal (path time).1 → path (time + 1) = path time)
    (hterminal : G.base.isTerminal (path horizon).1) :
    extension.eventualUtility player path =
      extension.toTerminalPayoffExtension.stoppedUtility horizon player path := by
  classical
  letI (state : G.base.State) : Decidable (G.base.isTerminal state) :=
    Classical.propDecidable _
  have habsorbs : EventuallyAbsorbsAtTerminal (G := G) (model := model) path :=
    ⟨horizon, hterminal, fun later hle =>
      (Arena.path_eq_of_terminal_of_le path habsorbing hterminal hle).1⟩
  have hs := Nat.find_spec habsorbs
  have heq : path (Nat.find habsorbs) = path horizon := by
    calc
      path (Nat.find habsorbs) = path (max (Nat.find habsorbs) horizon) :=
        (hs.2 _ (le_max_left _ _)).symm
      _ = path horizon := (Arena.path_eq_of_terminal_of_le path habsorbing hterminal
        (le_max_right _ _)).1
  simp only [BoundedTerminalPayoffExtension.eventualUtility, dif_pos habsorbs,
    TerminalPayoffExtension.stoppedUtility, if_pos hterminal]
  exact congrArg (extension.payoff player) heq

/-- Pointwise localization of truncation error. The bound is `M` on unfinished
coordinates because their stopped payoff is zero, and zero on terminal ones. -/
theorem truncation_pointwise (extension : BoundedTerminalPayoffExtension G model)
    (player : N) (path : ℕ → model.toArena.State) (horizon : ℕ) (bound : ℚ≥0)
    (hbound : (extension.bound : ℝ) ≤ (bound : ℝ))
    (habsorbing : ∀ time, G.base.isTerminal (path time).1 → path (time + 1) = path time) :
    ‖extension.eventualUtility player path -
      extension.toTerminalPayoffExtension.stoppedUtility horizon player path‖ ≤
        if G.base.isTerminal (path horizon).1 then 0 else (bound : ℝ) := by
  by_cases ht : G.base.isTerminal (path horizon).1
  · rw [if_pos ht, eventual_eq_stopped_of_terminal extension player path horizon habsorbing ht]
    simp
  · rw [if_neg ht, extension.toTerminalPayoffExtension.stoppedUtility_eq_zero horizon player path ht,
      sub_zero]
    exact (extension.norm_eventualUtility_le player path).trans hbound

/-- Almost-sure eventual absorption proves integrability under any finite path
measure, by measurable stopped approximants and the existing uniform bound. -/
theorem integrable_eventual (extension : BoundedTerminalPayoffExtension G model)
    (μ : Measure (ℕ → model.toArena.State)) [IsFiniteMeasure μ] (player : N)
    (hterminates : ∀ᵐ path ∂μ, EventuallyAbsorbsAtTerminal (G := G) (model := model) path) :
    Integrable (extension.eventualUtility player) μ := by
  have hmeas : AEStronglyMeasurable (extension.eventualUtility player) μ :=
    aestronglyMeasurable_of_tendsto_ae Filter.atTop
      (fun horizon => (extension.toTerminalPayoffExtension.stoppedUtility_measurable
        horizon player).aestronglyMeasurable)
      (hterminates.mono fun path hp =>
        extension.stoppedUtility_tendsto_eventualUtility player path hp)
  apply (integrable_const (extension.bound : ℝ)).mono hmeas
  exact Filter.Eventually.of_forall fun path => by
    simpa using extension.norm_eventualUtility_le player path

end EventualUtility

section HistorySemantics

variable {A : Arena} {start : A.State}
variable [(state : A.State) → Decidable (A.IsTerminal state)]

local instance : MeasurableSpace (A.HistoryFrom start) := ⊤

local instance : (history : (A.historyKernelArena start).State) →
    Decidable (IsEmpty ((A.historyKernelArena start).Action history)) :=
  fun history => inferInstanceAs (Decidable (A.IsTerminal history.1))

/-- J's coordinate correspondence identifies the executable unfinished mass
with the actual unfinished cylinder probability, without a marginal certificate. -/
theorem measure_unfinished (policy : A.StochasticHistoryPolicy start)
    (current : A.HistoryFrom start) (horizon : ℕ) :
    historyPath(A, start, policy, current) {path | ¬ A.IsTerminal (path horizon).1} =
      (Arena.noneMass policy current horizon : ENNReal) := by
  have hm : MeasurableSet {h : A.HistoryFrom start | ¬ A.IsTerminal h.1} :=
    MeasurableSpace.measurableSet_top
  change historyPath(A, start, policy, current)
    ((fun path : ℕ → A.HistoryFrom start => path horizon) ⁻¹' {h | ¬ A.IsTerminal h.1}) = _
  rw [← Measure.map_apply (μ := historyPath(A, start, policy, current))
    (f := fun path : ℕ → A.HistoryFrom start => path horizon) (measurable_pi_apply horizon) hm]
  have hcoordinate : (historyPath(A, start, policy, current)).map
      (fun path : ℕ → A.HistoryFrom start => path horizon) =
        μ[(A.stochasticHistoryLawFrom policy current horizon).atoms] :=
    historyLaw_eq_coordinate policy current horizon
  rw [hcoordinate]
  simpa only [Arena.noneMass, Arena.pathMarginal, decide_eq_true_eq] using
    FiniteLawIntegral.measure_eventMass
      (A.stochasticHistoryLawFrom policy current horizon)
      (fun h => decide (¬ A.IsTerminal h.1)) MeasurableSpace.measurableSet_top

private theorem expectRat_unfinished (law : FiniteLaw (A.HistoryFrom start)) (bound : ℚ≥0) :
    law.expectRat (fun h => if A.IsTerminal h.1 then 0 else (bound : ℚ)) =
      ((bound * law.eventMass (fun h => decide (¬ A.IsTerminal h.1)) : ℚ≥0) : ℚ) := by
  unfold FiniteLaw.expectRat FiniteLaw.eventMass
  induction law.atoms with
  | nil => simp
  | cons atom atoms ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [ih]
      by_cases ht : A.IsTerminal atom.1.1 <;> simp [ht, mul_add, mul_comm]

/-- The dominating error observable has integral exactly the computed radius. -/
theorem integral_unfinished (policy : A.StochasticHistoryPolicy start)
    (current : A.HistoryFrom start) (horizon : ℕ) (bound : ℚ≥0) :
    (∫ path, (if A.IsTerminal (path horizon).1 then 0 else (bound : ℝ))
      ∂historyPath(A, start, policy, current)) =
        ((bound * Arena.noneMass policy current horizon : ℚ≥0) : ℝ) := by
  have h := integral_historyPayoff policy current horizon
    (fun h => if A.IsTerminal h.1 then 0 else (bound : ℚ))
  rw [expectRat_unfinished] at h
  simpa only [apply_ite Rat.cast, Rat.cast_zero, NNRat.cast_def, Rat.cast_div, Rat.cast_natCast,
    Arena.noneMass, Arena.pathMarginal] using h

private theorem ae_of_positive {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] (law : FiniteLaw α) (p : α → Prop)
    (hp : ∀ x, law.HasPositiveAtom x → p x) : ∀ᵐ x ∂μ[law.atoms], p x := by
  have aux (atoms : List (α × ℚ≥0))
      (h : ∀ atom ∈ atoms, atom.2 ≠ 0 → p atom.1) : ∀ᵐ x ∂μ[atoms], p x := by
    induction atoms with
    | nil => simp
    | cons atom atoms ih =>
        rw [List.foldr_cons, ae_add_measure_iff]
        refine ⟨?_, ih (fun a ha => h a (by simp [ha]))⟩
        by_cases hz : atom.2 = 0
        · simp [hz, ← ENNReal.coe_nnratCast]
        · apply Measure.ae_smul_measure
          simpa only [ae_dirac_eq, Filter.eventually_pure] using h atom (by simp) hz
  exact aux law.atoms (fun atom ha hz => hp atom.1 ⟨atom.2, ha, hz⟩)

private theorem stepKernel_eq (policy : A.StochasticHistoryPolicy start)
    (current : A.HistoryFrom start) :
    policy.toKernelPolicy.toMeasurable.stepKernel
      (A.historyKernelArena start).toMeasurable_measurableSet_terminalSet current =
        μ[(Arena.absorbingStepLaw policy current).atoms] := by
  obtain ⟨execution⟩ := MeasurableKernelArena.ActionPolicy.EndpointExecution.nonempty
    policy.toKernelPolicy.toMeasurable
    (A.historyKernelArena start).toMeasurable_measurableSet_terminalSet
  letI := execution
  have h := policy.toKernelPolicy.toMeasurable_endpointMeasure 1 current
  rw [MeasurableKernelArena.ActionPolicy.endpointMeasure,
    MeasurableKernelArena.ActionPolicy.endpointKernel_one] at h
  rw [Arena.absorbingStepLaw_eq_stochasticHistoryLawFrom_one]
  exact h.trans (congrArg (fun law : FiniteLaw (A.HistoryFrom start) => μ[law.atoms])
    (Arena.historyKernelArena_stateLawFrom_eq_stochasticHistoryLawFrom policy 1 current))

omit [(state : A.State) → Decidable (A.IsTerminal state)] in
/-- Normalization of the actual history trajectory is inherited from its
Markov step kernels; it is not a caller-supplied probability certificate. -/
theorem historyPath_probability (policy : A.StochasticHistoryPolicy start)
    (current : A.HistoryFrom start) : IsProbabilityMeasure historyPath(A, start, policy, current) := by
  obtain ⟨execution⟩ := MeasurableKernelArena.ActionPolicy.PathExecution.nonempty
    policy.toKernelPolicy.toMeasurable
    (A.historyKernelArena start).toMeasurable_measurableSet_terminalSet
  letI := execution
  have hp := MeasurableKernelArena.ActionPolicy.pathMeasure_isProbability
    policy.toKernelPolicy.toMeasurable
    (A.historyKernelArena start).toMeasurable_measurableSet_terminalSet current
  change IsProbabilityMeasure (MeasurableKernelArena.ActionPolicy.PathExecution.path _ _ _) at hp
  rw [MeasurableKernelArena.ActionPolicy.PathExecution.path_eq] at hp
  exact hp

/-- On countable discrete complete histories the actual analytic executor
almost surely takes legal positive-policy steps or stays at a terminal history.
Countability is used only for measurability of the varying history relation;
no countability encoder is used by the finite algorithms. -/
theorem ae_legal [Countable (A.HistoryFrom start)] (policy : A.StochasticHistoryPolicy start)
    (current : A.HistoryFrom start) :
    ∀ᵐ path ∂historyPath(A, start, policy, current),
      ∀ time, Arena.IsLegalAbsorbingTransition policy (path time) (path (time + 1)) := by
  rw [eventually_countable_forall]
  intro time
  let κ : (n : ℕ) → Kernel (Finset.Iic n → A.HistoryFrom start) (A.HistoryFrom start) :=
    policy.toKernelPolicy.toMeasurable.pathStepKernel
    (A.historyKernelArena start).toMeasurable_measurableSet_terminalSet
  letI : ∀ n, IsMarkovKernel (κ n) := fun n =>
    MeasurableKernelArena.ActionPolicy.pathStepKernel_isMarkov _ _ n
  have hc : ∀ᵐ pair ∂(Kernel.partialTraj (X := fun _ => A.HistoryFrom start)
      κ 0 time (fun _ => current) ⊗ₘ κ time),
      Arena.IsLegalAbsorbingTransition policy
        (pair.1 ⟨time, Finset.mem_Iic.mpr le_rfl⟩) pair.2 := by
    apply Measure.ae_compProd_of_ae_ae (Set.to_countable _).measurableSet
    refine Filter.Eventually.of_forall fun historyPrefix => ?_
    change ∀ᵐ next ∂policy.toKernelPolicy.toMeasurable.stepKernel
      (A.historyKernelArena start).toMeasurable_measurableSet_terminalSet
      (historyPrefix ⟨time, Finset.mem_Iic.mpr le_rfl⟩), _
    rw [stepKernel_eq]
    apply ae_of_positive (α := A.HistoryFrom start)
    intro next hn
    let h := historyPrefix ⟨time, Finset.mem_Iic.mpr le_rfl⟩
    by_cases ht : A.IsTerminal h.1
    · rw [Arena.absorbingStepLaw, dif_pos ht] at hn
      exact Or.inl ⟨ht, (FiniteLaw.hasPositiveAtom_pure_iff h next).mp hn⟩
    · rw [Arena.absorbingStepLaw, dif_neg ht] at hn
      obtain ⟨action, ha, heq⟩ := (FiniteLaw.hasPositiveAtom_map_iff _ _ _).mp hn
      exact Or.inr ⟨ht, action, ha, heq.symm⟩
  rw [Kernel.partialTraj_compProd_eq_map_traj (X := fun _ => A.HistoryFrom start)
    (Nat.zero_le time)] at hc
  exact ae_of_ae_map (by fun_prop) hc

/-- Legal terminal-aware transitions imply absorption at every terminal visit. -/
theorem ae_absorbing [Countable (A.HistoryFrom start)]
    (policy : A.StochasticHistoryPolicy start) (current : A.HistoryFrom start) :
    ∀ᵐ path ∂historyPath(A, start, policy, current),
      ∀ time, A.IsTerminal (path time).1 → path (time + 1) = path time := by
  filter_upwards [ae_legal policy current] with path hp time ht
  rcases hp time with hstay | hstep
  · exact hstay.2
  · exact (hstep.1 ht).elim

/-- The actual trajectory is almost surely a canonical complete play from
the supplied incoming history. J proves the marginals and `ae_legal` proves
the transition certificate consumed by the existing complete-play theorem. -/
theorem ae_completePlay [Countable (A.HistoryFrom start)]
    (policy : A.StochasticHistoryPolicy start) (current : A.HistoryFrom start) :
    ∀ᵐ path ∂historyPath(A, start, policy, current), A.IsCompletePlayPathFrom current path := by
  letI := historyPath_probability policy current
  exact Arena.pathLaw_ae_isCompletePlayPathFrom policy current
    ⟨historyPath(A, start, policy, current), inferInstance⟩
    (fun horizon => historyLaw_eq_coordinate policy current horizon)
    (ae_legal policy current)

/-- With absorption, being unfinished at `H` is almost surely the event
`T > H`, expressed without choosing an unbounded first hitting time. -/
theorem measure_no_hit [Countable (A.HistoryFrom start)]
    (policy : A.StochasticHistoryPolicy start) (current : A.HistoryFrom start) (horizon : ℕ) :
    historyPath(A, start, policy, current)
      {path | ∀ time ≤ horizon, ¬ A.IsTerminal (path time).1} =
      (Arena.noneMass policy current horizon : ENNReal) := by
  refine (measure_congr ?_).trans (measure_unfinished policy current horizon)
  filter_upwards [ae_absorbing policy current] with path habs
  apply propext
  constructor
  · exact fun h => h horizon le_rfl
  · intro h time hle ht
    exact h (Arena.path_eq_of_terminal_of_le path habs ht hle).2

/-- Vanishing computed unfinished mass proves almost-sure terminal
reachability. This theorem requires convergence, not an effective rate;
the bounded search does not infer such a rate or promise success. -/
theorem ae_reaches_of_mass_tendsto_zero (policy : A.StochasticHistoryPolicy start)
    (current : A.HistoryFrom start)
    (hmass : Filter.Tendsto (fun horizon => (Arena.noneMass policy current horizon : ENNReal))
      Filter.atTop (nhds 0)) :
    ∀ᵐ path ∂historyPath(A, start, policy, current), ∃ time, A.IsTerminal (path time).1 := by
  rw [ae_iff]
  apply bot_unique
  apply ge_of_tendsto hmass
  refine Filter.Eventually.of_forall fun horizon => ?_
  rw [← measure_unfinished]
  exact measure_mono (fun path h ht => h ⟨horizon, ht⟩)

end HistorySemantics

section PositiveTolerance

variable {A : Arena} {start : A.State}

local instance : MeasurableSpace (A.HistoryFrom start) := ⊤

/-- No terminal visit through a fixed horizon is a measurable event, including
on raw paths that need not absorb after a terminal visit. -/
theorem measurableSet_no_hit (horizon : ℕ) :
    MeasurableSet {path : ℕ → A.HistoryFrom start |
      ∀ time ≤ horizon, ¬ A.IsTerminal (path time).1} := by
  simp only [Set.setOf_forall]
  apply MeasurableSet.iInter
  intro time
  apply MeasurableSet.iInter
  intro _
  exact (MeasurableSpace.measurableSet_top (s :=
    {h : A.HistoryFrom start | ¬ A.IsTerminal h.1})).preimage (measurable_pi_apply time)

/-- No-hit events decrease pointwise; a single unfinished-coordinate event
would only decrease on absorbing paths. -/
theorem no_hit_antitone : Antitone (fun horizon : ℕ =>
    {path : ℕ → A.HistoryFrom start | ∀ time ≤ horizon, ¬ A.IsTerminal (path time).1}) :=
  fun _ _ hle _ hp time ht => hp time (ht.trans hle)

/-- The intersection of the finite no-hit events is exactly nontermination. -/
theorem iInter_no_hit :
    (⋂ horizon : ℕ, {path : ℕ → A.HistoryFrom start |
      ∀ time ≤ horizon, ¬ A.IsTerminal (path time).1}) =
      {path | ¬ ∃ time, A.IsTerminal (path time).1} := by
  ext path
  simp only [Set.mem_iInter, Set.mem_setOf_eq, not_exists]
  exact ⟨fun h time => h time time le_rfl, fun h _ time _ => h time⟩

variable [(state : A.State) → Decidable (A.IsTerminal state)]

/-- Almost-sure reachability forces the computed unfinished masses to vanish.
Continuity from above applies to no-hit events. Their identification with
`noneMass` uses the already proved almost-sure absorption of the actual law. -/
theorem mass_tendsto_zero_of_ae_reaches [Countable (A.HistoryFrom start)]
    (policy : A.StochasticHistoryPolicy start) (current : A.HistoryFrom start)
    (hreaches : ∀ᵐ path ∂historyPath(A, start, policy, current),
      ∃ time, A.IsTerminal (path time).1) :
    Filter.Tendsto (fun horizon => (Arena.noneMass policy current horizon : ENNReal))
      Filter.atTop (nhds 0) := by
  letI := historyPath_probability policy current
  have h := tendsto_measure_iInter_atTop
    (μ := historyPath(A, start, policy, current))
    (fun horizon => (measurableSet_no_hit (A := A) (start := start) horizon).nullMeasurableSet)
    no_hit_antitone ⟨0, measure_ne_top _ _⟩
  rw [iInter_no_hit, (ae_iff.mp hreaches)] at h
  simpa only [Function.comp_def, measure_no_hit] using h

/-- The exact rational radii converge to zero after the canonical real cast.
The ENNReal limit is finite, so `toReal` is continuous at that limit. -/
theorem radius_tendsto_zero [Countable (A.HistoryFrom start)]
    (policy : A.StochasticHistoryPolicy start) (current : A.HistoryFrom start) (bound : ℚ≥0)
    (hreaches : ∀ᵐ path ∂historyPath(A, start, policy, current),
      ∃ time, A.IsTerminal (path time).1) :
    Filter.Tendsto (fun horizon => ((bound * Arena.noneMass policy current horizon : ℚ≥0) : ℝ))
      Filter.atTop (nhds 0) := by
  have hmass : Filter.Tendsto (fun horizon => (Arena.noneMass policy current horizon : ℝ))
      Filter.atTop (nhds 0) := by
    simpa only [ENNReal.toReal_zero] using
      (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
        (mass_tendsto_zero_of_ae_reaches policy current hreaches)
  simpa only [NNRat.cast_mul, mul_zero] using hmass.const_mul (bound : ℝ)

/-- Positive rational tolerance is eventually met without a supplied rate,
budget, finite termination bound, or finite expected hitting time. -/
theorem exists_radius_le [Countable (A.HistoryFrom start)]
    (policy : A.StochasticHistoryPolicy start) (current : A.HistoryFrom start)
    (bound tolerance : ℚ≥0) (hpositive : 0 < tolerance)
    (hreaches : ∀ᵐ path ∂historyPath(A, start, policy, current),
      ∃ time, A.IsTerminal (path time).1) :
    ∃ horizon, bound * Arena.noneMass policy current horizon ≤ tolerance := by
  have ht : (0 : ℝ) < (tolerance : ℝ) := by exact_mod_cast hpositive
  obtain ⟨horizon, hh⟩ :=
    ((radius_tendsto_zero policy current bound hreaches).eventually_lt_const ht).exists
  exact ⟨horizon, NNRat.cast_le.mp hh.le⟩

/-- Execute exact rational tests at horizons `0, 1, ...` until the first
acceptable radius. Almost-sure reachability proves termination in `Prop`;
`Nat.find` performs the search and does not extract a classical witness.
Countability is proof-only and supplies no runtime encoder. -/
def leastHorizon [Countable (A.HistoryFrom start)]
    (policy : A.StochasticHistoryPolicy start) (current : A.HistoryFrom start)
    (bound tolerance : ℚ≥0) (hpositive : 0 < tolerance)
    (hreaches : ∀ᵐ path ∂historyPath(A, start, policy, current),
      ∃ time, A.IsTerminal (path time).1) : ℕ :=
  Nat.find (exists_radius_le policy current bound tolerance hpositive hreaches)

/-- The executed horizon meets tolerance and every smaller horizon fails. -/
theorem leastHorizon_spec [Countable (A.HistoryFrom start)]
    (policy : A.StochasticHistoryPolicy start) (current : A.HistoryFrom start)
    (bound tolerance : ℚ≥0) (hpositive : 0 < tolerance)
    (hreaches : ∀ᵐ path ∂historyPath(A, start, policy, current),
      ∃ time, A.IsTerminal (path time).1) :
    bound * Arena.noneMass policy current
        (leastHorizon policy current bound tolerance hpositive (by exact hreaches)) ≤ tolerance ∧
      ∀ earlier < leastHorizon policy current bound tolerance hpositive (by exact hreaches),
        tolerance < bound * Arena.noneMass policy current earlier := by
  unfold leastHorizon
  exact ⟨Nat.find_spec (exists_radius_le policy current bound tolerance hpositive hreaches),
    fun _ h => lt_of_not_ge
      (Nat.find_min (exists_radius_le policy current bound tolerance hpositive hreaches) h)⟩

/-- Kernel-friendly characterization of the least computed horizon. -/
theorem leastHorizon_eq_iff [Countable (A.HistoryFrom start)]
    (policy : A.StochasticHistoryPolicy start) (current : A.HistoryFrom start)
    (bound tolerance : ℚ≥0) (hpositive : 0 < tolerance)
    (hreaches : ∀ᵐ path ∂historyPath(A, start, policy, current),
      ∃ time, A.IsTerminal (path time).1) (horizon : ℕ) :
    leastHorizon policy current bound tolerance hpositive (by exact hreaches) = horizon ↔
      bound * Arena.noneMass policy current horizon ≤ tolerance ∧
        ∀ earlier < horizon, tolerance < bound * Arena.noneMass policy current earlier := by
  simp only [leastHorizon, Nat.find_eq_iff, not_le]

/-- Return the least horizon and its existing rational stopped estimate.
Only finite execution and rational comparison run; analytic assumptions and
the termination argument are erased. There is no claimed complexity bound. -/
def approximate [Countable (A.HistoryFrom start)]
    (policy : A.StochasticHistoryPolicy start) (current : A.HistoryFrom start)
    (payoff : A.HistoryFrom start → ℚ) (bound tolerance : ℚ≥0) (hpositive : 0 < tolerance)
    (hreaches : ∀ᵐ path ∂historyPath(A, start, policy, current),
      ∃ time, A.IsTerminal (path time).1) : ℕ × ℚ × ℚ≥0 :=
  let horizon := leastHorizon policy current bound tolerance hpositive (by exact hreaches)
  (horizon, estimate policy current payoff bound horizon)

/-- The old bounded search finds exactly the same least horizon when its
candidate budget includes it, and returns `none` for every smaller budget. -/
theorem searchHorizon_eq_leastHorizon [Countable (A.HistoryFrom start)]
    (policy : A.StochasticHistoryPolicy start) (current : A.HistoryFrom start)
    (bound tolerance : ℚ≥0) (hpositive : 0 < tolerance)
    (hreaches : ∀ᵐ path ∂historyPath(A, start, policy, current),
      ∃ time, A.IsTerminal (path time).1) (budget : ℕ) :
    searchHorizon policy current bound tolerance budget =
      if leastHorizon policy current bound tolerance hpositive (by exact hreaches) < budget then
        some (leastHorizon policy current bound tolerance hpositive (by exact hreaches))
      else none := by
  have hs := leastHorizon_spec policy current bound tolerance hpositive hreaches
  split_ifs with hb
  · apply List.find?_eq_some_iff_getElem.mpr
    refine ⟨by simpa using hs.1,
      leastHorizon policy current bound tolerance hpositive (by exact hreaches), ?_, ?_, ?_⟩
    · simpa using hb
    · simp
    · intro earlier hearlier
      simpa using hs.2 earlier hearlier
  · apply (searchHorizon_eq_none_iff policy current bound tolerance budget).mpr
    exact fun earlier hearlier => hs.2 earlier (hearlier.trans_le (Nat.le_of_not_gt hb))

/-- Including the least horizon returns the identical tuple through the
budgeted API. Excluding it retains the original exhaustion semantics. -/
theorem search_eq_approximate [Countable (A.HistoryFrom start)]
    (policy : A.StochasticHistoryPolicy start) (current : A.HistoryFrom start)
    (payoff : A.HistoryFrom start → ℚ) (bound tolerance : ℚ≥0) (hpositive : 0 < tolerance)
    (hreaches : ∀ᵐ path ∂historyPath(A, start, policy, current),
      ∃ time, A.IsTerminal (path time).1) (budget : ℕ) :
    search policy current payoff bound tolerance budget =
      if (approximate policy current payoff bound tolerance hpositive
          (by exact hreaches)).1 < budget then
        some (approximate policy current payoff bound tolerance hpositive (by exact hreaches))
      else none := by
  rw [search, searchHorizon_eq_leastHorizon policy current bound tolerance hpositive hreaches]
  simp only [approximate]
  split_ifs <;> rfl

end PositiveTolerance

section Correctness

open _root_.ExtensiveGame.ObservedGame
open MeasurableHistoryModel
open MeasurableKernelPresentation.KernelBehavioralProfile

variable {N : Type*} {G : _root_.ExtensiveGame.ObservedGame N ℝ}
variable [(state : G.base.State) → Decidable (G.base.isTerminal state)]

local instance : MeasurableSpace (CompleteHistory G) := ⊤

/-- Finite-history execution plus almost-sure terminal reachability gives
the existing eventual-absorption condition. The absorption part is proved
from the actual kernel's transitions, not supplied as a new certificate. -/
theorem ae_eventuallyAbsorbs [Countable (CompleteHistory G)]
    (policy : G.base.toArena.StochasticHistoryPolicy G.base.init)
    (current : CompleteHistory G)
    (hreaches : ∀ᵐ path ∂historyPath(G.base.toArena, G.base.init, policy, current),
      ∃ time, G.base.isTerminal (path time).1) :
    ∀ᵐ path ∂historyPath(G.base.toArena, G.base.init, policy, current),
      EventuallyAbsorbsAtTerminal (G := G) (model := MeasurableHistoryModel.discrete G) path := by
  filter_upwards [hreaches, ae_absorbing policy current] with path hreach habs
  obtain ⟨time, ht⟩ := hreach
  exact ⟨time, ht, fun later hle => (Arena.path_eq_of_terminal_of_le path habs ht hle).1⟩

/-- Correctness of the rational interval for the existing eventual utility
under J's actual history path law. The process premise is terminal reachability;
legal transitions, absorption, marginals and both integrability facts are proved.
Countable complete histories are a proof-only measurability assumption here. -/
theorem estimate_correct [Countable (CompleteHistory G)]
    (extension : BoundedTerminalPayoffExtension G (MeasurableHistoryModel.discrete G))
    (policy : G.base.toArena.StochasticHistoryPolicy G.base.init)
    (current : CompleteHistory G) (player : N) (payoff : CompleteHistory G → ℚ)
    (bound : ℚ≥0) (horizon : ℕ)
    (hbound : (extension.bound : ℝ) ≤ (bound : ℝ))
    (hpayoff : ∀ h, G.base.isTerminal h.1 → (payoff h : ℝ) = G.base.payoff h.1 player)
    (hreaches : ∀ᵐ path ∂historyPath(G.base.toArena, G.base.init, policy, current),
      ∃ time, G.base.isTerminal (path time).1) :
    |(∫ path, extension.eventualUtility player path
        ∂historyPath(G.base.toArena, G.base.init, policy, current)) -
        ((estimate policy current payoff bound horizon).1 : ℝ)| ≤
      ((estimate policy current payoff bound horizon).2 : ℝ) := by
  let μ : Measure (ℕ → (MeasurableHistoryModel.discrete G).toArena.State) :=
    historyPath(G.base.toArena, G.base.init, policy, current)
  letI : IsProbabilityMeasure μ := historyPath_probability policy current
  have heventual := integrable_eventual extension μ player
    (ae_eventuallyAbsorbs policy current hreaches)
  have hstopped : Integrable (extension.toTerminalPayoffExtension.stoppedUtility horizon player)
      historyPath(G.base.toArena, G.base.init, policy, current) :=
    integrable_historyPayoff policy current horizon
      (fun h => if G.base.isTerminal h.1 then extension.payoff player h else 0)
  have hdom := integrable_historyPayoff policy current horizon
    (fun h => if G.base.isTerminal h.1 then 0 else (bound : ℝ))
  change |(∫ path, extension.eventualUtility player path ∂historyPath(G.base.toArena,
    G.base.init, policy, current)) - (stoppedExpectedPayoff policy current horizon payoff : ℝ)| ≤ _
  have hi : (∫ path : ℕ → CompleteHistory G,
      extension.toTerminalPayoffExtension.stoppedUtility horizon player path
        ∂historyPath(G.base.toArena, G.base.init, policy, current)) =
      (stoppedExpectedPayoff policy current horizon payoff : ℝ) :=
    integral_stoppedUtility extension.toTerminalPayoffExtension policy current horizon
      player payoff hpayoff
  have hsub : (∫ path : ℕ → CompleteHistory G,
      extension.eventualUtility player path -
        extension.toTerminalPayoffExtension.stoppedUtility horizon player path
      ∂historyPath(G.base.toArena, G.base.init, policy, current)) =
    (∫ path, extension.eventualUtility player path
      ∂historyPath(G.base.toArena, G.base.init, policy, current)) -
    (∫ path, extension.toTerminalPayoffExtension.stoppedUtility horizon player path
      ∂historyPath(G.base.toArena, G.base.init, policy, current)) := integral_sub heventual hstopped
  rw [← hi, ← hsub, ← Real.norm_eq_abs]
  calc
    _ ≤ ∫ path, (if G.base.isTerminal (path horizon).1 then 0 else (bound : ℝ))
        ∂historyPath(G.base.toArena, G.base.init, policy, current) := by
      apply norm_integral_le_of_norm_le hdom
      filter_upwards [ae_absorbing policy current] with path hp
      exact truncation_pointwise extension player path horizon bound hbound hp
    _ = _ := integral_unfinished policy current horizon bound

/-- A successful finite search certifies the requested error tolerance for
the actual eventual expectation. The search itself never evaluates an integral. -/
theorem search_correct [Countable (CompleteHistory G)]
    (extension : BoundedTerminalPayoffExtension G (MeasurableHistoryModel.discrete G))
    (policy : G.base.toArena.StochasticHistoryPolicy G.base.init)
    (current : CompleteHistory G) (player : N) (payoff : CompleteHistory G → ℚ)
    (bound tolerance : ℚ≥0) (budget horizon : ℕ) (center : ℚ) (radius : ℚ≥0)
    (hbound : (extension.bound : ℝ) ≤ (bound : ℝ))
    (hpayoff : ∀ h, G.base.isTerminal h.1 → (payoff h : ℝ) = G.base.payoff h.1 player)
    (hreaches : ∀ᵐ path ∂historyPath(G.base.toArena, G.base.init, policy, current),
      ∃ time, G.base.isTerminal (path time).1)
    (hresult : search policy current payoff bound tolerance budget = some (horizon, center, radius)) :
    horizon < budget ∧
      |(∫ path, extension.eventualUtility player path
          ∂historyPath(G.base.toArena, G.base.init, policy, current)) - (center : ℝ)| ≤ (radius : ℝ) ∧
      radius ≤ tolerance := by
  obtain ⟨hb, heq, hr⟩ := search_sound policy current payoff bound tolerance budget
    horizon center radius hresult
  have hc := estimate_correct extension policy current player payoff bound horizon hbound hpayoff
    hreaches
  rw [heq] at hc
  exact ⟨hb, hc, hr⟩

/-- The unbudgeted computation approximates the original eventual-utility
integral under the same hypotheses as `estimate_correct`, with positive
tolerance. The returned radius bounds the error and meets that tolerance. -/
theorem approximate_correct [Countable (CompleteHistory G)]
    (extension : BoundedTerminalPayoffExtension G (MeasurableHistoryModel.discrete G))
    (policy : G.base.toArena.StochasticHistoryPolicy G.base.init)
    (current : CompleteHistory G) (player : N) (payoff : CompleteHistory G → ℚ)
    (bound tolerance : ℚ≥0) (hpositive : 0 < tolerance)
    (hbound : (extension.bound : ℝ) ≤ (bound : ℝ))
    (hpayoff : ∀ h, G.base.isTerminal h.1 → (payoff h : ℝ) = G.base.payoff h.1 player)
    (hreaches : ∀ᵐ path ∂historyPath(G.base.toArena, G.base.init, policy, current),
      ∃ time, G.base.isTerminal (path time).1) :
    let result := approximate policy current payoff bound tolerance hpositive (by exact hreaches)
    |(∫ path, extension.eventualUtility player path
        ∂historyPath(G.base.toArena, G.base.init, policy, current)) - (result.2.1 : ℝ)| ≤
      (result.2.2 : ℝ) ∧ result.2.2 ≤ tolerance := by
  exact ⟨estimate_correct extension policy current player payoff bound
    (leastHorizon policy current bound tolerance hpositive (by exact hreaches)) hbound hpayoff hreaches,
    (leastHorizon_spec policy current bound tolerance hpositive hreaches).1⟩

end Correctness

namespace RepeatOrStop

open _root_.ExtensiveGame.ObservedGame

open Examples.ObservedMeasurableKernelAlmostSureOutcomeBoundary

local instance : (state : observed.base.State) → Decidable (observed.base.isTerminal state) :=
  terminalDecidable

local instance : Countable (CompleteHistory observed) := historyCountable

local instance : Countable (base.toArena.HistoryFrom base.init) := historyCountable

/-- Reuse the existing repeat-or-stop arena and policy. The auxiliary active
payoff is deliberately nonzero; only the terminal payoff one is evaluated. -/
def payoff (history : History) : ℚ :=
  match history.1 with
  | .active => 17
  | .terminal => 1

/-- The existing base payoff has the explicit rational bound one. -/
def payoffExtension : MeasurableHistoryModel.BoundedTerminalPayoffExtension
    observed (MeasurableHistoryModel.discrete observed) where
  payoff := fun _ h => (payoff h : ℝ)
  payoff_measurable := fun _ _ _ => MeasurableSpace.measurableSet_top
  payoff_eq_base := by
    intro _ ⟨state, history⟩ ht
    cases state with
    | active => exact (ht.false false).elim
    | terminal => change ((1 : ℚ) : ℝ) = 1; norm_num
  bound := 1
  norm_payoff_le := by
    intro _ ⟨state, history⟩ ht
    cases state with
    | active => exact (ht.false false).elim
    | terminal => norm_num [payoff]

/-- Reuse the established geometric survival proof for every incoming repeat
history. The coordinate horizon is relative to that retained complete history. -/
theorem survival (offset horizon : ℕ) :
    Arena.noneMass fairHistoryPolicy (activeHistory offset) horizon = (1 / 2 : ℚ≥0) ^ horizon :=
  active_survival_probability offset horizon

/-- Terminal reachability of the actual history trajectory is proved from
the geometric probabilities. No analytic profile or finite-marginal certificate is supplied. -/
theorem ae_reaches (offset : ℕ) :
    ∀ᵐ path ∂historyPath(base.toArena, base.init, fairHistoryPolicy, activeHistory offset),
      ∃ time, base.isTerminal (path time).1 := by
  apply ae_reaches_of_mass_tendsto_zero
  have hcast (horizon : ℕ) :
      (Arena.noneMass fairHistoryPolicy (activeHistory offset) horizon : ENNReal) =
        (1 / 2 : ENNReal) ^ horizon := by
    rw [survival]
    simp [← ENNReal.coe_nnratCast, ENNReal.inv_pow]
  simp_rw [hcast]
  exact ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num)

/-- The general error theorem applies to unbounded-support termination at
every horizon and every retained incoming repeat history. -/
theorem error_bound (offset horizon : ℕ) :
    |(∫ path, payoffExtension.eventualUtility () path
      ∂historyPath(base.toArena, base.init, fairHistoryPolicy, activeHistory offset)) -
      (stoppedExpectedPayoff fairHistoryPolicy (activeHistory offset) horizon payoff : ℝ)| ≤
        ((1 / 2 : ℚ≥0) ^ horizon : ℝ) := by
  have h := estimate_correct payoffExtension fairHistoryPolicy (activeHistory offset)
    () payoff 1 horizon (by norm_num [payoffExtension])
    (fun history ht => (payoffExtension.payoff_eq_base () history ht)) (ae_reaches offset)
  calc
    _ ≤ ((estimate fairHistoryPolicy (activeHistory offset) payoff 1 horizon).2 : ℝ) := h
    _ = _ := by simp only [estimate, one_mul, survival, NNRat.cast_pow]

/-- Every finite horizon retains strictly positive unfinished probability;
this example cannot satisfy a uniform deterministic termination bound. -/
theorem no_finite_bound (offset horizon : ℕ) :
    historyPath(base.toArena, base.init, fairHistoryPolicy, activeHistory offset)
      {path | ¬ base.isTerminal (path horizon).1} ≠ 0 := by
  rw [measure_unfinished, survival]
  simp [← ENNReal.coe_nnratCast]

/-- Budget three tests only horizons zero through two, so tolerance `1/8`
is missed although termination is almost sure. -/
theorem insufficient_budget :
    search fairHistoryPolicy (activeHistory 0) payoff 1 (1 / 8) 3 = none := by
  decide +kernel

/-- One more candidate yields horizon three, center `7/8`, radius `1/8`. -/
theorem successful_budget :
    search fairHistoryPolicy (activeHistory 0) payoff 1 (1 / 8) 4 =
      some (3, 7 / 8, 1 / 8) := by
  decide +kernel

/-- A nonempty incoming history is retained by the same computation. -/
theorem retained_history :
    search fairHistoryPolicy (activeHistory 5) payoff 1 (1 / 8) 4 =
      some (3, 7 / 8, 1 / 8) := by
  decide +kernel

/-- An already terminal history succeeds at horizon zero with its full
payoff and zero radius; zero candidate budget still returns exhaustion. -/
theorem already_terminal :
    search fairHistoryPolicy (terminalHistory 2) payoff 1 (1 / 8) 1 = some (0, 1, 0) ∧
    search fairHistoryPolicy (terminalHistory 2) payoff 1 (1 / 8) 0 = none := by
  decide +kernel

/-- Horizon zero at an active history has center zero and radius one,
despite the deliberately nonzero auxiliary payoff. -/
theorem active_zero : estimate fairHistoryPolicy (activeHistory 0) payoff 1 0 = (0, 1) ∧
    payoff (activeHistory 0) = 17 := by
  decide +kernel

/-- The returned numerical interval contains the actual eventual expectation. -/
theorem successful_budget_correct :
    |(∫ path, payoffExtension.eventualUtility () path
      ∂historyPath(base.toArena, base.init, fairHistoryPolicy, activeHistory 0)) -
      (7 / 8 : ℝ)| ≤ 1 / 8 := by
  have h := search_correct payoffExtension fairHistoryPolicy (activeHistory 0) () payoff
    1 (1 / 8) 4 3 (7 / 8) (1 / 8) (by norm_num [payoffExtension])
    (fun history ht => payoffExtension.payoff_eq_base () history ht)
    (ae_reaches 0) successful_budget
  norm_num at h
  exact h

/-- info: (none, some (3, 7 / 8, 1 / 8), some (0, 1, 0)) -/
#guard_msgs in
#eval
  let render := fun result : Option (ℕ × ℚ × ℚ≥0) =>
    result.map fun (horizon, center, radius) => (horizon, center, (radius : ℚ))
  (render (search fairHistoryPolicy (activeHistory 0) payoff 1 (1 / 8) 3),
    render (search fairHistoryPolicy (activeHistory 5) payoff 1 (1 / 8) 4),
    render (search fairHistoryPolicy (terminalHistory 2) payoff 1 (1 / 8) 1))

/-- Positive tolerance needs no supplied budget. The least horizon is three
at every incoming repeat history, although all finite horizons have survival mass. -/
theorem least_horizon (offset : ℕ) :
    leastHorizon fairHistoryPolicy (activeHistory offset) 1 (1 / 8)
      (by norm_num) (ae_reaches offset) = 3 := by
  rw [leastHorizon_eq_iff]
  constructor
  · norm_num [survival]
  · intro earlier hearlier
    interval_cases earlier <;> norm_num [survival]

/-- Actual unbudgeted output at a nonempty incoming history. The horizon
proof uses exact rational comparisons and the center reduces in the kernel. -/
theorem approximation_retained :
    approximate fairHistoryPolicy (activeHistory 5) payoff 1 (1 / 8)
      (by norm_num) (ae_reaches 5) = (3, 7 / 8, 1 / 8) := by
  rw [approximate, least_horizon]
  decide +kernel

/-- The new correctness entry point certifies the actual eventual integral,
using the returned center and radius rather than a supplied target equality. -/
theorem approximation_integral :
    |(∫ path, payoffExtension.eventualUtility () path
      ∂historyPath(base.toArena, base.init, fairHistoryPolicy, activeHistory 5)) -
      (7 / 8 : ℝ)| ≤ 1 / 8 := by
  have h := approximate_correct payoffExtension fairHistoryPolicy (activeHistory 5) () payoff
    1 (1 / 8) (by norm_num) (by norm_num [payoffExtension])
    (fun history ht => payoffExtension.payoff_eq_base () history ht) (ae_reaches 5)
  erw [approximation_retained] at h
  norm_num at h
  exact h

/-- At the least horizon, budget three excludes the answer and budget four
includes precisely the same tuple as the unbudgeted computation. -/
theorem approximation_budgets :
    search fairHistoryPolicy (activeHistory 5) payoff 1 (1 / 8) 3 = none ∧
    search fairHistoryPolicy (activeHistory 5) payoff 1 (1 / 8) 4 =
      some (approximate fairHistoryPolicy (activeHistory 5) payoff 1 (1 / 8)
        (by norm_num) (ae_reaches 5)) := by
  constructor <;>
    rw [search_eq_approximate fairHistoryPolicy (activeHistory 5) payoff 1 (1 / 8)
      (by norm_num) (ae_reaches 5), approximation_retained] <;> rfl

private theorem terminal_reaches (offset : ℕ) :
    ∀ᵐ path ∂historyPath(base.toArena, base.init, fairHistoryPolicy, terminalHistory offset),
      ∃ time, base.isTerminal (path time).1 := by
  rw [ae_iff]
  apply measure_mono_null (show
    {path : ℕ → History | ¬ ∃ time, base.isTerminal (path time).1} ⊆
      {path | ¬ base.isTerminal (path 0).1} from fun _ hp ht => hp ⟨0, ht⟩)
  erw [measure_unfinished fairHistoryPolicy (terminalHistory offset) 0]
  have hzero : Arena.noneMass fairHistoryPolicy (terminalHistory offset) 0 = 0 := by
    norm_num [Arena.noneMass, Arena.pathMarginal, Arena.stochasticHistoryLawFrom,
      FiniteLaw.eventMass, FiniteLaw.pure, Arena.IsTerminal, terminalHistory, nodeAction]
  rw [hzero]
  simp [← ENNReal.coe_nnratCast]

/-- An already terminal incoming history returns immediately with its full
payoff; the process proof is derived from its actual coordinate-zero law. -/
theorem approximation_terminal :
    approximate fairHistoryPolicy (terminalHistory 2) payoff 1 (1 / 8)
      (by norm_num) (terminal_reaches 2) = (0, 1, 0) := by
  have h : leastHorizon fairHistoryPolicy (terminalHistory 2) 1 (1 / 8)
      (by norm_num) (terminal_reaches 2) = 0 := by
    rw [leastHorizon_eq_iff]
    constructor
    · decide +kernel
    · exact fun _ h => (Nat.not_lt_zero _ h).elim
  rw [approximate, h]
  decide +kernel

/-- Negative and zero reward variants preserve the same arena and observed
information; only the base payoff changes. -/
def rewardObserved (reward : ℚ) : _root_.ExtensiveGame.ObservedGame Unit ℝ :=
  { observed with base :=
    { Examples.ObservedMeasurableKernelAlmostSureOutcomeBoundary.base with
      payoff := fun _ _ => (reward : ℝ) } }

local instance (reward : ℚ) :
    (state : (rewardObserved reward).base.State) →
      Decidable ((rewardObserved reward).base.isTerminal state) := terminalDecidable

local instance (reward : ℚ) : Countable (CompleteHistory (rewardObserved reward)) :=
  historyCountable

/-- A rational constant reward has the explicit absolute-value terminal
bound. All measurability is in the discrete history model. -/
def rewardExtension (reward : ℚ) : MeasurableHistoryModel.BoundedTerminalPayoffExtension
    (rewardObserved reward) (MeasurableHistoryModel.discrete (rewardObserved reward)) where
  payoff := fun _ _ => (reward : ℝ)
  payoff_measurable := fun _ _ _ => MeasurableSpace.measurableSet_top
  payoff_eq_base := fun _ _ _ => rfl
  bound := ⟨((|reward| : ℚ) : ℝ), by exact_mod_cast abs_nonneg reward⟩
  norm_payoff_le := fun _ _ _ => by
    change ‖(reward : ℝ)‖ ≤ ((|reward| : ℚ) : ℝ)
    simp only [Rat.cast_abs, Real.norm_eq_abs, le_refl]

/-- Signed reward computation uses the actual stopped payoff and retains
the same least horizon; unfinished payoff is still zero. -/
theorem approximation_negative :
    approximate fairHistoryPolicy (activeHistory 5) (fun _ => -1) 1 (1 / 8)
      (by norm_num) (ae_reaches 5) = (3, -7 / 8, 1 / 8) := by
  rw [approximate, least_horizon]
  decide +kernel

/-- The signed result approximates the negative variant's original eventual
utility under the actual unchanged execution law. -/
theorem approximation_negative_integral :
    |(∫ path, (rewardExtension (-1)).eventualUtility () path
      ∂historyPath(base.toArena, base.init, fairHistoryPolicy, activeHistory 5)) -
      (-7 / 8 : ℝ)| ≤ 1 / 8 := by
  have h := approximate_correct (rewardExtension (-1)) fairHistoryPolicy (activeHistory 5)
    () (fun _ => -1) 1 (1 / 8) (by norm_num) (by norm_num [rewardExtension]; exact le_rfl)
    (fun _ _ => rfl) (ae_reaches 5)
  erw [approximation_negative] at h
  norm_num at h
  simpa only [sub_neg_eq_add, neg_div] using h

/-- A zero bound and zero terminal reward succeed at horizon zero even
though the current history is active. -/
theorem approximation_zero :
    approximate fairHistoryPolicy (activeHistory 5) (fun _ => 0) 0 (1 / 8)
      (by norm_num) (ae_reaches 5) = (0, 0, 0) := by
  have h : leastHorizon fairHistoryPolicy (activeHistory 5) 0 (1 / 8)
      (by norm_num) (ae_reaches 5) = 0 := by
    rw [leastHorizon_eq_iff]
    simp
  rw [approximate, h]
  decide +kernel

/-- The zero-radius result really certifies the original zero-reward
eventual integral, with a valid zero terminal bound. -/
theorem approximation_zero_integral :
    (∫ path, (rewardExtension 0).eventualUtility () path
      ∂historyPath(base.toArena, base.init, fairHistoryPolicy, activeHistory 5)) = 0 := by
  have h := approximate_correct (rewardExtension 0) fairHistoryPolicy (activeHistory 5)
    () (fun _ => 0) 0 (1 / 8) (by norm_num) (by norm_num [rewardExtension]; exact le_rfl)
    (fun _ _ => rfl) (ae_reaches 5)
  erw [approximation_zero] at h
  simpa using h.1

/-- Repeat until absolute history length three, then stop. Retaining the
incoming history changes the number of additional execution steps. -/
def clockPolicy : base.toArena.StochasticHistoryPolicy base.init := by
  intro current hn
  rcases current with ⟨state, history⟩
  cases state with
  | active => exact FiniteLaw.pure (decide (3 ≤ history.length))
  | terminal => exact (hn ⟨Empty.elim⟩).elim

private theorem clock_reaches (offset : Fin 3) :
    ∀ᵐ path ∂historyPath(base.toArena, base.init, clockPolicy, activeHistory offset),
      ∃ time, base.isTerminal (path time).1 := by
  rw [ae_iff]
  apply measure_mono_null (show
    {path : ℕ → History | ¬ ∃ time, base.isTerminal (path time).1} ⊆
      {path | ¬ base.isTerminal (path 4).1} from fun _ hp ht => hp ⟨4, ht⟩)
  erw [measure_unfinished clockPolicy (activeHistory offset) 4]
  have hzero : Arena.noneMass clockPolicy (activeHistory offset) 4 = 0 := by
    fin_cases offset <;> decide +kernel
  rw [hzero]
  simp [← ENNReal.coe_nnratCast]

/-- Absolute time two requires two more steps, whereas a fresh time-zero
start requires four. The outputs distinguish retaining the prefix from restart. -/
theorem approximation_absolute_time :
    approximate clockPolicy (activeHistory 2) payoff 1 (1 / 8)
      (by norm_num) (clock_reaches 2) = (2, 1, 0) ∧
    approximate clockPolicy (activeHistory 0) payoff 1 (1 / 8)
      (by norm_num) (clock_reaches 0) = (4, 1, 0) := by
  have htwo : leastHorizon clockPolicy (activeHistory 2) 1 (1 / 8)
      (by norm_num) (clock_reaches 2) = 2 := by
    rw [leastHorizon_eq_iff]
    constructor
    · decide +kernel
    · intro earlier hearlier
      interval_cases earlier <;> decide +kernel
  have hzero : leastHorizon clockPolicy (activeHistory 0) 1 (1 / 8)
      (by norm_num) (clock_reaches 0) = 4 := by
    rw [leastHorizon_eq_iff]
    constructor
    · decide +kernel
    · intro earlier hearlier
      interval_cases earlier <;> decide +kernel
  constructor
  · rw [approximate, htwo]; decide +kernel
  · rw [approximate, hzero]; decide +kernel

/-- Zero tolerance keeps the old API: an active geometric process misses
every finite budget, while an already terminal history succeeds at zero. -/
theorem zero_tolerance_budget (budget : ℕ) :
    search fairHistoryPolicy (activeHistory 0) payoff 1 0 budget = none ∧
    search fairHistoryPolicy (terminalHistory 2) payoff 1 0 1 = some (0, 1, 0) := by
  constructor
  · have h : searchHorizon fairHistoryPolicy (activeHistory 0) 1 0 budget = none := by
      rw [searchHorizon_eq_none_iff]
      intro horizon _
      simp [survival]
    simp [search, h]
  · decide +kernel

/-- info: [(3, 7 / 8, 1 / 8), (0, 1, 0), (3, -7 / 8, 1 / 8), (0, 0, 0), (2, 1, 0), (4, 1, 0)] -/
#guard_msgs in
#eval
  let render := fun result : ℕ × ℚ × ℚ≥0 => (result.1, result.2.1, (result.2.2 : ℚ))
  [render (approximate fairHistoryPolicy (activeHistory 5) payoff 1 (1 / 8)
      (by norm_num) (ae_reaches 5)),
    render (approximate fairHistoryPolicy (terminalHistory 2) payoff 1 (1 / 8)
      (by norm_num) (terminal_reaches 2)),
    render (approximate fairHistoryPolicy (activeHistory 5) (fun _ => -1) 1 (1 / 8)
      (by norm_num) (ae_reaches 5)),
    render (approximate fairHistoryPolicy (activeHistory 5) (fun _ => 0) 0 (1 / 8)
      (by norm_num) (ae_reaches 5)),
    render (approximate clockPolicy (activeHistory 2) payoff 1 (1 / 8)
      (by norm_num) (clock_reaches 2)),
    render (approximate clockPolicy (activeHistory 0) payoff 1 (1 / 8)
      (by norm_num) (clock_reaches 0))]

end RepeatOrStop

end Examples.ExtensiveGame.FiniteTruncation
