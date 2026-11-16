/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.MeasureTheory.Measure.Map
import EconCSLib.GameTheory.ExtensiveGame.Simulation.Equilibrium.Outcome
import EconCSLib.Examples.ExtensiveGame.FiniteTruncation
import Lean.Elab.Command

/-!
# Evidence for the EFG library computability review

This standalone research file supplies two bounded pieces of evidence.
`mapEmbedding` compiles and equals the original measure pushforward when the
map is a measurable embedding. It consumes an existing measure and does not
construct that input measure or apply to every merely measurable map.
`no_finite_prefix_determines_value` proves a zero/one finite-prefix obstruction
for the original EFG `eventualUtility`, instantiated in the existing
repeat-or-stop game. It excludes a total finite-query numerical evaluator;
it does not formalize a general Lean-program noncomputability theorem.

Run from the repository root with:
`lake env lean docs/research/efg-computability/LibraryFeasibility.lean`.
The file is outside library and example aggregates; it adds no EFG API.
-/

open MeasureTheory

namespace LibraryComputabilityProbe

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- Push forward a supplied measure along a measurable embedding using executable data fields. -/
def mapEmbedding (μ : Measure α) (f : α → β) (hf : MeasurableEmbedding f) : Measure β := by
  let outer : OuterMeasure β := {
    measureOf := fun s => μ (f ⁻¹' s)
    empty := by simp
    mono := fun h => measure_mono (Set.preimage_mono h)
    iUnion_nat := fun sets _ => by simpa using measure_iUnion_le (fun n => f ⁻¹' sets n)
  }
  have hout : (μ.map f).toOuterMeasure = outer := by
    ext s
    exact hf.map_apply μ s
  exact {
    toOuterMeasure := outer
    m_iUnion := by rw [← hout]; exact (μ.map f).m_iUnion
    trim_le := by rw [← hout]; exact (μ.map f).trim_le
  }

/-- The executable construction is exactly Mathlib's pushforward, including its outer measure. -/
theorem mapEmbedding_eq (μ : Measure α) (f : α → β) (hf : MeasurableEmbedding f) :
    mapEmbedding μ f hf = μ.map f := by
  apply Measure.ext
  intro s hs
  exact (hf.map_apply μ s).symm

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  if Lean.isNoncomputable env ``mapEmbedding then
    throwError "mapEmbedding is noncomputable"
  else logInfo "mapEmbedding compiles: Measure output alone is not an impossibility criterion"

end LibraryComputabilityProbe

open ExtensiveGame.ObservedGame

namespace LibraryComputabilityProbe

variable {N : Type*} {G : ExtensiveGame.ObservedGame N ℝ}
variable {model : MeasurableHistoryModel G}
variable (extension : MeasurableHistoryModel.BoundedTerminalPayoffExtension G model)
variable (player : N) (active terminal : model.toArena.State)
variable (hactive : ¬ G.base.isTerminal active.1)
variable (hterminal : G.base.isTerminal terminal.1)
variable (hpayoff : extension.payoff player terminal = 1)

/-- Same active history forever: it never absorbs at a terminal history. -/
def neverPath {α : Type*} (active : α) : ℕ → α := fun _ => active

/-- An arbitrary raw path that switches to a fixed terminal history after a finite prefix. -/
def latePath {α : Type*} (active terminal : α) (horizon : ℕ) : ℕ → α :=
  fun time => if time < horizon then active else terminal

include hactive in
/-- The original total utility is zero on the constant nonterminal path. -/
theorem never_value : extension.eventualUtility player (neverPath active) = 0 := by
  classical
  have hn : ¬ MeasurableKernelPresentation.KernelBehavioralProfile.EventuallyAbsorbsAtTerminal
      (G := G) (model := model) (neverPath active) := by
    rintro ⟨hit, hh, _⟩
    exact hactive hh
  simp [MeasurableHistoryModel.BoundedTerminalPayoffExtension.eventualUtility, hn]

include hactive hterminal hpayoff in
/-- The original total utility is one when the path eventually stays at the selected terminal. -/
theorem late_value (horizon : ℕ) :
    extension.eventualUtility player (latePath active terminal horizon) = 1 := by
  classical
  have ha : MeasurableKernelPresentation.KernelBehavioralProfile.EventuallyAbsorbsAtTerminal
      (G := G) (model := model) (latePath active terminal horizon) := by
    refine ⟨horizon, ?_, ?_⟩
    · simpa [latePath] using hterminal
    · intro later hlater
      simp [latePath, Nat.not_lt.mpr hlater]
  have hh := (Nat.find_spec ha).1
  have hge : horizon ≤ Nat.find ha := by
    by_contra hn
    have hlt : Nat.find ha < horizon := Nat.lt_of_not_ge hn
    have hb : (latePath active terminal horizon (Nat.find ha)) = active := by
      exact if_pos hlt
    rw [hb] at hh
    exact hactive hh
  simp only [MeasurableHistoryModel.BoundedTerminalPayoffExtension.eventualUtility, dif_pos ha]
  change extension.payoff player (latePath active terminal horizon (Nat.find ha)) = 1
  rw [show latePath active terminal horizon (Nat.find ha) = terminal from
    if_neg (Nat.not_lt.mpr hge)]
  exact hpayoff

include hactive hterminal hpayoff in
/-- At the nonabsorbing path, no finite prefix determines even whether the value is zero or one. -/
theorem no_finite_prefix_determines_value (horizon : ℕ) :
    (∀ time < horizon, latePath active terminal horizon time = neverPath active time) ∧
    extension.eventualUtility player (neverPath active) = 0 ∧
    extension.eventualUtility player (latePath active terminal horizon) = 1 := by
  refine ⟨?_, never_value extension player active hactive,
    late_value extension player active terminal hactive hterminal hpayoff horizon⟩
  intro time ht
  simp [latePath, neverPath, ht]

/-- The hypotheses occur in the existing repeat-or-stop EFG; this is not vacuous. -/
theorem repeatOrStop_prefixWitness (horizon : ℕ) :
    let ext := Examples.ExtensiveGame.FiniteTruncation.RepeatOrStop.payoffExtension
    let active := Examples.ObservedMeasurableKernelAlmostSureOutcomeBoundary.activeHistory 0
    let terminal := Examples.ObservedMeasurableKernelAlmostSureOutcomeBoundary.terminalHistory 0
    (∀ time < horizon, latePath active terminal horizon time = neverPath active time) ∧
    ext.eventualUtility () (neverPath active) = 0 ∧
    ext.eventualUtility () (latePath active terminal horizon) = 1 := by
  apply no_finite_prefix_determines_value
  · exact Examples.ObservedMeasurableKernelAlmostSureOutcomeBoundary.activeHistory_nonterminal 0
  · exact Examples.ObservedMeasurableKernelAlmostSureOutcomeBoundary.terminalHistory_terminal 0
  · norm_num [Examples.ExtensiveGame.FiniteTruncation.RepeatOrStop.payoffExtension,
      Examples.ExtensiveGame.FiniteTruncation.RepeatOrStop.payoff]

end LibraryComputabilityProbe

#print axioms LibraryComputabilityProbe.mapEmbedding_eq
#print axioms LibraryComputabilityProbe.no_finite_prefix_determines_value
#print axioms LibraryComputabilityProbe.repeatOrStop_prefixWitness
