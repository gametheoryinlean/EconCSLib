/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.Examples.ExtensiveGame.FiniteExecutionIntegral
import EconCSLib.Math.Probability.FiniteLaw.Conditioning

/-!
# Finite conditional continuation

An opt-in prototype for conditioning a finite history distribution and then
continuing the same history policy. `conditionalLaw` computes the posterior
with `FiniteLaw.conditionOnFiber` and binds the existing finite executor;
`conditionalPayoff` computes its exact rational expectation. Impossible
observations return `none`, independently of whether a real payoff is zero.

The joint law retains both the observation-time history and the final history.
The Bayes and commutation theorems concern semantic equality of sparse laws,
including duplicate and zero-weight atoms. Analytic correspondence uses the
actual history-path construction from `FiniteExecutionIntegral` for the same
finite window. No infinite-path utility or off-path belief is supplied here.

These example algorithms and proofs are not promoted to the frozen public API.
-/

open MeasureTheory ProbabilityTheory

namespace Examples.ExtensiveGame.FiniteConditionalContinuation

section Conditioning

variable {α β γ : Type*} [DecidableEq β]

private theorem condition_some_iff (law : FiniteLaw α) (observe : α → β) (y : β) :
    (∃ posterior, law.conditionOnFiber observe y = some posterior) ↔
      law.FiberPossible observe y := by
  rw [← Option.ne_none_iff_exists']
  simp [FiniteLaw.conditionOnFiber, FiniteLaw.FiberPossible]

/-- Bayes' formula for every rational observable, without equality decisions
on histories or a global finite carrier. -/
theorem expectRat_conditionOnFiber (law : FiniteLaw α) (observe : α → β) (y : β)
    (posterior : FiniteLaw α) (hposterior : law.conditionOnFiber observe y = some posterior)
    (value : α → ℚ) :
    posterior.expectRat value =
      law.expectRat (fun x => if observe x = y then value x else 0) /
        (law.eventMass (fun x => decide (observe x = y)) : ℚ) := by
  let atoms := law.atoms.map fun atom =>
    (atom.1, if observe atom.1 = y then atom.2 else 0)
  have htotal : FiniteLaw.totalWeight atoms =
      law.eventMass (fun x => decide (observe x = y)) := by
    simp [atoms, FiniteLaw.totalWeight, FiniteLaw.eventMass, List.map_map, Function.comp_def]
  have hc : FiniteLaw.normalize? atoms = some posterior := by
    change FiniteLaw.normalize? (law.atoms.map fun atom =>
      (atom.1, if decide (observe atom.1 = y) then atom.2 else 0)) = some posterior at hposterior
    simpa [atoms] using hposterior
  unfold FiniteLaw.normalize? at hc
  split at hc
  · simp at hc
  · rename_i hnonzero
    have hp : FiniteLaw.normalize atoms hnonzero = posterior := Option.some.inj hc
    rw [← hp]
    simp only [FiniteLaw.expectRat, FiniteLaw.normalize, List.map_map,
      Function.comp_def, htotal]
    dsimp only [atoms]
    simp only [List.map_map, Function.comp_def]
    generalize law.eventMass (fun x => decide (observe x = y)) = mass
    induction law.atoms with
    | nil => simp
    | cons atom atoms ih =>
      simp only [List.map_cons, List.sum_cons, ih, add_div]
      congr 1
      split <;> simp [div_mul_eq_mul_div]

private theorem joint_fst (law : FiniteLaw α) (next : α → FiniteLaw γ) :
    ((law.bind fun x => (next x).map (fun z => (x, z))).map Prod.fst).Equivalent law := by
  intro value
  change FiniteLaw.expectRat _ value = law.expectRat value
  simp [FiniteLaw.expectRat_map, FiniteLaw.expectRat_bind, Function.comp_def]

/-- Conditioning the first coordinate of a joint law agrees with continuing
from the posterior, for every rational observable of both coordinates. -/
theorem condition_joint (law : FiniteLaw α) (next : α → FiniteLaw γ)
    (observe : α → β) (y : β) (posterior : FiniteLaw α)
    (hposterior : law.conditionOnFiber observe y = some posterior) :
    ∃ jointPosterior,
      (law.bind fun x => (next x).map (fun z => (x, z))).conditionOnFiber
        (fun pair => observe pair.1) y = some jointPosterior ∧
      jointPosterior.Equivalent
        (posterior.bind fun x => (next x).map (fun z => (x, z))) := by
  let joint := law.bind fun x => (next x).map (fun z => (x, z))
  have hmass : joint.eventMass (fun pair => decide (observe pair.1 = y)) =
      law.eventMass (fun x => decide (observe x = y)) := by
    simpa [FiniteLaw.eventMass_map, Function.comp_def] using
      (joint_fst law next).eventMass (fun x => decide (observe x = y))
  have hpossible := (condition_some_iff law observe y).mp ⟨posterior, hposterior⟩
  have hjpossible : joint.FiberPossible (fun pair => observe pair.1) y := by
    simpa only [FiniteLaw.FiberPossible, hmass] using hpossible
  obtain ⟨jointPosterior, hj⟩ := (condition_some_iff joint _ y).mpr hjpossible
  refine ⟨jointPosterior, hj, ?_⟩
  intro value
  change jointPosterior.expectRat value = FiniteLaw.expectRat _ value
  rw [expectRat_conditionOnFiber joint _ y jointPosterior hj value,
    FiniteLaw.expectRat_bind posterior, expectRat_conditionOnFiber law observe y posterior hposterior,
    hmass]
  congr 1
  simp only [joint, FiniteLaw.expectRat_bind, FiniteLaw.expectRat_map,
    Function.comp_def]
  apply congrArg law.expectRat
  funext x
  by_cases h : observe x = y <;> simp [h]

end Conditioning

section HistoryExecution

variable {A : Arena} {start : A.State} {Y : Type*} [DecidableEq Y]
variable [(state : A.State) → Decidable (A.IsTerminal state)]

/-- Compute a finite posterior and continue the same policy from each complete
history. The retained history contains the original clock and action memory. -/
def conditionalLaw (policy : A.StochasticHistoryPolicy start)
    (prior : FiniteLaw (A.HistoryFrom start)) (observe : A.HistoryFrom start → Y)
    (y : Y) (horizon : ℕ) : Option (FiniteLaw (A.HistoryFrom start)) :=
  (prior.conditionOnFiber observe y).map fun posterior =>
    posterior.bind fun history => A.stochasticHistoryLawFrom policy history horizon

/-- Exact rational finite-window payoff; `none` means an impossible observation. -/
def conditionalPayoff (policy : A.StochasticHistoryPolicy start)
    (prior : FiniteLaw (A.HistoryFrom start)) (observe : A.HistoryFrom start → Y)
    (y : Y) (horizon : ℕ) (payoff : A.HistoryFrom start → ℚ) : Option ℚ :=
  (conditionalLaw policy prior observe y horizon).map fun law => law.expectRat payoff

/-- The joint finite execution records the actual observation-time history
and the final history, using the existing additive-horizon composition. -/
def jointExecution (policy : A.StochasticHistoryPolicy start)
    (current : A.HistoryFrom start) (time horizon : ℕ) :
    FiniteLaw (A.HistoryFrom start × A.HistoryFrom start) :=
  (A.stochasticHistoryLawFrom policy current time).bind fun history =>
    (A.stochasticHistoryLawFrom policy history horizon).map fun final => (history, final)

/-- Forgetting only the recorded middle history recovers the original
executor at `time + horizon`, with no restart or new coherence assumption. -/
theorem jointExecution_snd (policy : A.StochasticHistoryPolicy start)
    (current : A.HistoryFrom start) (time horizon : ℕ) :
    (jointExecution policy current time horizon).map Prod.snd =
      A.stochasticHistoryLawFrom policy current (time + horizon) := by
  rw [jointExecution, FiniteLaw.map_bind, A.stochasticHistoryLawFrom_add]
  congr 1
  funext history
  simpa only [FiniteLaw.map_comp, Function.comp_def] using
    FiniteLaw.map_id (A.stochasticHistoryLawFrom policy history horizon)

/-- Exactly zero observation probability is the only failure mode. -/
theorem conditionalPayoff_eq_none_iff (policy : A.StochasticHistoryPolicy start)
    (prior : FiniteLaw (A.HistoryFrom start)) (observe : A.HistoryFrom start → Y)
    (y : Y) (horizon : ℕ) (payoff : A.HistoryFrom start → ℚ) :
    conditionalPayoff policy prior observe y horizon payoff = none ↔
      prior.eventMass (fun history => decide (observe history = y)) = 0 := by
  simp [conditionalPayoff, conditionalLaw, FiniteLaw.conditionOnFiber]

/-- Bayes-weighted continuation expectation, including all histories consistent
with the observation, rather than one representative endpoint. -/
theorem conditionalPayoff_bayes (policy : A.StochasticHistoryPolicy start)
    (prior : FiniteLaw (A.HistoryFrom start)) (observe : A.HistoryFrom start → Y)
    (y : Y) (horizon : ℕ) (payoff : A.HistoryFrom start → ℚ)
    (hpossible : prior.FiberPossible observe y) :
    conditionalPayoff policy prior observe y horizon payoff = some
      (prior.expectRat (fun history => if observe history = y then
        (A.stochasticHistoryLawFrom policy history horizon).expectRat payoff else 0) /
        (prior.eventMass (fun history => decide (observe history = y)) : ℚ)) := by
  obtain ⟨posterior, hp⟩ := (condition_some_iff prior observe y).mpr hpossible
  simp only [conditionalPayoff, conditionalLaw, hp, Option.map_some,
    FiniteLaw.expectRat_bind]
  rw [expectRat_conditionOnFiber prior observe y posterior hp]

/-- Every positive observation computes a normalized continuation law. The
posterior and normalization proof are constructed from the input law. -/
theorem conditionalLaw_exists (policy : A.StochasticHistoryPolicy start)
    (prior : FiniteLaw (A.HistoryFrom start)) (observe : A.HistoryFrom start → Y)
    (y : Y) (horizon : ℕ) (hpossible : prior.FiberPossible observe y) :
    ∃ result, conditionalLaw policy prior observe y horizon = some result ∧
      FiniteLaw.totalWeight result.atoms = 1 := by
  obtain ⟨posterior, hp⟩ := (condition_some_iff prior observe y).mpr hpossible
  refine ⟨posterior.bind (fun history => A.stochasticHistoryLawFrom policy history horizon),
    ?_, FiniteLaw.totalWeight_atoms _⟩
  simp [conditionalLaw, hp]

/-- Conditioning the actual joint finite execution and projecting its final
history agrees with posterior continuation, including absence at zero mass. -/
theorem conditionalLaw_joint (policy : A.StochasticHistoryPolicy start)
    (current : A.HistoryFrom start) (time horizon : ℕ)
    (observe : A.HistoryFrom start → Y) (y : Y) :
    Option.Rel FiniteLaw.Equivalent
      (((jointExecution policy current time horizon).conditionOnFiber
        (fun pair => observe pair.1) y).map (fun law => law.map Prod.snd))
      (conditionalLaw policy (A.stochasticHistoryLawFrom policy current time)
        observe y horizon) := by
  let prior := A.stochasticHistoryLawFrom policy current time
  let next := fun history => A.stochasticHistoryLawFrom policy history horizon
  cases hp : prior.conditionOnFiber observe y with
  | none =>
    have hzero : prior.eventMass (fun history => decide (observe history = y)) = 0 := by
      simpa [FiniteLaw.conditionOnFiber] using hp
    have hmass := (joint_fst prior next).eventMass
      (fun history => decide (observe history = y))
    have hjzero : (jointExecution policy current time horizon).eventMass
        (fun pair => decide (observe pair.1 = y)) = 0 := by
      simpa [FiniteLaw.eventMass_map, Function.comp_def, hzero] using hmass
    have hj : (jointExecution policy current time horizon).conditionOnFiber
        (fun pair => observe pair.1) y = none := by
      simpa [FiniteLaw.conditionOnFiber] using hjzero
    simp only [hj, Option.map_none, conditionalLaw, show
      A.stochasticHistoryLawFrom policy current time = prior from rfl, hp]
    exact Option.Rel.none
  | some posterior =>
    obtain ⟨jointPosterior, hj, heq⟩ := condition_joint prior next observe y posterior hp
    change (jointExecution policy current time horizon).conditionOnFiber
      (fun pair => observe pair.1) y = some jointPosterior at hj
    simp only [hj, Option.map_some, conditionalLaw, show
      A.stochasticHistoryLawFrom policy current time = prior from rfl, hp]
    apply Option.Rel.some
    have h := heq.map Prod.snd
    rw [FiniteLaw.map_bind] at h
    simp only [FiniteLaw.map_comp] at h
    change (jointPosterior.map Prod.snd).Equivalent
      (posterior.bind fun history => (next history).map id) at h
    simpa only [FiniteLaw.map_id] using h

end HistoryExecution

section AnalyticWindow

variable {A : Arena} {start : A.State} {Y : Type*} [DecidableEq Y]
variable [(state : A.State) → Decidable (A.IsTerminal state)]

local instance : MeasurableSpace (A.HistoryFrom start) := ⊤
local instance : (history : (A.historyKernelArena start).State) →
    Decidable (IsEmpty ((A.historyKernelArena start).Action history)) :=
  fun history => inferInstanceAs (Decidable (A.IsTerminal history.1))

local macro "historyPath(" arena:term ", " start:term ", " policy:term ", " current:term ")" :
    term =>
  `(Kernel.traj
    ((Arena.StochasticHistoryPolicy.toKernelPolicy $policy).toMeasurable.pathStepKernel
      (Arena.historyKernelArena $arena $start).toMeasurable_measurableSet_terminalSet)
    0 (fun _ => $current))

local notation "μ[" atoms "]" =>
  List.foldr (fun (atom : _ × ℚ≥0) rest =>
    ((Prod.snd atom : ℚ≥0) : ENNReal) • Measure.dirac (Prod.fst atom) + rest) 0 atoms

/-- The joint finite law evaluates every rational two-coordinate observable
as the actual analytic continuation from the retained middle history.
The inner integral uses J's actual trajectory, not a supplied law. -/
theorem jointExecution_integral (policy : A.StochasticHistoryPolicy start)
    (current : A.HistoryFrom start) (time horizon : ℕ)
    (value : A.HistoryFrom start × A.HistoryFrom start → ℚ) :
    (∫ pair, (value pair : ℝ) ∂μ[(jointExecution policy current time horizon).atoms]) =
      ∫ history, (∫ path, (value (history, path horizon) : ℝ)
        ∂historyPath(A, start, policy, history))
        ∂μ[(A.stochasticHistoryLawFrom policy current time).atoms] := by
  have hinner (history : A.HistoryFrom start) :
      (∫ path, (value (history, path horizon) : ℝ) ∂historyPath(A, start, policy, history)) =
        ((A.stochasticHistoryLawFrom policy history horizon).expectRat
          (fun final => value (history, final)) : ℝ) :=
    FiniteExecutionIntegral.integral_historyPayoff policy history horizon
      (fun final => value (history, final))
  simp_rw [hinner]
  rw [FiniteLawIntegral.integral_eq_expectRat, FiniteLawIntegral.integral_eq_expectRat]
  congr 1
  simp [jointExecution, FiniteLaw.expectRat_bind, FiniteLaw.expectRat_map, Function.comp_def]

/-- A positive observation's computed value is its normalized analytic
finite-window expectation. Both the posterior weighting and the inner
trajectory integrals are proved, with no conditional-evaluation input.
The observation is of the middle history; the payoff sees the final complete
history. This does not evaluate arbitrary infinite-path utilities. -/
theorem conditionalPayoff_analytic (policy : A.StochasticHistoryPolicy start)
    (prior : FiniteLaw (A.HistoryFrom start)) (observe : A.HistoryFrom start → Y)
    (y : Y) (horizon : ℕ) (payoff : A.HistoryFrom start → ℚ)
    (hpossible : prior.FiberPossible observe y) :
    (conditionalPayoff policy prior observe y horizon payoff).map (fun q => (q : ℝ)) =
      some ((∫ history, (if observe history = y then
        (∫ path, (payoff (path horizon) : ℝ) ∂historyPath(A, start, policy, history)) else 0)
        ∂μ[prior.atoms]) /
        (prior.eventMass (fun history => decide (observe history = y)) : ℝ)) := by
  rw [conditionalPayoff_bayes policy prior observe y horizon payoff hpossible]
  have hinner (history : A.HistoryFrom start) :
      (∫ path, (payoff (path horizon) : ℝ) ∂historyPath(A, start, policy, history)) =
        ((A.stochasticHistoryLawFrom policy history horizon).expectRat payoff : ℝ) :=
    FiniteExecutionIntegral.integral_historyPayoff policy history horizon payoff
  simp_rw [hinner]
  have hcast : (fun history : A.HistoryFrom start =>
      if observe history = y then
        ((A.stochasticHistoryLawFrom policy history horizon).expectRat payoff : ℝ) else 0) =
      (fun history => ((if observe history = y then
        (A.stochasticHistoryLawFrom policy history horizon).expectRat payoff else 0 : ℚ) : ℝ)) := by
    funext history
    split <;> simp
  rw [hcast, FiniteLawIntegral.integral_eq_expectRat]
  simp

/-- The computed optional value is exactly the integral against the computed
joint posterior. This constructs the finite conditional-evaluation certificate
for both positive and zero-mass observations; no target equality is an input. -/
theorem conditionalPayoff_joint_integral (policy : A.StochasticHistoryPolicy start)
    (current : A.HistoryFrom start) (time horizon : ℕ)
    (observe : A.HistoryFrom start → Y) (y : Y) (payoff : A.HistoryFrom start → ℚ) :
    (conditionalPayoff policy (A.stochasticHistoryLawFrom policy current time)
      observe y horizon payoff).map (fun q => (q : ℝ)) =
      ((jointExecution policy current time horizon).conditionOnFiber
        (fun pair => observe pair.1) y).map
        (fun law => ∫ pair, (payoff pair.2 : ℝ) ∂μ[law.atoms]) := by
  have h := conditionalLaw_joint policy current time horizon observe y
  cases hj : (jointExecution policy current time horizon).conditionOnFiber
      (fun pair => observe pair.1) y with
  | none =>
    simp only [hj, Option.map_none] at h
    cases hc : conditionalLaw policy (A.stochasticHistoryLawFrom policy current time)
        observe y horizon with
    | none => simp [conditionalPayoff, hc]
    | some law => rw [hc] at h; cases h
  | some posterior =>
    simp only [hj, Option.map_some] at h
    cases hc : conditionalLaw policy (A.stochasticHistoryLawFrom policy current time)
        observe y horizon with
    | none => rw [hc] at h; cases h
    | some law =>
      rw [hc] at h
      cases h with
      | some heq =>
        have hex := heq payoff
        change (posterior.map Prod.snd).expectRat payoff = law.expectRat payoff at hex
        simp only [FiniteLaw.expectRat_map, Function.comp_def] at hex
        simp [conditionalPayoff, hc, FiniteLawIntegral.integral_eq_expectRat, hex]

section Regression

/-- The two hidden routes merge at `middle`; payoffs are terminal state data. -/
inductive World
  | entry | fork | middle | good | bad
  deriving DecidableEq

/-- A nonempty incoming prefix precedes a nonuniform three-way chance move. -/
def arena : Arena where
  State := World
  Action
    | .entry => Unit
    | .fork => Fin 3
    | .middle => Fin 2
    | .good | .bad => PEmpty
  next
    | .entry, _ => .fork
    | .fork, _ => .middle
    | .middle, action => if action = 0 then .good else .bad

local instance terminalDecidable : (state : arena.State) → Decidable (arena.IsTerminal state)
  | .entry => isFalse (fun h => h.false ())
  | .fork => isFalse (fun h => h.false (0 : Fin 3))
  | .middle => isFalse (fun h => h.false (0 : Fin 2))
  | .good | .bad => isTrue ⟨PEmpty.elim⟩

/-- Read the most recent fork occurrence, retaining the action after merging. -/
def route {start : arena.State} : {state : arena.State} → arena.History start state → Fin 3
  | _, .nil => 0
  | _, @Arena.History.snoc _ _ state previous action =>
    match state with
    | .fork => action
    | .entry | .middle => route previous
    | .good | .bad => PEmpty.elim action

/-- Duplicate and zero-weight occurrences are deliberately retained. -/
def forkLaw : FiniteLaw (Fin 3) where
  atoms := [(0, 1 / 4), (1, 1 / 4), (0, 1 / 4), (2, 1 / 4), (1, 0)]
  normalized := by norm_num

/-- The middle decision uses both its retained fork action and absolute
history length. Removing the incoming entry step changes the selected action. -/
def policy {start : arena.State} : arena.StochasticHistoryPolicy start := by
  intro history hnonterminal
  rcases history with ⟨state, history⟩
  cases state with
  | entry => exact FiniteLaw.pure ()
  | fork => exact forkLaw
  | middle =>
    exact FiniteLaw.pure
      (if history.length = 2 ∧ route history = 0 then (0 : Fin 2) else (1 : Fin 2))
  | good | bad => exact False.elim (hnonterminal ⟨PEmpty.elim⟩)

/-- Observation zero cannot distinguish routes zero and one; two is impossible. -/
def observe {start : arena.State} (history : arena.HistoryFrom start) : Fin 3 :=
  if route history.2 = 2 then 1 else 0

/-- Rational terminal payoff; the nonterminal value prevents accidental zero tests. -/
def payoff {start : arena.State} (history : arena.HistoryFrom start) : ℚ :=
  match history.1 with
  | .good => 6
  | .bad => -3
  | _ => 17

/-- The actual current history has already traversed the entry step. -/
def current : arena.HistoryFrom .entry := ⟨.fork, Arena.History.nil.snoc ()⟩

/-- The first hidden history at the shared middle state. -/
def leftHistory : arena.HistoryFrom .entry := ⟨.middle, current.2.snoc (0 : Fin 3)⟩

/-- The second hidden history at that same middle state. -/
def rightHistory : arena.HistoryFrom .entry := ⟨.middle, current.2.snoc (1 : Fin 3)⟩

/-- The same compact fork state with no retained incoming history. -/
def fresh : arena.HistoryFrom .fork := ⟨.fork, .nil⟩

/-- Both histories have the same endpoint and observation but produce distinct
continued expected payoffs, so selecting one representative would be incorrect. -/
theorem hidden_routes :
    leftHistory.1 = rightHistory.1 ∧ observe leftHistory = observe rightHistory ∧
      (arena.stochasticHistoryLawFrom policy leftHistory 1).expectRat payoff = 6 ∧
      (arena.stochasticHistoryLawFrom policy rightHistory 1).expectRat payoff = -3 := by
  refine ⟨rfl, ?_⟩
  decide +kernel

/-- A positive observation aggregates duplicate atoms into posterior masses
two thirds and one third, giving `(2/3)6 + (1/3)(-3) = 3`. -/
theorem positive_observation :
    (arena.stochasticHistoryLawFrom policy current 1).eventMass
      (fun history => decide (observe history = 0)) = 3 / 4 ∧
    conditionalPayoff policy (arena.stochasticHistoryLawFrom policy current 1)
      observe 0 1 payoff = some 3 := by
  decide +kernel

/-- The computed posterior contains both hidden histories with their Bayes
weights, and its atom weights sum to one despite duplicates and zero atoms. -/
theorem posterior_weights :
    ((arena.stochasticHistoryLawFrom policy current 1).conditionOnFiber observe 0).map
      (fun law => (law.eventMass (fun history => decide (route history.2 = 0)),
        law.eventMass (fun history => decide (route history.2 = 1)),
        FiniteLaw.totalWeight law.atoms)) = some (2 / 3, 1 / 3, 1) := by
  decide +kernel

/-- Conditioning on an impossible observation fails instead of manufacturing
a posterior or returning a real payoff of zero. -/
theorem zero_observation :
    conditionalPayoff policy (arena.stochasticHistoryLawFrom policy current 1)
      observe 2 1 payoff = none := by
  decide +kernel

/-- A genuine conditional payoff of zero remains present. -/
theorem zero_payoff_present :
    conditionalPayoff policy (arena.stochasticHistoryLawFrom policy current 1)
      observe 0 1 (fun _ => 0) = some 0 := by
  decide +kernel

/-- With no future steps, the middle history's auxiliary payoff is evaluated.
This is a window observable, not an implicit stopped-utility convention. -/
theorem zero_horizon :
    conditionalPayoff policy (arena.stochasticHistoryLawFrom policy current 1)
      observe 0 0 payoff = some 17 := by
  decide +kernel

/-- Resetting the incoming history removes one unit of absolute time and
changes the same conditional computation from three to minus three. -/
theorem clock_offset : current.1 = fresh.1 ∧ current.2.length = 1 ∧ fresh.2.length = 0 ∧
    conditionalPayoff policy (arena.stochasticHistoryLawFrom policy fresh 1)
      observe 0 1 payoff = some (-3) := by
  refine ⟨rfl, ?_⟩
  decide +kernel

/-- The other positive observation selects the third route. -/
theorem other_observation :
    conditionalPayoff policy (arena.stochasticHistoryLawFrom policy current 1)
      observe 1 1 payoff = some (-3) := by
  decide +kernel

/-- Once the hidden routes have terminated, more continuation fuel preserves
their posterior expected payoff and their recorded observation. -/
theorem terminal_continuation :
    conditionalPayoff policy (arena.stochasticHistoryLawFrom policy current 2)
      observe 0 4 payoff = some 3 := by
  decide +kernel

/-- The analytic normalized finite-window integral is exactly three in the
hidden-route regression. Positivity is proved from its computed event mass. -/
theorem analytic_positive :
    (∫ history, (if observe history = 0 then
      (∫ path, (payoff (path 1) : ℝ) ∂historyPath(arena, World.entry, policy, history)) else 0)
      ∂μ[(arena.stochasticHistoryLawFrom policy current 1).atoms]) /
      ((arena.stochasticHistoryLawFrom policy current 1).eventMass
        (fun history => decide (observe history = 0)) : ℝ) = 3 := by
  have hpositive : (arena.stochasticHistoryLawFrom policy current 1).FiberPossible observe 0 := by
    unfold FiniteLaw.FiberPossible
    rw [positive_observation.1]
    norm_num
  have h := conditionalPayoff_analytic policy
    (arena.stochasticHistoryLawFrom policy current 1) observe 0 1 payoff hpositive
  rw [positive_observation.2] at h
  simpa using (Option.some.inj h).symm

/-- info: true -/
#guard_msgs in
#eval conditionalPayoff policy (arena.stochasticHistoryLawFrom policy current 1)
    observe 0 1 payoff == some 3 &&
  conditionalPayoff policy (arena.stochasticHistoryLawFrom policy current 1)
    observe 2 1 payoff == none &&
  conditionalPayoff policy (arena.stochasticHistoryLawFrom policy fresh 1)
    observe 0 1 payoff == some (-3)

end Regression

end AnalyticWindow

end Examples.ExtensiveGame.FiniteConditionalContinuation
