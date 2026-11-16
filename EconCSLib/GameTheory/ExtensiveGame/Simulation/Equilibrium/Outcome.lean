/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Simulation.Presentation.Kernel.ProfileAssembly
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Equilibrium.Outcome — path utility for kernel-valued observed games

The measurable observed-game executor produces a probability measure on
complete infinite state paths. This module adds the economic interpretation
that must remain separate from execution:

* `MeasurableHistoryModel.PathUtility` is an explicitly measurable
  player-indexed real functional on complete state paths;
* `PathUtility.IntegrableAt` records integrability for one profile and initial
  history;
* `expectedUtility` requires that certificate rather than silently using the
  Bochner integral's default value for a non-integrable function;
* `BoundedPathUtility` supplies integrability uniformly for every profile;
* `ProfileAssembly.IsNashAmongIntegrableDeviations` and
  `BoundedPathUtility.IsNashAt` quantify over the constructive player
  deviations from the profile-assembly layer;
* terminal-payoff extensions and `TerminatesBy` provide an explicit safe
  finite-horizon bridge to the base game's terminal payoff;
* `TerminatesAlmostSurely`, `eventualUtility`, and dominated convergence
  support unbounded random termination without inventing an endpoint on
  nonterminating paths.

The generic path-utility layer never reads a terminal payoff implicitly. The
terminal bridges below require a measurable extension plus either an explicit
finite-horizon certificate or almost-sure eventual terminal absorption.
-/

open MeasureTheory ProbabilityTheory

namespace ExtensiveGame.ObservedGame

universe uN uU

variable {N : Type uN} {U : Type uU}
variable {G : ObservedGame N U}

namespace MeasurableHistoryModel

/-- A measurable real utility for every player on complete infinite state
paths of one measurable complete-history model.

The utility belongs to the history model rather than to one presentation, so
different information or realization presentations over the same dynamics
can reuse it. -/
structure PathUtility
    (model : MeasurableHistoryModel G) where
  /-- Player-indexed utility of a complete state path. -/
  utility :
    N → (ℕ → model.toArena.State) → ℝ
  /-- Every player's path utility is measurable. -/
  utility_measurable :
    ∀ i, Measurable (utility i)

/-- A uniformly bounded measurable path utility. The nonnegative bound is
strong enough to prove integrability under every profile path probability
measure. -/
structure BoundedPathUtility
    (model : MeasurableHistoryModel G)
    extends PathUtility model where
  /-- Uniform bound on absolute utility. -/
  bound : NNReal
  /-- Pointwise uniform bound for every player and path. -/
  norm_utility_le :
    ∀ (i : N) (path : ℕ → model.toArena.State),
      ‖utility i path‖ ≤ bound

namespace PathUtility

variable
  {model : MeasurableHistoryModel G}
  (evaluation : PathUtility model)

/-- Integrability of every player's path utility under one profile and
initial history. -/
def IntegrableAt
    {presentation : G.MeasurableKernelPresentation model}
    (profile : presentation.KernelBehavioralProfile)
    (initialHistory : CompleteHistory G) :
    Prop :=
  ∀ i,
    Integrable
      (evaluation.utility i)
      (profile.statePathMeasure initialHistory)

/-- Expected utility under one profile path law.

The integrability proof is an explicit argument. Although it is proof
irrelevant computationally, requiring it prevents non-integrable utilities
from being assigned the Bochner integral's conventional fallback value. -/
noncomputable def expectedUtility
    {presentation : G.MeasurableKernelPresentation model}
    (profile : presentation.KernelBehavioralProfile)
    (initialHistory : CompleteHistory G)
    (_hintegrable :
      evaluation.IntegrableAt profile initialHistory)
    (i : N) :
    ℝ :=
  ∫ path, evaluation.utility i path
    ∂profile.statePathMeasure initialHistory

/-- Expected utility does not depend on which proof of integrability is
supplied. -/
theorem expectedUtility_proof_irrel
    {presentation : G.MeasurableKernelPresentation model}
    (profile : presentation.KernelBehavioralProfile)
    (initialHistory : CompleteHistory G)
    (hfirst hsecond :
      evaluation.IntegrableAt profile initialHistory)
    (i : N) :
    evaluation.expectedUtility
        profile initialHistory hfirst i =
      evaluation.expectedUtility
        profile initialHistory hsecond i :=
  rfl

/-- Equal complete state-path laws give equal expected utility. -/
theorem expectedUtility_eq_of_statePathMeasure_eq
    {presentation : G.MeasurableKernelPresentation model}
    (first second : presentation.KernelBehavioralProfile)
    (initialHistory : CompleteHistory G)
    (hfirst :
      evaluation.IntegrableAt first initialHistory)
    (hsecond :
      evaluation.IntegrableAt second initialHistory)
    (hmeasure :
      first.statePathMeasure initialHistory =
        second.statePathMeasure initialHistory)
    (i : N) :
    evaluation.expectedUtility
        first initialHistory hfirst i =
      evaluation.expectedUtility
        second initialHistory hsecond i := by
  unfold expectedUtility
  rw [hmeasure]

/-- Equal compiled event policies give equal expected utility. -/
theorem expectedUtility_eq_of_compiledPolicy_eq
    {presentation : G.MeasurableKernelPresentation model}
    (first second : presentation.KernelBehavioralProfile)
    (initialHistory : CompleteHistory G)
    (hfirst :
      evaluation.IntegrableAt first initialHistory)
    (hsecond :
      evaluation.IntegrableAt second initialHistory)
    (hpolicy :
      first.compiledPolicy = second.compiledPolicy)
    (i : N) :
    evaluation.expectedUtility
        first initialHistory hfirst i =
      evaluation.expectedUtility
        second initialHistory hsecond i := by
  apply
    evaluation.expectedUtility_eq_of_statePathMeasure_eq
      first second initialHistory hfirst hsecond
  unfold
    MeasurableKernelPresentation.KernelBehavioralProfile.statePathMeasure
  rw [hpolicy]

end PathUtility

namespace BoundedPathUtility

variable
  {model : MeasurableHistoryModel G}
  (evaluation :
    MeasurableHistoryModel.BoundedPathUtility model)

/-- A bounded measurable path utility is integrable under every admissible
profile path law. -/
theorem integrableAt
    {presentation : G.MeasurableKernelPresentation model}
    (profile : presentation.KernelBehavioralProfile)
    (initialHistory : CompleteHistory G) :
    evaluation.toPathUtility.IntegrableAt
      profile initialHistory := by
  intro i
  let μ := profile.statePathMeasure initialHistory
  letI : IsProbabilityMeasure μ := by
    dsimp only [μ]
    unfold
      MeasurableKernelPresentation.KernelBehavioralProfile.statePathMeasure
    infer_instance
  apply
    (integrable_const (evaluation.bound : ℝ)).mono
      (evaluation.utility_measurable i).aestronglyMeasurable
  exact
    Filter.Eventually.of_forall fun path => by
      simpa using evaluation.norm_utility_le i path

/-- Expected bounded utility with its canonical integrability certificate. -/
noncomputable def expectedUtility
    {presentation : G.MeasurableKernelPresentation model}
    (profile : presentation.KernelBehavioralProfile)
    (initialHistory : CompleteHistory G)
    (i : N) :
    ℝ :=
  evaluation.toPathUtility.expectedUtility
    profile initialHistory
    (evaluation.integrableAt profile initialHistory)
    i

/-- Equal state-path laws give equal bounded expected utility. -/
theorem expectedUtility_eq_of_statePathMeasure_eq
    {presentation : G.MeasurableKernelPresentation model}
    (first second : presentation.KernelBehavioralProfile)
    (initialHistory : CompleteHistory G)
    (hmeasure :
      first.statePathMeasure initialHistory =
        second.statePathMeasure initialHistory)
    (i : N) :
    evaluation.expectedUtility first initialHistory i =
      evaluation.expectedUtility second initialHistory i :=
  PathUtility.expectedUtility_eq_of_statePathMeasure_eq
    (evaluation := evaluation.toPathUtility)
    first second initialHistory
    (evaluation.integrableAt first initialHistory)
    (evaluation.integrableAt second initialHistory)
    hmeasure i

/-- Equal compiled event policies give equal bounded expected utility. -/
theorem expectedUtility_eq_of_compiledPolicy_eq
    {presentation : G.MeasurableKernelPresentation model}
    (first second : presentation.KernelBehavioralProfile)
    (initialHistory : CompleteHistory G)
    (hpolicy :
      first.compiledPolicy = second.compiledPolicy)
    (i : N) :
    evaluation.expectedUtility first initialHistory i =
      evaluation.expectedUtility second initialHistory i :=
  PathUtility.expectedUtility_eq_of_compiledPolicy_eq
    (evaluation := evaluation.toPathUtility)
    first second initialHistory
    (evaluation.integrableAt first initialHistory)
    (evaluation.integrableAt second initialHistory)
    hpolicy i

end BoundedPathUtility

/-- A measurable real-valued extension of the base game's terminal payoff.

Only equality at terminal complete histories is semantically required. Values
away from terminal histories are auxiliary measurable extension data and are
never read by `stoppedPathUtility`. -/
structure TerminalPayoffExtension
    {N : Type uN}
    (G : ObservedGame N ℝ)
    (model : MeasurableHistoryModel G) where
  /-- Measurable extension of each player's terminal payoff. -/
  payoff :
    N → model.toArena.State → ℝ
  /-- The extension is measurable on complete histories. -/
  payoff_measurable :
    ∀ i, Measurable (payoff i)
  /-- At terminal histories the extension is exactly the base payoff. -/
  payoff_eq_base :
    ∀ (i : N) (history : model.toArena.State),
      G.base.isTerminal history.1 →
        payoff i history = G.base.payoff history.1 i

/-- A uniformly bounded terminal-payoff extension. The bound is required only
at terminal histories because stopped utility is zero elsewhere. -/
structure BoundedTerminalPayoffExtension
    {N : Type uN}
    (G : ObservedGame N ℝ)
    (model : MeasurableHistoryModel G)
    extends TerminalPayoffExtension G model where
  /-- Uniform terminal payoff bound. -/
  bound : NNReal
  /-- Every actual terminal payoff lies within the bound. -/
  norm_payoff_le :
    ∀ (i : N) (history : model.toArena.State),
      G.base.isTerminal history.1 →
        ‖payoff i history‖ ≤ bound

namespace TerminalPayoffExtension

variable
  {N : Type uN}
  {G : ObservedGame N ℝ}
  {model : MeasurableHistoryModel G}
  (terminalPayoff : TerminalPayoffExtension G model)

section StoppedUtility

/-- Terminal payoff observed at one finite event horizon, with explicit value
zero when the path has not terminated by that coordinate. Computation requires
an executable terminal decision and the supplied path and payoff; selecting a
real payoff does not provide arbitrary real evaluation or integration. -/
def stoppedUtility
    [(state : G.base.State) → Decidable (G.base.isTerminal state)]
    (terminalPayoff : TerminalPayoffExtension G model)
    (horizon : ℕ)
    (i : N)
    (path : ℕ → model.toArena.State) :
    ℝ :=
  if G.base.isTerminal (path horizon).1 then
    terminalPayoff.payoff i (path horizon)
  else
    0

/-- Finite-horizon stopped utility is measurable. -/
theorem stoppedUtility_measurable
    [(state : G.base.State) → Decidable (G.base.isTerminal state)]
    (horizon : ℕ)
    (i : N) :
    Measurable (terminalPayoff.stoppedUtility horizon i) := by
  classical
  apply Measurable.ite
  · exact
      model.toArena_terminalSet_measurable.preimage
        (measurable_pi_apply horizon)
  · exact
      (terminalPayoff.payoff_measurable i).comp
        (measurable_pi_apply horizon)
  · exact measurable_const

/-- The stopped utility as a reusable measurable path evaluation. -/
def stoppedPathUtility
    [(state : G.base.State) → Decidable (G.base.isTerminal state)]
    (terminalPayoff : TerminalPayoffExtension G model)
    (horizon : ℕ) :
    PathUtility model where
  utility := fun i =>
    terminalPayoff.stoppedUtility horizon i
  utility_measurable := by
    intro i
    exact terminalPayoff.stoppedUtility_measurable horizon i

/-- At a terminal horizon coordinate, stopped utility is exactly the base
game's terminal payoff. -/
theorem stoppedUtility_eq_base
    [(state : G.base.State) → Decidable (G.base.isTerminal state)]
    (horizon : ℕ)
    (i : N)
    (path : ℕ → model.toArena.State)
    (hterminal :
      G.base.isTerminal (path horizon).1) :
    terminalPayoff.stoppedUtility horizon i path =
      G.base.payoff (path horizon).1 i := by
  rw [
    stoppedUtility,
    if_pos hterminal,
    terminalPayoff.payoff_eq_base i
      (path horizon) hterminal]

/-- Before termination, stopped utility is explicitly zero. -/
theorem stoppedUtility_eq_zero
    [(state : G.base.State) → Decidable (G.base.isTerminal state)]
    (horizon : ℕ)
    (i : N)
    (path : ℕ → model.toArena.State)
    (hnonterminal :
      ¬ G.base.isTerminal (path horizon).1) :
    terminalPayoff.stoppedUtility horizon i path = 0 := by
  rw [stoppedUtility, if_neg hnonterminal]

end StoppedUtility

end TerminalPayoffExtension

namespace BoundedTerminalPayoffExtension

variable
  {N : Type uN}
  {G : ObservedGame N ℝ}
  {model : MeasurableHistoryModel G}
  (terminalPayoff :
    BoundedTerminalPayoffExtension G model)

/-- The bounded finite-horizon terminal payoff as a bounded path utility. -/
def stoppedBoundedPathUtility
    [(state : G.base.State) → Decidable (G.base.isTerminal state)]
    (terminalPayoff :
      BoundedTerminalPayoffExtension G model)
    (horizon : ℕ) :
    BoundedPathUtility model where
  toPathUtility :=
    terminalPayoff.toTerminalPayoffExtension.stoppedPathUtility
      horizon
  bound := terminalPayoff.bound
  norm_utility_le := by
    intro i path
    by_cases hterminal :
        G.base.isTerminal (path horizon).1
    · change
        ‖terminalPayoff.toTerminalPayoffExtension.stoppedUtility
            horizon i path‖ ≤
          terminalPayoff.bound
      unfold TerminalPayoffExtension.stoppedUtility
      rw [if_pos hterminal]
      exact
        terminalPayoff.norm_payoff_le
          i (path horizon) hterminal
    · change
        ‖terminalPayoff.toTerminalPayoffExtension.stoppedUtility
            horizon i path‖ ≤
          terminalPayoff.bound
      unfold TerminalPayoffExtension.stoppedUtility
      rw [if_neg hterminal]
      simpa only [norm_zero] using
        terminalPayoff.bound.2

end BoundedTerminalPayoffExtension

end MeasurableHistoryModel

namespace MeasurableKernelPresentation

namespace ProfileAssembly

variable
  {model : MeasurableHistoryModel G}
  {presentation : G.MeasurableKernelPresentation model}
  (assembly : presentation.ProfileAssembly)

/-- Nash optimality among constructive deviations whose resulting path
utilities are integrable.

This predicate is appropriate for an unbounded path utility. A deviation is
compared exactly when its expected utility is mathematically defined by the
explicit integrability certificate. -/
def IsNashAmongIntegrableDeviations
    (evaluation : model.PathUtility)
    (initialHistory : CompleteHistory G)
    (profile : assembly.PlayerKernelProfile)
    (hprofile :
      evaluation.IntegrableAt
        (assembly.toKernelBehavioralProfile profile)
        initialHistory) :
    Prop :=
  ∀ (who : N)
    (strategy : assembly.PlayerStrategy who)
    (hdeviated :
      evaluation.IntegrableAt
        (assembly.toKernelBehavioralProfile
          (PlayerKernelProfile.deviate
            (assembly := assembly)
            profile who strategy))
        initialHistory),
    evaluation.expectedUtility
        (assembly.toKernelBehavioralProfile
          (PlayerKernelProfile.deviate
            (assembly := assembly)
            profile who strategy))
        initialHistory hdeviated who ≤
      evaluation.expectedUtility
        (assembly.toKernelBehavioralProfile profile)
        initialHistory hprofile who

/-- Splitting and reassembling a generic profile preserves every bounded
expected path utility exactly. -/
theorem split_reassembly_expectedUtility
    (evaluation : model.BoundedPathUtility)
    (profile : presentation.KernelBehavioralProfile)
    (initialHistory : CompleteHistory G)
    (i : N) :
    evaluation.expectedUtility
        (assembly.toKernelBehavioralProfile
          (PlayerKernelProfile.ofKernelBehavioralProfile
            (assembly := assembly) profile))
        initialHistory i =
      evaluation.expectedUtility
        profile initialHistory i := by
  apply evaluation.expectedUtility_eq_of_compiledPolicy_eq
  exact
    assembly.toKernelBehavioralProfile_ofKernelBehavioralProfile_compiledPolicy
      profile

end ProfileAssembly

end MeasurableKernelPresentation

namespace MeasurableHistoryModel
namespace BoundedPathUtility

variable
  {model : MeasurableHistoryModel G}
  (evaluation :
    MeasurableHistoryModel.BoundedPathUtility model)

/-- Constructive Nash optimality for a bounded path utility. Every certified
player strategy is compared because boundedness supplies integrability for
both the original and deviated profiles. -/
def IsNashAt
    {presentation : G.MeasurableKernelPresentation model}
    (assembly : presentation.ProfileAssembly)
    (initialHistory : CompleteHistory G)
    (profile : assembly.PlayerKernelProfile) :
    Prop :=
  ∀ (who : N)
    (strategy : assembly.PlayerStrategy who),
    evaluation.expectedUtility
        (assembly.toKernelBehavioralProfile
          (MeasurableKernelPresentation.ProfileAssembly.PlayerKernelProfile.deviate
            (assembly := assembly)
            profile who strategy))
        initialHistory who ≤
      evaluation.expectedUtility
        (assembly.toKernelBehavioralProfile profile)
        initialHistory who

end BoundedPathUtility
end MeasurableHistoryModel

namespace MeasurableKernelPresentation
namespace KernelBehavioralProfile

variable
  {model : MeasurableHistoryModel G}
  {presentation : G.MeasurableKernelPresentation model}

/-- One profile terminates by a fixed event coordinate when its state path is
terminal there almost surely. -/
def TerminatesBy
    (profile : presentation.KernelBehavioralProfile)
    (initialHistory : CompleteHistory G)
    (horizon : ℕ) :
    Prop :=
  ∀ᵐ path ∂profile.statePathMeasure initialHistory,
    G.base.isTerminal (path horizon).1

end KernelBehavioralProfile
end MeasurableKernelPresentation

namespace MeasurableHistoryModel
namespace TerminalPayoffExtension

variable
  {N : Type uN}
  {G : ObservedGame N ℝ}
  {model : MeasurableHistoryModel G}
  (terminalPayoff : TerminalPayoffExtension G model)

/-- Under an explicit finite-horizon termination certificate, expected
stopped utility equals the expectation of the measurable terminal-payoff
extension at that coordinate. -/
theorem expectedUtility_eq_integral_payoff_of_terminatesBy
    [(state : G.base.State) → Decidable (G.base.isTerminal state)]
    {presentation : G.MeasurableKernelPresentation model}
    (profile : presentation.KernelBehavioralProfile)
    (initialHistory : CompleteHistory G)
    (horizon : ℕ)
    (hintegrable :
      (terminalPayoff.stoppedPathUtility horizon).IntegrableAt
        profile initialHistory)
    (hterminates :
      profile.TerminatesBy initialHistory horizon)
    (i : N) :
    (terminalPayoff.stoppedPathUtility horizon).expectedUtility
        profile initialHistory hintegrable i =
      ∫ path,
        terminalPayoff.payoff i (path horizon)
        ∂profile.statePathMeasure initialHistory := by
  unfold PathUtility.expectedUtility
  apply integral_congr_ae
  filter_upwards [hterminates] with path hterminal
  change
    terminalPayoff.stoppedUtility horizon i path =
      terminalPayoff.payoff i (path horizon)
  unfold stoppedUtility
  rw [if_pos hterminal]

end TerminalPayoffExtension
end MeasurableHistoryModel

namespace MeasurableHistoryModel
namespace BoundedTerminalPayoffExtension

variable
  {N : Type uN}
  {G : ObservedGame N ℝ}
  {model : MeasurableHistoryModel G}
  (terminalPayoff :
    BoundedTerminalPayoffExtension G model)

/-- For a bounded terminal-payoff extension and a fixed-horizon termination
certificate, expected stopped utility is the terminal-payoff integral against
the matching one-coordinate state law. -/
theorem expectedUtility_eq_integral_stateCoordinate_of_terminatesBy
    [(state : G.base.State) → Decidable (G.base.isTerminal state)]
    {presentation : G.MeasurableKernelPresentation model}
    (profile : presentation.KernelBehavioralProfile)
    (initialHistory : CompleteHistory G)
    (horizon : ℕ)
    (hterminates :
      profile.TerminatesBy initialHistory horizon)
    (i : N) :
    (terminalPayoff.stoppedBoundedPathUtility horizon).expectedUtility
        profile initialHistory i =
      ∫ history,
        terminalPayoff.payoff i history
        ∂profile.compiledPolicy.stateCoordinateMeasure
          model.toArena_terminalSet_measurable
          initialHistory horizon := by
  unfold BoundedPathUtility.expectedUtility
  change
    (terminalPayoff.toTerminalPayoffExtension.stoppedPathUtility horizon).expectedUtility
        profile initialHistory
        ((terminalPayoff.stoppedBoundedPathUtility horizon).integrableAt
          profile initialHistory)
        i =
      _
  rw [
    TerminalPayoffExtension.expectedUtility_eq_integral_payoff_of_terminatesBy
      terminalPayoff.toTerminalPayoffExtension
      profile initialHistory horizon
      ((terminalPayoff.stoppedBoundedPathUtility horizon).integrableAt
        profile initialHistory)
      hterminates i]
  change
    (∫ path,
      terminalPayoff.payoff i (path horizon)
      ∂profile.statePathMeasure initialHistory) =
      ∫ history,
        terminalPayoff.payoff i history
        ∂(profile.statePathMeasure initialHistory).map
          (fun path => path horizon)
  symm
  exact
    integral_map
      (measurable_pi_apply horizon).aemeasurable
      (terminalPayoff.payoff_measurable i).aestronglyMeasurable

end BoundedTerminalPayoffExtension
end MeasurableHistoryModel

namespace MeasurableKernelPresentation
namespace KernelBehavioralProfile

variable
  {N : Type uN}
  {G : ObservedGame N ℝ}
  {model : MeasurableHistoryModel G}
  {presentation : G.MeasurableKernelPresentation model}

/-- Every admitted profile generates a probability measure on complete state
paths. -/
instance statePathMeasure_isProbability
    (profile : presentation.KernelBehavioralProfile)
    (initialHistory : CompleteHistory G) :
    IsProbabilityMeasure
      (profile.statePathMeasure initialHistory) := by
  unfold statePathMeasure
  infer_instance

/-- A state path eventually reaches a terminal history and remains at that
same terminal history forever. This combines finite termination with the
terminal absorption needed to identify one unambiguous eventual payoff. -/
def EventuallyAbsorbsAtTerminal
    (path : ℕ → model.toArena.State) :
    Prop :=
  ∃ hit : ℕ,
    G.base.isTerminal (path hit).1 ∧
      ∀ later : ℕ, hit ≤ later →
        path later = path hit

/-- Almost-sure eventual terminal absorption under one profile path law.

Unlike `TerminatesBy`, the terminal time may have unbounded support. The
predicate explicitly includes eventual constancy, so no arbitrary endpoint
is selected on a path that merely visits a terminal state and then leaves. -/
def TerminatesAlmostSurely
    (profile : presentation.KernelBehavioralProfile)
    (initialHistory : CompleteHistory G) :
    Prop :=
  ∀ᵐ path ∂profile.statePathMeasure initialHistory,
    EventuallyAbsorbsAtTerminal
      (G := G) (model := model) path

/-- A weaker almost-sure reachability certificate: some finite coordinate is
terminal, without yet asserting what the executor does afterwards. -/
def ReachesTerminalAlmostSurely
    (profile : presentation.KernelBehavioralProfile)
    (initialHistory : CompleteHistory G) :
    Prop :=
  ∀ᵐ path ∂profile.statePathMeasure initialHistory,
    ∃ hit : ℕ, G.base.isTerminal (path hit).1

/-- Paths that are still nonterminal at one event coordinate. -/
def UnfinishedAt
    (horizon : ℕ) :
    Set (ℕ → model.toArena.State) :=
  {path | ¬ G.base.isTerminal (path horizon).1}

/-- Probability mass still outside the terminal set at one event
coordinate. -/
noncomputable def unfinishedMass
    (profile : presentation.KernelBehavioralProfile)
    (initialHistory : CompleteHistory G)
    (horizon : ℕ) :
    ENNReal :=
  profile.statePathMeasure initialHistory
    (UnfinishedAt (G := G) (model := model) horizon)

/-- The unfinished event is measurable at every coordinate. -/
theorem unfinishedAt_measurableSet
    (horizon : ℕ) :
    MeasurableSet
      (UnfinishedAt (G := G) (model := model) horizon) := by
  exact
    (model.toArena_terminalSet_measurable.preimage
      (measurable_pi_apply horizon)).compl

/-- Fixed-horizon termination is equivalent to zero unfinished mass at that
coordinate. -/
theorem terminatesBy_iff_unfinishedMass_eq_zero
    (profile : presentation.KernelBehavioralProfile)
    (initialHistory : CompleteHistory G)
    (horizon : ℕ) :
    profile.TerminatesBy initialHistory horizon ↔
      profile.unfinishedMass initialHistory horizon = 0 := by
  unfold TerminatesBy unfinishedMass UnfinishedAt
  exact MeasureTheory.ae_iff

/-- Vanishing unfinished mass implies almost-sure finite terminal
reachability.

No monotonicity premise is needed: a path that never reaches a terminal
history belongs to every unfinished event, so its mass is bounded by every
term of any sequence converging to zero. -/
theorem reachesTerminalAlmostSurely_of_unfinishedMass_tendsto_zero
    (profile : presentation.KernelBehavioralProfile)
    (initialHistory : CompleteHistory G)
    (hmass :
      Filter.Tendsto
        (profile.unfinishedMass initialHistory)
        Filter.atTop
        (nhds 0)) :
    profile.ReachesTerminalAlmostSurely initialHistory := by
  unfold ReachesTerminalAlmostSurely
  rw [MeasureTheory.ae_iff]
  have hle :
      ∀ horizon,
        profile.statePathMeasure initialHistory
            {path |
              ¬ ∃ hit : ℕ,
                G.base.isTerminal (path hit).1} ≤
          profile.unfinishedMass initialHistory horizon := by
    intro horizon
    unfold unfinishedMass
    apply measure_mono
    intro path hnever
    change ¬ G.base.isTerminal (path horizon).1
    intro hterminal
    exact hnever ⟨horizon, hterminal⟩
  exact
    bot_unique
      (ge_of_tendsto hmass
        (Filter.Eventually.of_forall hle))

/-- In a countable discrete history presentation, almost-sure reachability
upgrades to almost-sure terminal absorption.

The proof uses the executor's terminal-aware step kernel. Event-carrier
countability and measurable singletons make the pathwise equality events
measurable; state countability is derived from the event carrier, while state
singletons are already supplied by `MeasurableHistoryModel`. These are not
assumptions about the economic game's horizon. -/
theorem terminatesAlmostSurely_of_reachesTerminalAlmostSurely
    (profile : presentation.KernelBehavioralProfile)
    (initialHistory : CompleteHistory G)
    [Countable model.toArena.PathEvent]
    [MeasurableSingletonClass model.toArena.PathEvent]
    (hreaches :
      profile.ReachesTerminalAlmostSurely initialHistory) :
    profile.TerminatesAlmostSurely initialHistory := by
  have habsorbing :
      ∀ᵐ path ∂profile.statePathMeasure initialHistory,
        ∀ time,
          IsEmpty (model.toArena.Action (path time)) →
            path (time + 1) = path time := by
    unfold statePathMeasure
    exact
      profile.compiledPolicy.statePathMeasure_terminal_absorbing_of_countable
        model.toArena_terminalSet_measurable
        initialHistory
  filter_upwards [hreaches, habsorbing] with path hreach habsorb
  rcases hreach with ⟨hit, hterminal⟩
  refine ⟨hit, hterminal, ?_⟩
  intro later hlater
  obtain ⟨offset, rfl⟩ := Nat.exists_eq_add_of_le hlater
  clear hlater
  induction offset with
  | zero =>
      rfl
  | succ offset ih =>
      have hterminalOffset :
          G.base.isTerminal (path (hit + offset)).1 := by
        rw [ih]
        exact hterminal
      calc
        path (hit + offset.succ) =
            path ((hit + offset) + 1) := by
              rw [Nat.add_succ]
        _ = path (hit + offset) :=
          habsorb (hit + offset) hterminalOffset
        _ = path hit := ih

end KernelBehavioralProfile
end MeasurableKernelPresentation

namespace MeasurableHistoryModel
namespace BoundedTerminalPayoffExtension

variable
  {N : Type uN}
  {G : ObservedGame N ℝ}
  {model : MeasurableHistoryModel G}
  (terminalPayoff :
    BoundedTerminalPayoffExtension G model)

/-- Eventual terminal payoff, with explicit value zero on paths that do not
eventually absorb at one terminal history. -/
noncomputable def eventualUtility
    (i : N)
    (path : ℕ → model.toArena.State) :
    ℝ := by
  classical
  exact
    if h :
        MeasurableKernelPresentation.KernelBehavioralProfile.EventuallyAbsorbsAtTerminal
          (G := G) (model := model) path then
      terminalPayoff.payoff i (path (Nat.find h))
    else
      0

section StoppedConvergence

/-- On an eventually terminal-absorbing path, fixed-horizon stopped utility
is eventually equal to the eventual terminal payoff. -/
theorem stoppedUtility_eventuallyEq_eventualUtility
    [(state : G.base.State) → Decidable (G.base.isTerminal state)]
    (i : N)
    (path : ℕ → model.toArena.State)
    (habsorbs :
      MeasurableKernelPresentation.KernelBehavioralProfile.EventuallyAbsorbsAtTerminal
        (G := G) (model := model) path) :
    (fun horizon =>
      terminalPayoff.toTerminalPayoffExtension.stoppedUtility
        horizon i path) =ᶠ[Filter.atTop]
      fun _ => terminalPayoff.eventualUtility i path := by
  classical
  -- Select the same classical least hit as `eventualUtility`; this choice is
  -- confined to the convergence proof, not the bounded evaluator.
  letI (state : G.base.State) : Decidable (G.base.isTerminal state) :=
    Classical.propDecidable _
  let hit := Nat.find habsorbs
  have hspec := Nat.find_spec habsorbs
  refine Filter.eventually_atTop.2 ⟨hit, ?_⟩
  intro horizon hhorizon
  have hstate :
      path horizon = path hit :=
    hspec.2 horizon hhorizon
  have hterminal :
      G.base.isTerminal (path horizon).1 := by
    rw [hstate]
    exact hspec.1
  dsimp only [TerminalPayoffExtension.stoppedUtility, eventualUtility]
  rw [if_pos hterminal, dif_pos habsorbs]
  dsimp only [hit] at hstate
  exact congrArg (terminalPayoff.payoff i) hstate

/-- Fixed-horizon stopped utility converges on every eventually
terminal-absorbing path. -/
theorem stoppedUtility_tendsto_eventualUtility
    [(state : G.base.State) → Decidable (G.base.isTerminal state)]
    (i : N)
    (path : ℕ → model.toArena.State)
    (habsorbs :
      MeasurableKernelPresentation.KernelBehavioralProfile.EventuallyAbsorbsAtTerminal
        (G := G) (model := model) path) :
    Filter.Tendsto
      (fun horizon =>
        terminalPayoff.toTerminalPayoffExtension.stoppedUtility
          horizon i path)
      Filter.atTop
      (nhds (terminalPayoff.eventualUtility i path)) := by
  apply Filter.Tendsto.congr'
    (terminalPayoff.stoppedUtility_eventuallyEq_eventualUtility
      i path habsorbs).symm
  exact tendsto_const_nhds

/-- Under almost-sure terminal absorption, stopped utility converges almost
everywhere to eventual terminal utility. -/
theorem stoppedUtility_tendsto_eventualUtility_ae
    [(state : G.base.State) → Decidable (G.base.isTerminal state)]
    {presentation : G.MeasurableKernelPresentation model}
    (profile : presentation.KernelBehavioralProfile)
    (initialHistory : CompleteHistory G)
    (hterminates :
      profile.TerminatesAlmostSurely initialHistory)
    (i : N) :
    ∀ᵐ path ∂profile.statePathMeasure initialHistory,
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

end StoppedConvergence

/-- Eventual terminal utility is almost-everywhere strongly measurable under
an almost-sure terminal-absorption certificate. -/
theorem eventualUtility_aestronglyMeasurable
    {presentation : G.MeasurableKernelPresentation model}
    (profile : presentation.KernelBehavioralProfile)
    (initialHistory : CompleteHistory G)
    (hterminates :
      profile.TerminatesAlmostSurely initialHistory)
    (i : N) :
    AEStronglyMeasurable
      (terminalPayoff.eventualUtility i)
      (profile.statePathMeasure initialHistory) := by
  classical
  exact
    aestronglyMeasurable_of_tendsto_ae
      Filter.atTop
      (fun horizon =>
        (terminalPayoff.toTerminalPayoffExtension.stoppedUtility_measurable
          horizon i).aestronglyMeasurable)
      (terminalPayoff.stoppedUtility_tendsto_eventualUtility_ae
        profile initialHistory hterminates i)

/-- Eventual terminal utility is uniformly bounded, including its explicit
zero value on nonterminating paths. -/
theorem norm_eventualUtility_le
    (i : N)
    (path : ℕ → model.toArena.State) :
    ‖terminalPayoff.eventualUtility i path‖ ≤
      terminalPayoff.bound := by
  classical
  by_cases habsorbs :
      MeasurableKernelPresentation.KernelBehavioralProfile.EventuallyAbsorbsAtTerminal
        (G := G) (model := model) path
  · rw [eventualUtility, dif_pos habsorbs]
    exact
      terminalPayoff.norm_payoff_le
        i (path (Nat.find habsorbs))
        (Nat.find_spec habsorbs).1
  · rw [eventualUtility, dif_neg habsorbs]
    simpa only [norm_zero] using terminalPayoff.bound.2

/-- Bounded eventual terminal utility is integrable under every
almost-surely terminal-absorbing profile path law. -/
theorem eventualUtility_integrable
    {presentation : G.MeasurableKernelPresentation model}
    (profile : presentation.KernelBehavioralProfile)
    (initialHistory : CompleteHistory G)
    (hterminates :
      profile.TerminatesAlmostSurely initialHistory)
    (i : N) :
    Integrable
      (terminalPayoff.eventualUtility i)
      (profile.statePathMeasure initialHistory) := by
  classical
  apply
    (integrable_const (terminalPayoff.bound : ℝ)).mono
      (terminalPayoff.eventualUtility_aestronglyMeasurable
        profile initialHistory hterminates i)
  exact Filter.Eventually.of_forall fun path => by
    simpa using terminalPayoff.norm_eventualUtility_le i path

/-- Expected eventual terminal utility under an almost-sure terminal-
absorption certificate. -/
noncomputable def expectedEventualUtility
    {presentation : G.MeasurableKernelPresentation model}
    (profile : presentation.KernelBehavioralProfile)
    (initialHistory : CompleteHistory G)
    (_hterminates :
      profile.TerminatesAlmostSurely initialHistory)
    (i : N) :
    ℝ :=
  ∫ path, terminalPayoff.eventualUtility i path
    ∂profile.statePathMeasure initialHistory

/-- For bounded terminal payoff, expected fixed-horizon stopped utility
converges to expected eventual terminal utility under almost-sure terminal
absorption. -/
theorem expectedUtility_tendsto_expectedEventualUtility
    [(state : G.base.State) → Decidable (G.base.isTerminal state)]
    {presentation : G.MeasurableKernelPresentation model}
    (profile : presentation.KernelBehavioralProfile)
    (initialHistory : CompleteHistory G)
    (hterminates :
      profile.TerminatesAlmostSurely initialHistory)
    (i : N) :
    Filter.Tendsto
      (fun horizon =>
        (terminalPayoff.stoppedBoundedPathUtility horizon).expectedUtility
          profile initialHistory i)
      Filter.atTop
      (nhds
        (terminalPayoff.expectedEventualUtility
          profile initialHistory hterminates i)) := by
  unfold
    BoundedPathUtility.expectedUtility
    PathUtility.expectedUtility
    expectedEventualUtility
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
      terminalPayoff.stoppedUtility_tendsto_eventualUtility_ae
        profile initialHistory hterminates i

end BoundedTerminalPayoffExtension
end MeasurableHistoryModel

end ExtensiveGame.ObservedGame
