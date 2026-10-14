/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Execution.CompletePlay
import EconCSLib.GameTheory.ExtensiveGame.Execution.Objective
import EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Morphism.Core
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Payoff-free complete-path probability semantics

This module owns the representation-independent probability law on complete,
occurrence-sensitive history paths.  `CompletePathLawSemantics` is based only
on `ControlledObservedGame`: it mentions no payoff, PMF, countability
assumption, local Markov kernel, or particular strategy formalism.

Every stored law is certified to be a probability measure and to satisfy the
canonical terminal-absorbing complete-play predicate almost surely.  Local
execution or chance-kernel coherence is deliberately orthogonal and is
expressed by `RealizesExecution` or `ExecutionCoherent`.

The carrier is a family of lawful path measures and caller-supplied bounded
coordinate laws, one family for each starting history. Every bounded law is
certified equal to the corresponding path coordinate. The carrier does not by
itself assert that different roots are versions of one joint causal process.
Restart, conditioning, and cross-root coherence require an additional named
certificate.

Same-game strategy realization and cross-game functional realization are
separate structures.  A cross-game realization records measurable history and
path maps and exact pushforward equality.  Source deviation mapping, reverse
target-deviation coverage, and strategy-space isomorphism remain distinct.
-/

open MeasureTheory ProbabilityTheory

namespace ExtensiveGame.ControlledObservedGame

universe uN uStrategy uOutcome

variable {N : Type uN}

/-! ## Maximum lawful probability semantics -/

/-- Probability semantics on complete occurrence-sensitive history paths.

The legality field uses `Arena.IsCompletePlayPathFrom`, which already states
the initial-coordinate, one-legal-step, and terminal-absorption laws. -/
structure CompletePathLawSemantics
    (G : ControlledObservedGame N)
    [MeasurableSpace G.base.History] where
  /-- One strategy carrier per player. -/
  Strategy : N → Type uStrategy
  /-- Complete-path law from every current absolute history. -/
  pathLaw :
    (profile : ∀ i, Strategy i) →
      G.base.History →
        Measure (ℕ → G.base.History)
  /-- Every complete-path law has total mass one. -/
  pathLaw_isProbability :
    ∀ (profile : ∀ i, Strategy i)
      (current : G.base.History),
      IsProbabilityMeasure (pathLaw profile current)
  /-- Almost every generated path is a canonical legal complete play. -/
  pathLaw_ae_legal :
    ∀ (profile : ∀ i, Strategy i)
      (current : G.base.History),
      ∀ᵐ path ∂pathLaw profile current,
        G.base.toArena.IsCompletePlayPathFrom current path
  /-- Caller-supplied bounded coordinate laws.  Keeping these as data avoids
  manufacturing `Measure.map` values in an executable declaration. -/
  boundedCompleteHistoryLaw :
    (profile : ∀ i, Strategy i) →
      G.base.History → ℕ → Measure G.base.History
  /-- Every supplied bounded law is the corresponding coordinate marginal of
  the complete path law. -/
  boundedCompleteHistoryLaw_eq_map :
    ∀ (profile : ∀ i, Strategy i)
      (current : G.base.History) (time : ℕ),
      boundedCompleteHistoryLaw profile current time =
        (pathLaw profile current).map (fun path => path time)

namespace CompletePathLawSemantics

variable {G : ControlledObservedGame N}
  [MeasurableSpace G.base.History]

/-- Profiles for one complete-path semantic model. -/
abbrev Profile (S : G.CompletePathLawSemantics) :=
  ∀ i, S.Strategy i

/-- The probability certificate stored by a semantic model is available as a
local typeclass instance. -/
instance instPathLawIsProbability
    (S : G.CompletePathLawSemantics)
    (profile : S.Profile)
    (current : G.base.History) :
    IsProbabilityMeasure (S.pathLaw profile current) :=
  S.pathLaw_isProbability profile current

/-- Equality of complete-path probability laws at one current history. -/
def CompletePathLawEquivalentAt
    (S T : G.CompletePathLawSemantics)
    (source : S.Profile) (target : T.Profile)
    (current : G.base.History) : Prop :=
  S.pathLaw source current =
    T.pathLaw target current

/-- Coordinate evaluation on the history-path space is measurable. -/
theorem measurable_pathCoordinate (time : ℕ) :
    Measurable (fun path : ℕ → G.base.History => path time) :=
  measurable_pi_apply time

/-- Equality of bounded complete-history laws. -/
def BoundedCompleteHistoryLawEquivalentAt
    (S T : G.CompletePathLawSemantics)
    (source : S.Profile) (target : T.Profile)
    (current : G.base.History)
    (time : ℕ) : Prop :=
  S.boundedCompleteHistoryLaw source current time =
    T.boundedCompleteHistoryLaw target current time

/-- Complete-path equality implies every coordinate-history equality. -/
theorem CompletePathLawEquivalentAt.boundedCompleteHistory
    {S T : G.CompletePathLawSemantics}
    {source : S.Profile} {target : T.Profile}
    {current : G.base.History}
    (hpath :
      S.CompletePathLawEquivalentAt
        T source target current)
    (time : ℕ) :
    S.BoundedCompleteHistoryLawEquivalentAt
      T source target current time := by
  unfold BoundedCompleteHistoryLawEquivalentAt
  rw [S.boundedCompleteHistoryLaw_eq_map,
    T.boundedCompleteHistoryLaw_eq_map, hpath]

/-- Bounded history-law equality is preserved by every common measurable
interpretation. -/
theorem BoundedCompleteHistoryLawEquivalentAt.interpreted
    {S T : G.CompletePathLawSemantics}
    {source : S.Profile} {target : T.Profile}
    {current : G.base.History}
    {time : ℕ}
    (hhistory :
      S.BoundedCompleteHistoryLawEquivalentAt
        T source target current time)
    {Outcome : Type uOutcome}
    [MeasurableSpace Outcome]
    (interpret : G.base.History → Outcome)
    (_hinterpret : Measurable interpret) :
    (S.boundedCompleteHistoryLaw source current time).map interpret =
      (T.boundedCompleteHistoryLaw target current time).map interpret := by
  rw [hhistory]

/-! ## Downstream measurable interpretations -/

/-- History-law equality under an arbitrary explicitly measurable history
transform.

No terminality claim is attached to this generic transform. -/
def HistoryTransformLawEquivalentAt
    (S T : G.CompletePathLawSemantics)
    (source : S.Profile) (target : T.Profile)
    (current : G.base.History)
    (time : ℕ)
    (terminalize : G.base.History → G.base.History)
    (_hterminalize : Measurable terminalize) : Prop :=
  (S.boundedCompleteHistoryLaw source current time).map terminalize =
    (T.boundedCompleteHistoryLaw target current time).map terminalize

/-- Terminal-history law equality under an explicitly measurable map whose
codomain carries a proof that every result is terminal. -/
def TerminalHistoryLawEquivalentAt
    (S T : G.CompletePathLawSemantics)
    (source : S.Profile) (target : T.Profile)
    (current : G.base.History)
    (time : ℕ)
    (terminalize :
      G.base.History →
      G.base.toArena.TerminalHistoryFrom G.base.init)
    (_hterminalize : Measurable terminalize) : Prop :=
  (S.boundedCompleteHistoryLaw source current time).map terminalize =
    (T.boundedCompleteHistoryLaw target current time).map terminalize

/-- Outcome-law equality under an explicitly measurable interpretation. -/
def OutcomeLawEquivalentAt
    (S T : G.CompletePathLawSemantics)
    (source : S.Profile) (target : T.Profile)
    (current : G.base.History)
    (time : ℕ)
    {Outcome : Type uOutcome}
    [MeasurableSpace Outcome]
    (outcome : G.base.History → Outcome)
    (_houtcome : Measurable outcome) : Prop :=
  (S.boundedCompleteHistoryLaw source current time).map outcome =
    (T.boundedCompleteHistoryLaw target current time).map outcome

/-- Payoff-law equality is a downstream measurable outcome interpretation. -/
abbrev PayoffLawEquivalentAt
    (S T : G.CompletePathLawSemantics)
    (source : S.Profile) (target : T.Profile)
    (current : G.base.History)
    (time : ℕ)
    {Payoff : Type uOutcome}
    [MeasurableSpace Payoff]
    (payoff : G.base.History → Payoff)
    (hpayoff : Measurable payoff) : Prop :=
  S.OutcomeLawEquivalentAt
    T source target current time payoff hpayoff

/-- Bounded history equality is preserved by an arbitrary measurable history
transform. -/
theorem BoundedCompleteHistoryLawEquivalentAt.historyTransform
    {S T : G.CompletePathLawSemantics}
    {source : S.Profile} {target : T.Profile}
    {current : G.base.History}
    {time : ℕ}
    (hhistory :
      S.BoundedCompleteHistoryLawEquivalentAt
        T source target current time)
    (terminalize : G.base.History → G.base.History)
    (hterminalize : Measurable terminalize) :
    S.HistoryTransformLawEquivalentAt
      T source target current time terminalize hterminalize :=
  hhistory.interpreted terminalize hterminalize

/-- Bounded history equality implies equality after any measurable transform
into the terminal-history subtype. -/
theorem BoundedCompleteHistoryLawEquivalentAt.terminalHistory
    {S T : G.CompletePathLawSemantics}
    {source : S.Profile} {target : T.Profile}
    {current : G.base.History}
    {time : ℕ}
    (hhistory :
      S.BoundedCompleteHistoryLawEquivalentAt
        T source target current time)
    (terminalize :
      G.base.History →
        G.base.toArena.TerminalHistoryFrom G.base.init)
    (hterminalize : Measurable terminalize) :
    S.TerminalHistoryLawEquivalentAt
      T source target current time terminalize hterminalize :=
  hhistory.interpreted terminalize hterminalize

/-- Bounded history equality implies every common measurable outcome-law
equality. -/
theorem BoundedCompleteHistoryLawEquivalentAt.outcome
    {S T : G.CompletePathLawSemantics}
    {source : S.Profile} {target : T.Profile}
    {current : G.base.History}
    {time : ℕ}
    (hhistory :
      S.BoundedCompleteHistoryLawEquivalentAt
        T source target current time)
    {Outcome : Type uOutcome}
    [MeasurableSpace Outcome]
    (outcome : G.base.History → Outcome)
    (houtcome : Measurable outcome) :
    S.OutcomeLawEquivalentAt
      T source target current time outcome houtcome :=
  hhistory.interpreted outcome houtcome

/-- Equality of outcome laws gives equality of arbitrary integrals.

This theorem deliberately does not call the integral an expected utility. -/
theorem OutcomeLawEquivalentAt.integral_eq
    {S T : G.CompletePathLawSemantics}
    {source : S.Profile} {target : T.Profile}
    {current : G.base.History}
    {time : ℕ}
    {Outcome : Type uOutcome}
    [MeasurableSpace Outcome]
    {outcome : G.base.History → Outcome}
    {houtcome : Measurable outcome}
    (hlaw :
      S.OutcomeLawEquivalentAt
        T source target current time outcome houtcome)
    (integrand : Outcome → ℝ) :
    ∫ value,
        integrand value ∂
          (S.boundedCompleteHistoryLaw
            source current time).map outcome =
      ∫ value,
        integrand value ∂
          (T.boundedCompleteHistoryLaw
            target current time).map outcome := by
  rw [hlaw]

/-- Integrability transfers to the target because the two outcome laws are
equal; callers need not repeat the same hypothesis. -/
theorem OutcomeLawEquivalentAt.integrable_target
    {S T : G.CompletePathLawSemantics}
    {source : S.Profile} {target : T.Profile}
    {current : G.base.History}
    {time : ℕ}
    {Outcome : Type uOutcome}
    [MeasurableSpace Outcome]
    {outcome : G.base.History → Outcome}
    {houtcome : Measurable outcome}
    (hlaw :
      S.OutcomeLawEquivalentAt
        T source target current time outcome houtcome)
    {utility : Outcome → ℝ}
    (hintegrable :
      Integrable utility
        ((S.boundedCompleteHistoryLaw
          source current time).map outcome)) :
    Integrable utility
      ((T.boundedCompleteHistoryLaw
        target current time).map outcome) := by
  rw [← hlaw]
  exact hintegrable

/-- Expected-utility equality with explicit measurable-utility and
integrability hypotheses.  Target integrability is derived from law equality. -/
theorem OutcomeLawEquivalentAt.expectedUtility
    {S T : G.CompletePathLawSemantics}
    {source : S.Profile} {target : T.Profile}
    {current : G.base.History}
    {time : ℕ}
    {Outcome : Type uOutcome}
    [MeasurableSpace Outcome]
    {outcome : G.base.History → Outcome}
    {houtcome : Measurable outcome}
    (hlaw :
      S.OutcomeLawEquivalentAt
        T source target current time outcome houtcome)
    (utility : Outcome → ℝ)
    (_hutility : Measurable utility)
    (hintegrable :
      Integrable utility
        ((S.boundedCompleteHistoryLaw
          source current time).map outcome)) :
    ∫ value,
        utility value ∂
          (S.boundedCompleteHistoryLaw
            source current time).map outcome =
      ∫ value,
        utility value ∂
          (T.boundedCompleteHistoryLaw
            target current time).map outcome := by
  have _htarget := hlaw.integrable_target hintegrable
  exact hlaw.integral_eq utility

/-! ## Execution coherence outside the maximum carrier -/

/-- A semantic path law realizes a separately supplied execution
implementation exactly. -/
def RealizesExecution
    (S : G.CompletePathLawSemantics)
    (executionLaw :
      S.Profile → G.base.History →
        Measure (ℕ → G.base.History)) : Prop :=
  ∀ profile current,
    S.pathLaw profile current =
      executionLaw profile current

/-- A general external coherence predicate holds for every semantic law.

This accommodates local-kernel, correlated, mediator, or other implementation
certificates without forcing a Markov factorization into the maximum carrier. -/
def ExecutionCoherent
    (S : G.CompletePathLawSemantics)
    (coherence :
      S.Profile → G.base.History →
        Measure (ℕ → G.base.History) → Prop) : Prop :=
  ∀ profile current,
    coherence profile current
      (S.pathLaw profile current)

/-! ## Same-game realization -/

/-- One-way realization between two strategy semantics on the same game. -/
structure CompletePathLawRealization
    (S T : G.CompletePathLawSemantics) where
  /-- Playerwise strategy map. -/
  mapStrategy :
    (i : N) → S.Strategy i → T.Strategy i
  /-- Complete path law is preserved at every profile and history. -/
  pathLaw_eq :
    ∀ (profile : S.Profile)
      (current : G.base.History),
      S.pathLaw profile current =
        T.pathLaw (fun i => mapStrategy i (profile i)) current

/-- Map a complete source profile player by player. -/
def CompletePathLawRealization.mapProfile
    {S T : G.CompletePathLawSemantics}
    (R : S.CompletePathLawRealization T)
    (profile : S.Profile) : T.Profile :=
  fun i => R.mapStrategy i (profile i)

/-- Playerwise realization commutes with unilateral profile update. -/
theorem CompletePathLawRealization.mapProfile_update
    [DecidableEq N]
    {S T : G.CompletePathLawSemantics}
    (R : S.CompletePathLawRealization T)
    (profile : S.Profile) (who : N)
    (deviation : S.Strategy who) :
    R.mapProfile (Function.update profile who deviation) =
      Function.update (R.mapProfile profile) who
        (R.mapStrategy who deviation) := by
  funext i
  by_cases hi : i = who
  · subst i
    simp [CompletePathLawRealization.mapProfile]
  · simp [CompletePathLawRealization.mapProfile, hi]

/-- Reverse target-deviation coverage at one same-game root. -/
def CompletePathLawRealization.TargetDeviationsCoveredAt
    [DecidableEq N]
    {S T : G.CompletePathLawSemantics}
    (R : S.CompletePathLawRealization T)
    (profile : S.Profile)
    (current : G.base.History) : Prop :=
  ∀ (who : N) (targetDeviation : T.Strategy who),
    ∃ sourceDeviation : S.Strategy who,
      T.pathLaw
          (Function.update (R.mapProfile profile)
            who targetDeviation) current =
        S.pathLaw
          (Function.update profile who sourceDeviation)
          current

/-- Strategy-space isomorphism is stronger than one-way realization and
target-deviation coverage. -/
structure CompletePathLawStrategyIso
    (S T : G.CompletePathLawSemantics)
    extends S.CompletePathLawRealization T where
  /-- Each player's strategy map is an equivalence. -/
  strategyEquiv : (i : N) → S.Strategy i ≃ T.Strategy i
  /-- The realization map is the forward strategy equivalence. -/
  mapStrategy_eq :
    ∀ (i : N), toCompletePathLawRealization.mapStrategy i =
      strategyEquiv i

end CompletePathLawSemantics

/-! ## Canonical history/path maps of a strict structural isomorphism -/

namespace Iso

variable {G H : ControlledObservedGame N}

/-- Strict structural isomorphism induces an equivalence of complete
occurrence-sensitive histories. -/
abbrev completeHistoryEquiv (e : G.Iso H) :
    G.base.History ≃ H.base.History :=
  e.historyIso.stateEquiv

/-- Strict structural isomorphism induces the pointwise equivalence of full
history paths.  This is structural data only; probability-law preservation
still requires an explicit semantic certificate. -/
def completePathEquiv (e : G.Iso H) :
    (ℕ → G.base.History) ≃ (ℕ → H.base.History) where
  toFun := fun path time =>
    e.completeHistoryEquiv (path time)
  invFun := fun path time =>
    e.completeHistoryEquiv.symm (path time)
  left_inv := by
    intro path
    funext time
    exact e.completeHistoryEquiv.symm_apply_apply (path time)
  right_inv := by
    intro path
    funext time
    exact e.completeHistoryEquiv.apply_symm_apply (path time)

@[simp]
theorem completePathEquiv_apply
    (e : G.Iso H) (path : ℕ → G.base.History)
    (time : ℕ) :
    e.completePathEquiv path time =
      e.completeHistoryEquiv (path time) :=
  rfl

end Iso

/-! ## Cross-game functional realization -/

/-- Functional realization of complete path laws across two different EFG
representations.

The measurable history/path maps and pushforward law are explicit.  The target
current history is exactly the image of the source current history. -/
structure CrossGameCompletePathLawRealization
    {G H : ControlledObservedGame N}
    [MeasurableSpace G.base.History]
    [MeasurableSpace H.base.History]
    (S : G.CompletePathLawSemantics)
    (T : H.CompletePathLawSemantics) where
  /-- Playerwise strategy map. -/
  mapStrategy :
    (i : N) → S.Strategy i → T.Strategy i
  /-- Map source complete histories to target complete histories. -/
  mapHistory : G.base.History → H.base.History
  /-- The history map is measurable. -/
  mapHistory_measurable : Measurable mapHistory
  /-- Map complete source paths to complete target paths. -/
  mapPath :
    (ℕ → G.base.History) → (ℕ → H.base.History)
  /-- The complete-path map is measurable. -/
  mapPath_measurable : Measurable mapPath
  /-- The path map is the coordinatewise history map. -/
  mapPath_apply :
    ∀ path time,
      mapPath path time = mapHistory (path time)
  /-- Source law pushforward is the target law at the corresponding current
  history. -/
  pathLaw_map_eq :
    ∀ (profile : S.Profile)
      (current : G.base.History),
      (S.pathLaw profile current).map mapPath =
        T.pathLaw
          (fun i => mapStrategy i (profile i))
          (mapHistory current)

namespace CrossGameCompletePathLawRealization

variable {G H : ControlledObservedGame N}
  [MeasurableSpace G.base.History]
  [MeasurableSpace H.base.History]
  {S : G.CompletePathLawSemantics}
  {T : H.CompletePathLawSemantics}

/-- Map a complete source profile player by player. -/
def mapProfile
    (R : CrossGameCompletePathLawRealization S T)
    (profile : S.Profile) : T.Profile :=
  fun i => R.mapStrategy i (profile i)

/-- Cross-game playerwise strategy mapping commutes with unilateral update. -/
theorem mapProfile_update
    [DecidableEq N]
    (R : CrossGameCompletePathLawRealization S T)
    (profile : S.Profile) (who : N)
    (deviation : S.Strategy who) :
    R.mapProfile (Function.update profile who deviation) =
      Function.update (R.mapProfile profile) who
        (R.mapStrategy who deviation) := by
  funext i
  by_cases hi : i = who
  · subst i
    simp [mapProfile]
  · simp [mapProfile, hi]

/-- Reverse target-deviation coverage is an additional cross-game property,
not a consequence of mapping source deviations. -/
def TargetDeviationsCoveredAt
    [DecidableEq N]
    (R : CrossGameCompletePathLawRealization S T)
    (profile : S.Profile)
    (current : G.base.History) : Prop :=
  ∀ (who : N) (targetDeviation : T.Strategy who),
    ∃ sourceDeviation : S.Strategy who,
      T.pathLaw
          (Function.update (R.mapProfile profile)
            who targetDeviation)
          (R.mapHistory current) =
        (S.pathLaw
          (Function.update profile who sourceDeviation)
          current).map R.mapPath

end CrossGameCompletePathLawRealization

/-- Cross-game strategy-space isomorphism is stronger than a functional
realization and reverse deviation coverage. -/
structure CrossGameCompletePathLawStrategyIso
    {G H : ControlledObservedGame N}
    [MeasurableSpace G.base.History]
    [MeasurableSpace H.base.History]
    (S : G.CompletePathLawSemantics)
    (T : H.CompletePathLawSemantics)
    extends CrossGameCompletePathLawRealization S T where
  /-- Each player strategy carrier is equivalent. -/
  strategyEquiv : (i : N) → S.Strategy i ≃ T.Strategy i
  /-- The realization map is the forward equivalence. -/
  mapStrategy_eq :
    ∀ i, toCrossGameCompletePathLawRealization.mapStrategy i =
      strategyEquiv i

namespace CompletePathLawSemantics.CompletePathLawRealization

variable {G : ControlledObservedGame N}
  [MeasurableSpace G.base.History]
  {S T : G.CompletePathLawSemantics}

/-- Same-game realization is the identity-history special case of cross-game
functional realization. -/
def toCrossGame
    (R : S.CompletePathLawRealization T) :
    CrossGameCompletePathLawRealization S T where
  mapStrategy := R.mapStrategy
  mapHistory := id
  mapHistory_measurable := measurable_id
  mapPath := id
  mapPath_measurable := measurable_id
  mapPath_apply := by
    intro _path _time
    rfl
  pathLaw_map_eq := by
    intro profile current
    rw [Measure.map_id]
    exact R.pathLaw_eq profile current

end CompletePathLawSemantics.CompletePathLawRealization

namespace Iso

variable {G H : ControlledObservedGame N}
  [MeasurableSpace G.base.History]
  [MeasurableSpace H.base.History]

/-- A strict structural isomorphism packages a canonical cross-game
realization once measurability and semantic naturality are supplied.

The law equality is not inferred from structure alone. -/
def toCrossGameCompletePathLawRealization
    (e : G.Iso H)
    (S : G.CompletePathLawSemantics)
    (T : H.CompletePathLawSemantics)
    (mapStrategy :
      (i : N) → S.Strategy i → T.Strategy i)
    (hhistory :
      Measurable e.completeHistoryEquiv)
    (hpath :
      Measurable e.completePathEquiv)
    (hlaw :
      ∀ (profile : S.Profile)
        (current : G.base.History),
        (S.pathLaw profile current).map
            e.completePathEquiv =
          T.pathLaw
            (fun i => mapStrategy i (profile i))
            (e.completeHistoryEquiv current)) :
    CrossGameCompletePathLawRealization S T where
  mapStrategy := mapStrategy
  mapHistory := e.completeHistoryEquiv
  mapHistory_measurable := hhistory
  mapPath := e.completePathEquiv
  mapPath_measurable := hpath
  mapPath_apply := e.completePathEquiv_apply
  pathLaw_map_eq := hlaw

end Iso

/-! ## Zero measure cannot be probability semantics -/

/-- The zero measure cannot satisfy the probability certificate required by
`CompletePathLawSemantics`. -/
theorem zeroMeasure_not_probability
    {α : Type*} [MeasurableSpace α] :
    ¬ IsProbabilityMeasure (0 : Measure α) := by
  intro hprobability
  letI : IsProbabilityMeasure (0 : Measure α) := hprobability
  exact IsProbabilityMeasure.ne_zero (0 : Measure α) rfl

end ExtensiveGame.ControlledObservedGame
