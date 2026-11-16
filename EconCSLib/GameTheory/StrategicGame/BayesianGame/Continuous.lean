/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Probability.Kernel.Composition.Lemmas
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Probability.Kernel.Representation

/-!
# Continuous Bayesian and nonatomic strategies

This module formalizes the measure-theoretic strategy representations in
[MFoGT, Section 7.4.2]. A behavioral strategy is a Markov kernel from types to
actions. A random-seed strategy is a jointly measurable map from the product
of the type space and the unit interval, equipped with uniform measure, to the
action space. A distributional strategy is a probability measure on the
type-action product with the prescribed type marginal.

The standard-Borel assumption on actions is substantive: it is what permits a
jointly measurable random-seed realization of every Markov kernel and a
regular conditional distribution for every distributional strategy.

The final section formalizes the nonatomic model stated after
[MFoGT, Example 7.4.1]. Its equilibrium condition is expressed both as the
source's full-measure best-response graph and as the equivalent almost-everywhere
inequality. Measurability of that graph is explicit rather than silently
assumed.

## Main results

* `ContinuousBehaviorStrategy.exists_randomSeedStrategy` - every behavioral
  strategy on a standard Borel action space has a jointly measurable
  `[0,1]`-seed realization;
* `RandomSeedStrategy.inducedDistribution_eq_behavior` - the seed
  realization and its behavioral kernel induce exactly the same joint law;
* `ContinuousDistributionalStrategy.exists_behaviorStrategy` - every
  compatible joint law has a regular conditional behavioral strategy;
* `NonatomicBayesianGame.isDistributionalEquilibrium_iff_ae` - equivalence
  between the source's measure-one condition and almost-everywhere optimality.

## References

* [MFoGT] Chapter 7, Section 7.4.2
* Kallenberg, *Foundations of Modern Probability*, Lemma 4.22
-/

open MeasureTheory ProbabilityTheory Set unitInterval

namespace StrategicGame

universe uT uA

/-! ## Behavioral strategies and random seeds -/

/-- A behavioral strategy on measurable type and action spaces is a Markov
kernel assigning a probability distribution on actions to every type. -/
structure ContinuousBehaviorStrategy (Ty : Type uT) (Act : Type uA)
    [MeasurableSpace Ty] [MeasurableSpace Act] where
  /-- The type-contingent action kernel. -/
  kernel : Kernel Ty Act
  /-- Every conditional action law is a probability measure. -/
  [isMarkovKernel : IsMarkovKernel kernel]

attribute [instance] ContinuousBehaviorStrategy.isMarkovKernel

namespace ContinuousBehaviorStrategy

variable {Ty : Type uT} {Act : Type uA}
variable [MeasurableSpace Ty] [MeasurableSpace Act]

/-- A mixed strategy represented by a jointly measurable action function of
the player's type and an independent uniform seed on `[0,1]`, exactly as in
[MFoGT, Section 7.4.2]. -/
structure RandomSeedStrategy (Ty : Type uT) (Act : Type uA)
    [MeasurableSpace Ty] [MeasurableSpace Act] where
  /-- The action selected from a type and a unit-interval seed. -/
  action : Ty → I → Act
  /-- Joint measurability, not merely separate measurability. -/
  measurable_action : Measurable (Function.uncurry action)

namespace RandomSeedStrategy

/-- The behavioral kernel induced by uniform independent randomization of a
random-seed strategy. -/
noncomputable def inducedBehavior (seedStrategy : RandomSeedStrategy Ty Act) :
    ContinuousBehaviorStrategy Ty Act where
  kernel :=
    (Kernel.id ×ₖ Kernel.const Ty (volume : Measure I)).map
      (Function.uncurry seedStrategy.action)
  isMarkovKernel := by
    have hprod :
        IsMarkovKernel (Kernel.id ×ₖ Kernel.const Ty (volume : Measure I)) :=
      inferInstance
    exact ProbabilityTheory.Kernel.IsMarkovKernel.map _
      seedStrategy.measurable_action

/-- At each type, the induced behavioral law is the pushforward of uniform
measure by the corresponding seed-to-action map. -/
theorem inducedBehavior_apply (seedStrategy : RandomSeedStrategy Ty Act) (t : Ty) :
    seedStrategy.inducedBehavior.kernel t =
      volume.map (seedStrategy.action t) := by
  rw [inducedBehavior, Kernel.map_apply _ seedStrategy.measurable_action]
  simp only [Kernel.prod_apply, Kernel.id_apply, Kernel.const_apply]
  rw [Measure.dirac_prod,
    Measure.map_map seedStrategy.measurable_action measurable_prodMk_left]
  rfl

/-- The joint type-action law induced by a type prior and a random seed. -/
noncomputable def inducedDistribution (seedStrategy : RandomSeedStrategy Ty Act)
    (μ : Measure Ty) : Measure (Ty × Act) :=
  (μ.prod (volume : Measure I)).map
    (fun p => (p.1, seedStrategy.action p.1 p.2))

/-- A random-seed strategy and its induced behavioral kernel generate exactly
the same joint law on types and actions. -/
theorem inducedDistribution_eq_behavior (seedStrategy : RandomSeedStrategy Ty Act)
    (μ : Measure Ty) [SFinite μ] :
    seedStrategy.inducedDistribution μ =
      μ ⊗ₘ seedStrategy.inducedBehavior.kernel := by
  apply Measure.ext
  intro s hs
  change
    (Measure.map
      (fun p => (p.1, Function.uncurry seedStrategy.action p))
      (μ.prod (volume : Measure I))) s =
      (μ ⊗ₘ seedStrategy.inducedBehavior.kernel) s
  rw [Measure.map_apply
      (measurable_fst.prodMk seedStrategy.measurable_action) hs,
    Measure.compProd_apply hs,
    Measure.prod_apply
      ((measurable_fst.prodMk seedStrategy.measurable_action) hs)]
  apply lintegral_congr
  intro t
  rw [seedStrategy.inducedBehavior_apply,
    Measure.map_apply seedStrategy.measurable_action.of_uncurry_left
      (measurable_prodMk_left hs)]
  rfl

end RandomSeedStrategy

variable [Nonempty Act] [StandardBorelSpace Act]

/-- Every continuous behavioral strategy has the measurable `[0,1]` random-seed
representation stated in [MFoGT, Section 7.4.2]. -/
theorem exists_randomSeedStrategy (β : ContinuousBehaviorStrategy Ty Act) :
    ∃ seedStrategy : RandomSeedStrategy Ty Act,
      seedStrategy.inducedBehavior.kernel = β.kernel := by
  obtain ⟨f, hf, hmap⟩ := β.kernel.exists_measurable_map_eq_unitInterval
  refine ⟨⟨f, hf⟩, ?_⟩
  apply Kernel.ext
  intro t
  rw [RandomSeedStrategy.inducedBehavior_apply]
  exact hmap t

end ContinuousBehaviorStrategy

/-! ## Distributional strategies -/

variable {Ty : Type uT} {Act : Type uA}
variable [MeasurableSpace Ty] [MeasurableSpace Act]
variable [Nonempty Act] [StandardBorelSpace Act]

/-- A continuous distributional strategy is a probability measure on the
type-action product whose type marginal is the given prior. -/
structure ContinuousDistributionalStrategy (μ : Measure Ty) where
  /-- The joint distribution of type and action. -/
  joint : Measure (Ty × Act)
  /-- The joint law is a probability measure. -/
  [isProbabilityMeasure : IsProbabilityMeasure joint]
  /-- Compatibility with the data: the type marginal is the prescribed law. -/
  fst_eq : joint.fst = μ

attribute [instance] ContinuousDistributionalStrategy.isProbabilityMeasure

namespace ContinuousDistributionalStrategy

variable {μ : Measure Ty} [IsProbabilityMeasure μ]

/-- The distributional strategy induced by a behavioral kernel. -/
noncomputable def ofBehavior (β : ContinuousBehaviorStrategy Ty Act) :
    ContinuousDistributionalStrategy (Act := Act) μ where
  joint := μ ⊗ₘ β.kernel
  isProbabilityMeasure := inferInstance
  fst_eq := Measure.fst_compProd μ β.kernel

/-- The conditional behavioral strategy canonically obtained from a
distributional strategy by standard-Borel disintegration. -/
noncomputable def toBehavior
    (d : ContinuousDistributionalStrategy (Act := Act) μ) :
    ContinuousBehaviorStrategy Ty Act where
  kernel := d.joint.condKernel
  isMarkovKernel := inferInstance

/-- Disintegration recovers the original compatible joint law exactly. -/
theorem ofBehavior_toBehavior
    (d : ContinuousDistributionalStrategy (Act := Act) μ) :
    (ofBehavior (μ := μ) d.toBehavior).joint = d.joint := by
  change μ ⊗ₘ d.joint.condKernel = d.joint
  calc
    μ ⊗ₘ d.joint.condKernel =
        d.joint.fst ⊗ₘ d.joint.condKernel := by
          exact congrArg (fun prior => prior ⊗ₘ d.joint.condKernel)
            d.fst_eq.symm
    _ = d.joint := d.joint.disintegrate d.joint.condKernel

/-- Every compatible continuous distributional strategy is induced by a
behavioral strategy. This uses regular conditional probabilities and therefore
the standard-Borel action assumption above. -/
theorem exists_behaviorStrategy
    (d : ContinuousDistributionalStrategy (Act := Act) μ) :
    ∃ β : ContinuousBehaviorStrategy Ty Act,
      (ofBehavior (μ := μ) β).joint = d.joint :=
  ⟨d.toBehavior, d.ofBehavior_toBehavior⟩

end ContinuousDistributionalStrategy

/-! ## Nonatomic Bayesian games -/

/-- The nonatomic Bayesian/population model following
[MFoGT, Example 7.4.1].

The agent law is required to be a probability measure and atomless. The payoff
may depend on the agent's type, their own action, and the population action
distribution. Analytic regularity of a particular payoff is kept local to the
theorems that use it. -/
structure NonatomicBayesianGame (Agent : Type uT) (Action : Type uA)
    [MeasurableSpace Agent] [MeasurableSpace Action] where
  /-- The distribution of agents/types. -/
  agentLaw : Measure Agent
  /-- Population mass is normalized to one. -/
  [agentLawProbability : IsProbabilityMeasure agentLaw]
  /-- No individual agent has positive mass. -/
  [agentLawNoAtoms : NoAtoms agentLaw]
  /-- Payoff from own type, own action, and the population action law. -/
  payoff : Agent → Action → Measure Action → ℝ

attribute [instance] NonatomicBayesianGame.agentLawProbability
attribute [instance] NonatomicBayesianGame.agentLawNoAtoms

namespace NonatomicBayesianGame

variable {Agent : Type uT} {Action : Type uA}
variable [MeasurableSpace Agent] [MeasurableSpace Action]

/-- The action marginal of a joint type-action distribution. -/
noncomputable def actionDistribution (dist : Measure (Agent × Action)) :
    Measure Action :=
  dist.snd

/-- The graph of actions that maximize payoff against population law `ν`. -/
def bestResponseGraph (G : NonatomicBayesianGame Agent Action)
    (ν : Measure Action) : Set (Agent × Action) :=
  {p | ∀ a', G.payoff p.1 a' ν ≤ G.payoff p.1 p.2 ν}

/-- Distributional equilibrium in the nonatomic model. This is the literal
measure-one formulation in [MFoGT, Section 7.4.2], with all measure-theoretic
side conditions exposed:

* `λ` is a probability measure on the type-action product;
* its type marginal is the atomless agent law;
* its action marginal is the endogenous population law;
* the best-response graph is measurable and has full `λ`-measure.
-/
def IsDistributionalEquilibrium (G : NonatomicBayesianGame Agent Action)
    (dist : Measure (Agent × Action)) : Prop :=
  IsProbabilityMeasure dist ∧
    dist.fst = G.agentLaw ∧
    MeasurableSet (G.bestResponseGraph (actionDistribution dist)) ∧
    dist (G.bestResponseGraph (actionDistribution dist)) = 1

/-- The source's measure-one equilibrium condition is equivalent to saying
that `λ`-almost every selected action is optimal against the endogenous action
distribution. -/
theorem isDistributionalEquilibrium_iff_ae
    (G : NonatomicBayesianGame Agent Action)
    (dist : Measure (Agent × Action)) :
    G.IsDistributionalEquilibrium dist ↔
      IsProbabilityMeasure dist ∧
        dist.fst = G.agentLaw ∧
        MeasurableSet (G.bestResponseGraph (actionDistribution dist)) ∧
        ∀ᵐ p ∂dist, ∀ a',
          G.payoff p.1 a' (actionDistribution dist) ≤
            G.payoff p.1 p.2 (actionDistribution dist) := by
  constructor
  · rintro ⟨hprob, hfst, hmeas, hfull⟩
    letI : IsProbabilityMeasure dist := hprob
    refine ⟨hprob, hfst, hmeas, ?_⟩
    change ∀ᵐ p ∂dist,
      p ∈ G.bestResponseGraph (actionDistribution dist)
    rw [MeasureTheory.ae_mem_iff_measure_eq hmeas.nullMeasurableSet]
    simpa using hfull
  · rintro ⟨hprob, hfst, hmeas, hae⟩
    letI : IsProbabilityMeasure dist := hprob
    refine ⟨hprob, hfst, hmeas, ?_⟩
    have hae' : ∀ᵐ p ∂dist,
        p ∈ G.bestResponseGraph (actionDistribution dist) := by
      simpa [bestResponseGraph] using hae
    have hmeasure :=
      (MeasureTheory.ae_mem_iff_measure_eq hmeas.nullMeasurableSet).mp hae'
    simpa using hmeasure

end NonatomicBayesianGame

end StrategicGame
