---
id: mechanism_design.bayesian.bayesian_mechanisms
title: Bayesian Mechanisms
kind: definition
status: formalized
primary_topic: mechanism_design
topics:
- mechanism_design
- mechanism_design.bayesian
uses:
- mechanism_design.basic.direct_mechanism_interface
- mechanism_design.basic.induced_strategic_game
- mechanism_design.transfer.mechanisms_with_transfers
lean:
  modules:
  - EconCSLib.MechanismDesign.Auction.MechBayesian
  declarations:
  - BayesianMechanism
  - BayesianMechanism.Strategy
  - BayesianMechanism.StrategyProfile
  - BayesianMechanism.IsMeasurableStrategyProfile
  - BayesianMechanism.inducedMessages
  - BayesianMechanism.toMechanism
  - DirectBayesianMechanism
  - DirectBayesianMechanism.truthfulStrategy
  - BayesianMechanismWithTransfers
  - BayesianMechanismWithTransfers.StrategyProfile
  - BayesianMechanismWithTransfers.inducedAllocation
  - BayesianMechanismWithTransfers.inducedPayments
  - BayesianMechanismWithTransfers.deviate
  - BayesianMechanismWithTransfers.toMechanismWithTransfers
  - BayesianMechanismWithTransfers.toBayesianMechanism
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
tags:
- mechanism-design
- bayesian-mechanism
- incomplete-information
---

# Bayesian Mechanisms

Bayesian mechanisms record type spaces, message spaces, a common prior, and
type-contingent strategies. They induce messages from strategy profiles and can
be converted to direct or transfer mechanisms.

For mechanisms with transfers, the interface also records induced allocations,
induced payments, deviations, and the associated Bayesian mechanism obtained by
forgetting the allocation/payment decomposition.

## Mathematical model and Lean alignment

A Bayesian mechanism is a six-tuple

$$
\mathcal{M} \;=\; \bigl(I,\; (T_i)_{i \in I},\; (M_i)_{i \in I},\; O,\; p,\; g\bigr)
$$

with the following data.

- $I$ — set of agents.
- $T_i$ — agent $i$'s **type space**, equipped with a $\sigma$-algebra
  $\mathcal{F}_{T_i}$. A point $t_i \in T_i$ encodes all of agent $i$'s
  private information (Harsanyi type).
- $M_i$ — agent $i$'s **message** (or **report**) **space**. Need not
  equal $T_i$; choosing $M_i = T_i$ specializes to **direct revelation**.
- $O$ — **outcome space**. Any stochastic component of the mechanism is
  absorbed into the choice of $O$ (for example, a probabilistic single-item
  allocation rule records winning probabilities, not realized winners).
- $p$ — **common prior**: a probability measure on $T := \prod_{i \in I} T_i$
  carrying the joint distribution of types. The prior lives on the joint
  space, so types may be correlated; independence is an additional
  hypothesis recorded by downstream specializations.
- $g$ — **outcome rule**: a deterministic function
  $g : \prod_i M_i \to O$ mapping message profiles to outcomes.

Auxiliary objects used in strategic analysis are:

- a **pure strategy** $\sigma_i : T_i \to M_i$ and a **strategy profile**
  $\sigma = (\sigma_i)_{i \in I}$;
- the **induced message profile**
  $\sigma(t) := (\sigma_i(t_i))_{i \in I} \in \prod_i M_i$;
- a **measurable strategy profile**, requiring each $\sigma_i$ to be
  $(\mathcal{F}_{T_i}, \mathcal{F}_{M_i})$-measurable; needed only when
  ex-ante expected utilities are taken, not at the level of the bare
  mechanism;
- for a direct mechanism, the **truthful strategy**
  $\sigma_i^{\mathrm{truth}} := \mathrm{id}_{T_i}$.

### Lean alignment

The Lean structure `BayesianMechanism I T M O` realizes the math object
field by field.

| Mathematical object | Lean declaration | Note |
|---|---|---|
| $I$ | `(I : Type*)` | Agent index type; the literature symbol is kept in place of Mathlib's `ι`. |
| $T_i$ | `(T : I → Type*)` with `[∀ i, MeasurableSpace (T i)]` | Per-agent type space carrying a $\sigma$-algebra. The product $\sigma$-algebra on $T$ is supplied by `Pi.measurableSpace`. |
| $M_i$ | `(M : I → Type*)` | No measurability required at the mechanism level; added locally on consumers that integrate against strategies. |
| $O$ | `(O : Type*)` | Outcome space. |
| $p$ | `prior : Measure (∀ i, T i)` together with `prob_prior : IsProbabilityMeasure prior` | Mathematically a single probability measure. Lean stores it as a `Measure` so it composes directly with `Measure.pi`, `Measure.withDensity`, `MeasurePreserving`, `Integrable`, and `∫ · ∂μ`; the probability property is registered as a global instance via `attribute [instance] BayesianMechanism.prob_prior`, so typeclass search recovers it automatically wherever `B.prior` is integrated against. The two-field factoring is an interfacing choice with Mathlib's measure API, not a mathematical distinction. |
| $g$ | `outcome : (∀ i, M i) → O` | Deterministic. |
| $\sigma_i$ | `Strategy (T i) (M i) := T i → M i` | |
| $\sigma$ | `StrategyProfile T M := ∀ i, Strategy (T i) (M i)` | |
| $\sigma(t)$ | `inducedMessages σ t := fun i => σ i (t i)` | |
| $\sigma$ measurable | `IsMeasurableStrategyProfile σ := ∀ i, Measurable (σ i)` | Requires `[∀ i, MeasurableSpace (M i)]` locally. |
| Forget the prior | `toMechanism : BayesianMechanism I T M O → Mechanism I M O` | Recovers the complete-information mechanism on reported messages. |
| $\sigma_i^{\mathrm{truth}}$ | `DirectBayesianMechanism.truthfulStrategy := fun _ => id` | Available when $M_i = T_i$. |

### Specialization hierarchy

Mechanisms with transfers split $O$ into an allocation and a payment
vector; direct revelation pins $M_i = T_i$. The Lean tower mirrors this
specialization chain:

```text
BayesianMechanism I T M O
  │   split  O = A × (I → P)
  ▼
BayesianMechanismWithTransfers I T M A P
  │   pin   M = T
  ▼
DirectBayesianMechanismWithTransfers I T A P
```

Forgetful projections recover the underlying objects:

- `BayesianMechanismWithTransfers.toMechanismWithTransfers` drops the
  prior and lands in the complete-information transfer mechanism layer
  (`MechanismWithTransfers I M A P`).
- `BayesianMechanismWithTransfers.toBayesianMechanism` re-bundles the
  allocation and payment rules as a single outcome rule of type
  $A \times (I \to P)$.

Strategy-level objects parallel the base interface:

- `BayesianMechanismWithTransfers.inducedAllocation σ t`
  $= x(\sigma(t))$,
- `BayesianMechanismWithTransfers.inducedPayments σ t`
  $= p(\sigma(t))$,
- `BayesianMechanismWithTransfers.deviate σ i τ`
  $= (\sigma_1, \dots, \tau, \dots, \sigma_n)$ — single-agent strategy
  replacement, formalized via `Function.update`.

This node covers the data layer only. Ex-ante expected utility,
integrability hypotheses, and Bayesian Nash equilibrium are recorded by
the companion nodes
[[mechanism_design.bayesian.ex_ante_expected_utility]] and
[[mechanism_design.bayesian.ex_ante_equilibrium_predicates]].

## References

- [AGT, Chapter 9, Section 9.6, Def. 9.41] Nisan, Roughgarden, Tardos,
  and Vazirani, *Algorithmic Game Theory*. Bayesian mechanisms, type spaces,
  strategies, and expected utilities.
- [MFoGT, Chapter 7, Section 7.4] Maschler, Solan, and Zamir, *Game Theory*. Bayesian games and Bayesian equilibrium
  background.

## Used by auctions

[[mechanism_design.auction.bayesian.single_item_framework]] (single-item
Bayesian auction framework).

## Provenance

- Migrated from EconCSLib pull request 27, old blueprint label
  `def:md_bayesian_interface` in `blueprint/src/content.tex`.
