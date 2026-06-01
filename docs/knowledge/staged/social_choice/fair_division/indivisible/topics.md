# Staged Indivisible Fair Division Topic Catalog

Canonical folder topic: `social_choice.fair_division.indivisible`

## Scope

`social_choice.fair_division.indivisible` covers allocation of a finite set of
indivisible goods to a finite set of agents under cardinal (typically
additive) valuations, with fairness notions adapted to the indivisible
setting: EF, EF1, EFX, PROP, EQ, MMS, and their algorithmic and
impossibility results.

The Lean source lives under
`EconCSLib/SocialChoice/FairDivision/Indivisible/`.

## Subtopics

- `social_choice.fair_division.indivisible.algorithms` - round-robin EF1
  allocation and envy-cycle-elimination EF1 + Pareto-improvement allocation.
- `social_choice.fair_division.indivisible.mms` - maximin share value,
  α-MMS approximation, and PROP ⇒ MMS / α-MMS implications.

## Expected Nodes (rooted at `social_choice.fair_division.indivisible`)

- `social_choice.fair_division.indivisible.allocation` - allocation type and
  partition predicate.
- `social_choice.fair_division.indivisible.valuation` and `.additive_valuation` -
  abstract real-valued bundle valuation and per-item additive specialization.
- Fairness predicates: `envy_free`, `ef1`, `efx`, `proportional`, `equitable`,
  `maximin_share`, plus implication theorems (`EFX ⇒ EF1`,
  `EF ⇒ EFX` for monotone valuations, `EF ⇒ PROP ⇒ MMS` for additive).
- Efficiency: `pareto_optimal`.
- Impossibility: `ef_impossible_two_agents_one_good`.
- EFX existence: special cases and two-agent existence theorem.
- Welfare: utilitarian / egalitarian welfare and optimality.
- Bundled `Instance` / `CardinalInstance` / `AdditiveInstance` wrappers.
- A `Checker` cluster with decidable iff-soundness theorems.

## Boundary

Cake-cutting and measure-theoretic fairness belong under
`social_choice.fair_division.divisible`. Shared predicates that don't care
about the indivisible bundle structure stay in
`social_choice.fair_division.core`.
