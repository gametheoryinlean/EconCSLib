# Staged Divisible Fair Division Topic Catalog

Canonical folder topic: `social_choice.fair_division.divisible`

## Scope

`social_choice.fair_division.divisible` covers cake-cutting: an abstract
measurable cake `Ω`, agents endowed with personal (possibly non-atomic)
measures on `Ω`, and allocations that are measurable partitions of `Ω`.

The Lean source lives under
`EconCSLib/SocialChoice/FairDivision/Divisible/`.

## Subtopics

- `social_choice.fair_division.divisible.cut_and_choose` - two-agent
  cut-and-choose protocol and its envy-freeness guarantees.
- `social_choice.fair_division.divisible.dubins_spanier` - moving-knife
  n-agent proportional allocation and the unit-interval IVT for measures.
- `social_choice.fair_division.divisible.stromquist` - Stromquist's KKM-based
  proof that envy-free contiguous allocations exist for any number of agents
  with non-atomic measures on `[0,1]`.

## Expected Nodes (rooted at `social_choice.fair_division.divisible`)

- `social_choice.fair_division.divisible.allocation` - allocation type and
  measurable-partition predicate, plus the contiguous-allocation predicate
  on `ℝ`.
- `social_choice.fair_division.divisible.cake_valuation` - abstract cake
  valuation interface and the normalization predicate.
- `social_choice.fair_division.divisible.measure_valuation` - measure-based
  cake valuation with additivity / countable additivity lemmas.
- `social_choice.fair_division.divisible.envy_free` - EF / PROP / EQ
  specialized to cake valuations, plus `EF ⇒ PROP` for measure valuations.
- Wrappers for bundled ordinal, cardinal, and measure-based divisible
  instances (`Divisible.Instance` / `Divisible.CardinalInstance` /
  `Divisible.MeasureInstance`).

## Boundary

Shared fairness predicates that do not depend on the cake structure
(`SocialChoice.FairDivision.IsEnvyFree`, etc.) live in
`social_choice.fair_division.core`, not here. Indivisible-items material
belongs under `social_choice.fair_division.indivisible`.
