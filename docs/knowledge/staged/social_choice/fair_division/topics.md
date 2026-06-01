# Staged Fair Division Topic Catalog

Canonical folder topic: `social_choice.fair_division`

## Scope

`social_choice.fair_division` is the fair-division specialization of social
choice: the alternative space is a space of allocations, each agent values
only the share they receive (the no-externality model), and the central
questions are existence of fair (EF, PROP, EQ, MMS) and efficient (PO,
utilitarian, maximin) allocations, plus the algorithms that produce them.

The Lean source lives under `EconCSLib/SocialChoice/FairDivision/`.

## Subtopics

- `social_choice.fair_division.core` - generic allocation type, generic and
  share-only instances, real-valued cardinal instances, and shared fairness
  and welfare predicates (`IsEnvyFree`, `IsProportional`, `IsEquitable`,
  `IsParetoOptimal`, `utilitarianWelfare`, `egalitarianWelfare`).
- `social_choice.fair_division.divisible` - cake cutting with measurable
  pieces and (non-atomic) measure valuations.
- `social_choice.fair_division.indivisible` - allocation of discrete items
  with additive or general valuations, including EF1 / EFX / PROP / EQ / MMS,
  round-robin, envy-cycle elimination, and impossibility examples.

## Boundary

Generic preference and choice infrastructure stays in `social_choice`.
Voting axioms and impossibility theorems on unstructured alternative sets stay
in `social_choice.voting`. Mechanism-design topics (auctions, transfers, VCG,
Myerson) belong under `mechanism_design.*` and `auction.*` and are out of
scope here.
