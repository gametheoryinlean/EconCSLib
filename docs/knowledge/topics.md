# Knowledge Topic Catalog

Canonical topic ids are declared in `mdblueprint.yml`. Game-theory content is
organized into **six big topics**, each with a single curated sub-level. A node
declares its placement with `primary_topic: <big>` and
`topics: [<big>, <big>.<sub>]`.

## Authoring Workflow

- `nodes/` contains older accepted-style nodes retained for compatibility.
- `staged/` contains public, reviewable mathematical nodes awaiting promotion.
- New extraction work normally goes under `staged/`.

Staged nodes are part of the public roadmap, not private drafts. Promotion is a
review step; do not bulk-move nodes merely to normalize directory structure.

## Game Theory (6 big topics)

- `game_theory.strategic_game` — Strategic (normal-form) games. Subtopics:
  `core`, `equilibrium`, `dominance`, `refinements`, `continuous`, `dynamics`,
  `bayesian_correlated`.
- `game_theory.zero_sum` — Zero-sum & matrix games. Subtopics: `core`,
  `minimax`, `learning`, `continuous`, `operators`, `examples`, `applications`.
  Alias: `zerosum`.
- `game_theory.extensive_game` — Extensive-form games. Subtopics: `core`,
  `perfect_information`, `imperfect_information`, `normal_form`, `examples`.
- `game_theory.cooperative_game` — Cooperative games (TU coalitional games;
  later also NTU / bargaining). Subtopics: `core`, `shapley_value`, `classes`.
  Alias: `coalitional_game`.
- `game_theory.repeated_game` — Repeated games. Subtopics: `core`,
  `folk_theorem`, `incomplete_info`.
- `game_theory.stochastic_game` — Stochastic games. Subtopics: `core`, `value`,
  `asymptotic`.

Zero-sum is its own big topic (not nested under strategic), since it is large
and self-contained. Node ids keep their historical paths; placement is driven by
the `topics`/`primary_topic` fields, not by the id.

## Other Areas

- `social_choice` — voting (Arrow, Gibbard–Satterthwaite, rules) and fair
  division (divisible, indivisible).
- `mechanism_design` — mechanisms, transfers, truthfulness, Bayesian, VCG,
  Myerson, auctions.
- `foundation.utility` — preferences, lotteries, vNM axioms, expected utility.
- `foundation.cost` — the `CostM` complexity monad (cost-annotated computation),
  its parallel/space cost algebras, and worked examples (`foundation.cost.examples`).
- `math.*` — supporting mathematics: `minimax`, `fixed_point`, `linear_algebra`,
  `linear_programming`, `simplex`.
- `order`, `lattice` — order/lattice-theoretic support facts.

## Boundary

Each game-theory node belongs to exactly one big topic and one sub-topic. Keep
the tree two levels deep under each big topic; do not reintroduce deeper
chains. Use canonical ids in `uses` references; legacy aliases are
compatibility-only.
