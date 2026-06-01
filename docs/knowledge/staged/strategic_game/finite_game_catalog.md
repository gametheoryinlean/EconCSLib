---
id: game_theory.strategic_game.finite_game_catalog
primary_topic: game_theory.strategic_game
topics:
  - game_theory.strategic_game
  - game_theory.strategic_game.core
title: Finite Game Catalog
kind: definition
status: staged
uses:
  - game_theory.extensive_game.perfect_information.kuhn_spe_existence_no_chance
  - game_theory.extensive_game.perfect_information.zermelo_determinacy
  - math.minimax.loomis_theorem
  - game_theory.strategic_game.zero_sum.matrix_game_nash_equilibrium
  - game_theory.strategic_game.equilibrium.nash_existence_finite_games
verification:
  definition: accepted
tags:
  - finite-game
  - index
  - catalog
---

# Finite Game Catalog

Index of canonical theorems about finite games that are formally proved in
EconCSLib, distributed across `ExtensiveGame` and `StrategicGame`.  Readers
looking for a specific existence result should start here.

## Catalog

- **Kuhn's SPE existence (no chance)** — every finite perfect-information game
  without chance moves has a pure subgame-perfect equilibrium, constructed by
  backward induction.
  Lean: `EconCSLib.ExtensiveGame.GameTreeSPE :: Kuhn_exists_SPE`.
  Knowledge node: [[game_theory.extensive_game.perfect_information.kuhn_spe_existence_no_chance]].

- **Zermelo's determinacy (2-player zero-sum, perfect information)** — every
  finite 2-player zero-sum perfect-information game is determined: `optStrategy`
  is a saddle with value `value₀ g`.
  Lean: `EconCSLib.ExtensiveGame.Zermelo :: zermelo_determinacy`.
  Knowledge node: [[game_theory.extensive_game.perfect_information.zermelo_determinacy]].

- **Backward-induction value** — the `value` function assigns a payoff vector
  to every node by backward induction; `valueList` is the mutually recursive
  helper over lists of subtrees.
  Lean: `EconCSLib.ExtensiveGame.BackwardInduction :: GameTree.value`,
  `GameTree.valueList`.

- **Loomis minimax** — every finite matrix game over `ℝ` satisfies
  `max_x min_y xᵀAy = min_y max_x xᵀAy`, proved by the simplified Loomis
  induction on `|I| + |J|`.
  Lean: `EconCSLib.Math.Minimax.LoomisGeneral :: LoomisGeneral.minmax_from_general`
  (the `B = 𝟙` corollary of the general Loomis theorem).
  Knowledge nodes: [[math.minimax.loomis_theorem]],
  [[math.minimax.minimax_from_loomis]].

- **Ordered-field minimax** — the von Neumann minimax theorem over any
  linearly ordered field, via symmetrisation (an independent route to the
  same equality).
  Lean: `EconCSLib.Math.Minimax.Minimax :: Minimax.minimax`.

- **Matrix-game mixed Nash (Loomis route)** — every finite 2-player zero-sum
  matrix game has a mixed Nash equilibrium, derived from the Loomis minimax
  saddle point.
  Lean: `EconCSLib.StrategicGame.MatrixGameNash ::
  MatrixGame.exists_mixed_nash_equilibrium`.
  Knowledge node: [[game_theory.strategic_game.zero_sum.matrix_game_nash_equilibrium]].

- **General n-player finite Nash (Brouwer route)** — every finite strategic
  game has a mixed Nash equilibrium (Nash 1951).
  Lean: planned — `EconCSLib.StrategicGame.Nash ::
  exists_mixed_nash_equilibrium_finite` (see SG-L2 #199).
  Knowledge node: [[game_theory.strategic_game.equilibrium.nash_existence_finite_games]].

## Scope

This node covers *finite* games only.  Infinite-horizon, continuous-action, and
stochastic game results live in their own sections of the knowledge base.  The
chance-node extension of Kuhn's theorem (requiring vNM lottery utility) is
tracked by [[game_theory.extensive_game.kuhn_spe_existence_with_chance]].

## See also

- [[game_theory.extensive_game.theorems_catalog]] — comprehensive index of extensive-game theorems and their Lean locations.

## References

- [MSZ, Ch. 3, 4] Maschler, Solan, and Zamir, *Game Theory*.
- [MFoGT, §§2.3, 4.6, 6.2] Laraki, Renault, and Sorin,
  *Mathematical Foundations of Game Theory*.
