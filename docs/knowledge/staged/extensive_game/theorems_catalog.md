---
id: game_theory.extensive_game.theorems_catalog
title: Extensive-Game Theorems Catalog
kind: definition
status: staged
primary_topic: game_theory.extensive_game
topics:
  - game_theory.extensive_game
  - game_theory.extensive_game.perfect_information
uses:
  - game_theory.extensive_game.perfect_information.kuhn_spe_existence_no_chance
  - game_theory.extensive_game.perfect_information.zermelo_determinacy
  - game_theory.extensive_game.perfect_information.subgame_perfect_equilibrium
  - game_theory.extensive_game.perfect_information.spe_implies_nash
verification:
  definition: accepted
  proof: not_applicable
tags:
  - extensive-game
  - catalog
  - subgame-perfect-equilibrium
  - backward-induction
  - normal-form-reduction
---

# Extensive-Game Theorems Catalog

Index of canonical results for **extensive-form games** and their Lean
locations in EconCSLib.  Each row links to the dedicated knowledge node and
the module that contains the proof.

For the analogous strategic-game / zero-sum catalog see
[[game_theory.strategic_game.finite_game_catalog]].

---

## Catalog

### 1. Kuhn's SPE Existence (no chance)

**Result:** Every finite perfect-information game without chance nodes has a
pure-strategy subgame-perfect equilibrium.

| Field | Value |
|-------|-------|
| Knowledge node | [[game_theory.extensive_game.perfect_information.kuhn_spe_existence_no_chance]] |
| Lean module | `EconCSLib.GameTheory.ExtensiveGame.Compiler.GameTreeOccurrenceObserved` |
| Lean declarations | `occurrenceBackwardInductionProfile_isPureStandardSubgamePerfect`, `Kuhn_exists_occurrencePureSPE` |
| Status | formalized |

### 2. Kuhn's SPE Existence (with chance)

**Result:** Kuhn's theorem extended to finite perfect-information games with
fixed Nature/chance laws; existence of a pure contingent-strategy SPE.

| Field | Value |
|-------|-------|
| Knowledge node | [[game_theory.extensive_game.perfect_information.kuhn_spe_existence_with_chance]] |
| Lean module | `EconCSLib.GameTheory.ExtensiveGame.StochasticGameTree` (normalized execution only) |
| Lean declarations | pending |
| Status | staged; equilibrium-existence proof gap |

### 3. Zermelo's Determinacy

**Result:** Every finite 2-player zero-sum perfect-information game is determined:
`optStrategy` is a saddle point with value `value₀ g` — player 0 secures at least
`value₀ g`, player 1 holds player 0 to at most `value₀ g`. (Bare pure-SPE / Nash
structural endpoint/root-Nash existence is provided by
`zermelo_exists_pure_globalEndpointSPE_on` / `zermelo_exists_pure_NE`,
which needs no zero-sum hypothesis.)

| Field | Value |
|-------|-------|
| Knowledge node | [[game_theory.extensive_game.perfect_information.zermelo_determinacy]] |
| Lean module | `EconCSLib.GameTheory.ExtensiveGame.Zermelo` |
| Lean declarations | `zermelo_determinacy`, `value₀_eq_outcome_and_zeroSum` |
| Status | formalized |

### 4. Backward-Induction Value Function

**Result:** The backward-induction recursion assigns a well-defined payoff
vector `value : GameTree N U → (N → U)` to every node of the game tree.

| Field | Value |
|-------|-------|
| Knowledge node | [[game_theory.extensive_game.perfect_information.zero_sum_perfect_information_value_no_chance]] |
| Lean module | `EconCSLib.GameTheory.ExtensiveGame.BackwardInduction` |
| Lean declarations | `value`, `valueList` |
| Status | formalized |

### 5. SPE Implies Nash

**Result:** Every subgame-perfect equilibrium is a Nash equilibrium of the
whole game.

| Field | Value |
|-------|-------|
| Knowledge node | [[game_theory.extensive_game.perfect_information.spe_implies_nash]] |
| Lean module | `EconCSLib.GameTheory.ExtensiveGame.Observed.SPE` |
| Lean declarations | `ObservedGame.IsPureStandardSubgamePerfect.isNashAtInit` |
| Status | formalized |

### 6. Normal-Form Reduction

**Result:** The pure-strategy profiles of a game tree form a strategic game
(`toStrategicGame`); a profile is a Nash equilibrium of that strategic game
if and only if it is a Nash equilibrium at the root of the tree.

| Field | Value |
|-------|-------|
| Knowledge node | [[game_theory.extensive_game.normal_form.agent_normal_form]] |
| Lean module | `EconCSLib.GameTheory.ExtensiveGame.GameTreeStrategicForm` |
| Lean declarations | `GameTree.toStrategicGame`, `toStrategicGame_nash_iff_isNashAt` |
| Status | formalized |

### 7. Imperfect-Information Strategies

**Result:** Definition of coherent information-set actions,
information-indexed pure strategies, and history-indexed behavioral strategies
for games with imperfect information.

| Field | Value |
|-------|-------|
| Knowledge node | [[game_theory.extensive_game.imperfect_information.information_set]] |
| Lean module | `EconCSLib.GameTheory.ExtensiveGame.ImperfectInformation`, `EconCSLib.GameTheory.ExtensiveGame.Observed.Behavior` |
| Lean declarations | `FiniteImperfectGame.PureStrategy`, `ObservedGame.BehavioralStrategy` |
| Status | formalized definitions; equilibrium-existence theorems pending |

### 8. Sequential Equilibrium

**Result:** Every finite extensive game with perfect recall has a sequential
equilibrium (Kreps–Wilson 1982).

| Field | Value |
|-------|-------|
| Knowledge node | [[game_theory.extensive_game.imperfect_information.sequential_equilibrium]] |
| Lean module | pending |
| Lean declarations | pending |
| Status | staged; proof gap |

### 9. Behavioral ≡ Mixed Under Perfect Recall

**Result:** Under perfect recall every mixed strategy is outcome-equivalent to
a behavioral strategy (Kuhn 1953).

| Field | Value |
|-------|-------|
| Knowledge node | [[game_theory.extensive_game.imperfect_information.perfect_recall_mixed_to_behavioral]] |
| Lean module | `EconCSLib.GameTheory.ExtensiveGame.Observed.KuhnConditioning.Realization` (finite bounded realization); general target pending |
| Lean declarations | `ObservedChanceGame.isBehavioralNashOnDesignatedContinuationsAtFuel_iff_mixed` |
| Status | bounded finite theorem formalized; unrestricted textbook statement remains a proof gap |

---

## Pending items

| Item | Blocked on |
|------|-----------|
| Kuhn with chance (row 2) | standard subgame/equilibrium layer for normalized chance trees |
| Sequential equilibrium (row 8) | beliefs, consistency, and sequential-rationality implementation |
| General behavioral ≡ mixed (row 9) | extension beyond the current finite bounded realization theorem |

## References

- Kuhn, H. W. (1953). "Extensive Games and the Problem of Information." In *Contributions to the Theory of Games, Vol. II*.
- [MFoGT, Ch. 6] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*.
- [MSZ, Ch. 3–4] Maschler, Solan, Zamir, *Game Theory*.
- Zermelo, E. (1913). "Über eine Anwendung der Mengenlehre auf die Theorie des Schachspiels."
