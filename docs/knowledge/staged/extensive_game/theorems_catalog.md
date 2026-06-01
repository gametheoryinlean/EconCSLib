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
| Lean module | `EconCSLib.ExtensiveGame.GameTreeSPE` |
| Lean declarations | `optStrategy_isSubgamePerfect`, `Kuhn_exists_SPE` |
| Status | formalized (proof: gap — induction sketch accepted) |

### 2. Kuhn's SPE Existence (with chance)

**Result:** Kuhn's theorem extended to games that include Nature/chance nodes;
existence of a mixed-strategy SPE.

| Field | Value |
|-------|-------|
| Knowledge node | [[game_theory.extensive_game.kuhn_spe_existence_with_chance]] |
| Lean module | pending — see EG-L6 [#220](https://github.com/gametheoryinlean/EconCSLib/issues/220) |
| Lean declarations | pending |
| Status | staged; blocked on chance-extension port |

### 3. Zermelo's Determinacy

**Result:** Every finite 2-player zero-sum perfect-information game is determined:
`optStrategy` is a saddle point with value `value₀ g` — player 0 secures at least
`value₀ g`, player 1 holds player 0 to at most `value₀ g`. (Bare pure-SPE / Nash
existence is the Kuhn instance `zermelo_exists_pure_SPE` / `zermelo_exists_pure_NE`,
which needs no zero-sum hypothesis.)

| Field | Value |
|-------|-------|
| Knowledge node | [[game_theory.extensive_game.perfect_information.zermelo_determinacy]] |
| Lean module | `EconCSLib.ExtensiveGame.Zermelo` |
| Lean declarations | `zermelo_determinacy`, `value₀_eq_outcome_and_zeroSum` |
| Status | formalized |

### 4. Backward-Induction Value Function

**Result:** The backward-induction recursion assigns a well-defined payoff
vector `value : GameTree N U → (N → U)` to every node of the game tree.

| Field | Value |
|-------|-------|
| Knowledge node | [[game_theory.extensive_game.perfect_information.zero_sum_perfect_information_value_no_chance]] |
| Lean module | `EconCSLib.ExtensiveGame.BackwardInduction` |
| Lean declarations | `value`, `valueList` |
| Status | formalized |

### 5. SPE Implies Nash

**Result:** Every subgame-perfect equilibrium is a Nash equilibrium of the
whole game.

| Field | Value |
|-------|-------|
| Knowledge node | [[game_theory.extensive_game.perfect_information.spe_implies_nash]] |
| Lean module | `EconCSLib.ExtensiveGame.GameTreeNE` |
| Lean declarations | `IsSubgamePerfect.toNE` |
| Status | formalized |

### 6. Normal-Form Reduction

**Result:** The pure-strategy profiles of a game tree form a strategic game
(`toStrategicGame`); a profile is a Nash equilibrium of that strategic game
if and only if it is a Nash equilibrium at the root of the tree.

| Field | Value |
|-------|-------|
| Knowledge node | [[game_theory.extensive_game.normal_form.agent_normal_form]] |
| Lean module | `EconCSLib.ExtensiveGame.GameTreeStrategicForm` |
| Lean declarations | `GameTree.toStrategicGame`, `toStrategicGame_nash_iff_isNashAt` |
| Status | formalized |

### 7. Imperfect-Information Strategies

**Result:** Definition of information sets, pure strategies, and behavioral
strategies for games with imperfect information.

| Field | Value |
|-------|-------|
| Knowledge node | [[game_theory.extensive_game.imperfect_information.information_set]] |
| Lean module | `EconCSLib.ExtensiveGame.ImperfectInformation` |
| Lean declarations | see module |
| Status | staged (definitions in place; key theorems pending) |

### 8. Sequential Equilibrium

**Result:** Every finite extensive game with perfect recall has a sequential
equilibrium (Kreps–Wilson 1982).

| Field | Value |
|-------|-------|
| Knowledge node | [[game_theory.extensive_game.sequential_equilibrium]] |
| Lean module | pending — see EG-L4 [#182](https://github.com/gametheoryinlean/EconCSLib/issues/182) |
| Lean declarations | pending |
| Status | staged; pending EG-L4 #182 |

### 9. Behavioral ≡ Mixed Under Perfect Recall

**Result:** Under perfect recall every mixed strategy is outcome-equivalent to
a behavioral strategy (Kuhn 1953).

| Field | Value |
|-------|-------|
| Knowledge node | [[game_theory.extensive_game.isbell_behavioral_to_mixed]] |
| Lean module | pending — see EG-L2 [#180](https://github.com/gametheoryinlean/EconCSLib/issues/180) |
| Lean declarations | pending |
| Status | staged; pending EG-L2 #180 |

---

## Pending items

| Item | Blocked on |
|------|-----------|
| Kuhn with chance (row 2) | EG-L6 #220 (chance-extension port) |
| Sequential equilibrium (row 8) | EG-L4 #182 |
| Behavioral ≡ mixed (row 9) | EG-L2 #180 |

## References

- Kuhn, H. W. (1953). "Extensive Games and the Problem of Information." In *Contributions to the Theory of Games, Vol. II*.
- [MFoGT, Ch. 6] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*.
- [MSZ, Ch. 3–4] Maschler, Solan, Zamir, *Game Theory*.
- Zermelo, E. (1913). "Über eine Anwendung der Mengenlehre auf die Theorie des Schachspiels."
