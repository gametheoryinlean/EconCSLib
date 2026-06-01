# ExtensiveGame (GameTree) — API Design

Developer-facing design notes for the **finite perfect-information, no-chance**
extensive-game line in `EconCSLib/GameTheory/ExtensiveGame/`, built on the
inductive `GameTree` type: **how the Lean API is built** — the data model, where
each typeclass assumption enters, and how backward induction climbs from a value
function to Kuhn's SPE-existence theorem and Zermelo determinacy.

> Scope. This note covers the **`GameTree`** files (`GameTree`, `BackwardInduction`,
> `GameTreeSPE`, `GameTreeNE`, `GameTreeStrategicForm`, `Zermelo`, plus the
> `Examples/SimpleGameTree` smoke test). The *other* extensive-game framework —
> the state-space **`Arena`** model (`Basic`/`Strategy`/`Play`/`Subgame`), which
> supports infinite and imperfect-information games — is a separate design and is
> only cross-referenced here.

Part of the [design documentation set](README.md). Complements, does not replace:

- [`docs/design.md`](../design.md) — project-wide architecture and rules.
- `docs/knowledge/` — the published mathematical blueprint (textbook layer).

## Design principles, as they land here

1. **Bourbaki discipline.** `GameTree N U` constrains *neither* `N` nor `U`: no
   `Fintype`, no `DecidableEq`, no order. Finiteness is structural (the inductive
   type); `[TotalPreorder U]` is added only at the theorems that compare payoffs.
2. **Minimal order, no field.** The entire value / SPE / Kuhn stack needs only
   `[TotalPreorder U]` (reflexive + transitive + total) — *no* antisymmetry, *no*
   decidability, *no* arithmetic. Numbers (`ℚ`) enter only in the zero-sum
   `Zermelo` layer, where sums and negation are genuinely used.
3. **Stable predicates over wrappers.** Equilibria are predicates on strategies,
   not bespoke structures; subgames are the `Subtree` relation, not a new type.
4. **One "Kuhn".** "Kuhn's theorem" here = backward-induction / SPE existence
   (Kuhn 1953). The *other* Kuhn theorem (mixed ≡ behavioral under perfect
   recall) lives in `BehaviorStrategy.lean` (Arena side, EG-L2). Don't conflate.

## Module map

```
GameTheory/ExtensiveGame/
  GameTree.lean              -- the inductive type, size, children, Subtree, strong_induction  (§1)
  BackwardInduction.lean     -- value / valueList (argmax), value_Node_ge                       (§2)
  GameTreeSPE.lean           -- Strategy, outcome, optStrategy, IVariant, SPE, Kuhn_exists_SPE   (§3,§4)
  GameTreeNE.lean            -- IsNashEquilibrium, IsSubgamePerfectOn, Kuhn_exists_NE/_SPE_on     (§4)
  GameTreeStrategicForm.lean -- toStrategicGame bridge to the normal-form module                 (§4)
  Zermelo.lean               -- IsZeroSum, value₀, zermelo_determinacy (saddle value)            (§5)
```

Conventions: `[MSZ, Ch. 3]` = Maschler/Solan/Zamir, *Game Theory* (Cambridge,
2013), extensive games. "Minimal assumptions" lists what a declaration needs on
top of the always-present `{N U : Type*}`. Signatures abbreviated; source is
authoritative.

---

## 1. Core model — the `GameTree` type

File: [`GameTree.lean`](../../../EconCSLib/GameTheory/ExtensiveGame/GameTree.lean)

```lean
inductive GameTree (N : Type*) (U : Type*) : Type _
  | Leaf (payoff : N → U)
  | Node (mover : N) (head : GameTree N U) (tail : List (GameTree N U))
```

| name | Minimal assumptions | Meaning |
|------|--------------------|---------|
| `GameTree N U` | **none** | Finite perfect-info game: players `N`, payoffs `U`. |
| `Leaf payoff` | none | Terminal node with payoff vector `N → U`. |
| `Node mover head tail` | none | Decision node owned by `mover`, children `head :: tail`. |

Two modelling choices are load-bearing:

- **Finiteness is the inductive type itself** — no separate well-foundedness
  hypothesis is ever needed.
- **Children are non-empty by construction.** A `Node` carries `head` *plus*
  `tail : List`, so `children = head :: tail` is always non-empty
  (`children_node_ne_nil`). This is why backward induction can always pick a
  child — there is no empty-node edge case.
- **No `Nature` constructor.** The core stays chance-free. Separate stochastic
  tree modules model chance where the additional utility infrastructure is
  appropriate.

The supporting vocabulary every later proof leans on:

| name | Meaning |
|------|---------|
| `size` | structural size (`Leaf = 1`, `Node = 1 + head + Σ tail`); `size_pos`, `size_mem_children_lt` feed well-founded recursion. |
| `Subtree s g` | `s` occurs inside `g` (reflexive / in head / in a tail child); `Subtree.trans` = "a subgame of a subgame is a subgame". |
| `strong_induction` | to prove `motive g`, handle `Leaf` and each `Node` given the motive for **every** child. Stronger than the default recursor (which gives IH on the head only) — exactly what backward induction needs. |

`strong_induction` is the workhorse: `value`, `outcome`, and every zero-sum
invariant are proved by it.

---

## 2. Backward-induction value

File: [`BackwardInduction.lean`](../../../EconCSLib/GameTheory/ExtensiveGame/BackwardInduction.lean)

```lean
mutual
  noncomputable def value : GameTree N U → (N → U)
    | Leaf p => p
    | Node m h t => List.argMaxOn (fun v => v m) (value h) (valueList t)
  noncomputable def valueList : List (GameTree N U) → List (N → U)
    | [] => [] | x :: xs => value x :: valueList xs
end
```

| name | Minimal assumptions | Meaning |
|------|--------------------|---------|
| `value g` | `[TotalPreorder U]` | BI value vector: at a `Node`, the mover picks a child maximizing *their own* coordinate. |
| `value_Node_ge` | same | the mover's coordinate of `value (Node …)` dominates every child's. |
| `value_Node_eq_some_child_value` | same | `value (Node …)` *is* the value of some child (the argmax). |

`value` is `noncomputable` because `argMaxOn` over a total preorder needs
classical choice. The two lemmas are the entire interface used downstream: one
gives optimality (`≥` every child for the mover), the other says the optimum is
realized by an actual child. `[TotalPreorder U]` is the *only* assumption — the
argmax needs comparability, nothing more.

---

## 3. Strategies, outcome, and the BI strategy

File: [`GameTreeSPE.lean`](../../../EconCSLib/GameTheory/ExtensiveGame/GameTreeSPE.lean)

```lean
def Strategy (N U) := (m : N) → (h : GameTree N U) → (t : List (GameTree N U)) →
  { c : GameTree N U // c ∈ h :: t }
noncomputable def outcome (σ : Strategy N U) : GameTree N U → (N → U)
def optStrategy : Strategy N U          -- picks an argmax child at every node
def IVariant (i) (σ σ') : Prop          -- σ, σ' agree on every node with mover ≠ i
```

| name | Minimal assumptions | Meaning |
|------|--------------------|---------|
| `Strategy N U` | none | A **global** child-selector at every `(mover, head, tail)`, bundled with the membership proof. Covers all players at once. |
| `outcome σ g` | `[TotalPreorder U]` | The leaf payoff reached by following `σ` from `g` (well-founded on `size`). |
| `optStrategy` | `[TotalPreorder U]` | Canonical BI strategy: picks a child whose value equals the node's value. `noncomputable` (classical choice). |
| `IVariant i σ σ'` | none | `σ'` is a unilateral deviation by player `i` only. |
| `outcome_optStrategy_eq_value` | `[TotalPreorder U]` | the bridge: `outcome optStrategy g = value g`. |

A single `Strategy` is **player-agnostic** (one function for all movers); a
"player-`i` strategy" is conceptualised as its behaviour on `mover = i` nodes,
and `IVariant i` captures "change only player `i`'s choices". `outcome` is a
tree walk; `outcome_optStrategy_eq_value` is the load-bearing lemma that lets
every value fact transfer to an actual play.

---

## 4. Equilibrium and Kuhn's theorem

Files: [`GameTreeSPE.lean`](../../../EconCSLib/GameTheory/ExtensiveGame/GameTreeSPE.lean),
[`GameTreeNE.lean`](../../../EconCSLib/GameTheory/ExtensiveGame/GameTreeNE.lean)

```lean
def IsSubgamePerfect (σ) : Prop :=                 -- global: optimal at every tree
  ∀ g i σ', IVariant i σ σ' → outcome σ' g i ≤ outcome σ g i
def IsNashEquilibrium (σ) (g) : Prop :=            -- root-scoped (GameTreeNE)
  ∀ i σ', IVariant i σ σ' → outcome σ' g i ≤ outcome σ g i
def IsSubgamePerfectOn (σ) (g) : Prop :=           -- SPE on subgames of a fixed root
  ∀ s, Subtree s g → IsNashEquilibrium σ s
```

| name | Minimal assumptions | Meaning |
|------|--------------------|---------|
| `IsSubgamePerfect σ` | `[TotalPreorder U]` | No `i`-deviation improves `i` at **any** tree. Global (no root). |
| `IsNashEquilibrium σ g` | same | Same, but only at the fixed root `g`. Weaker — allows off-path threats. |
| `IsSubgamePerfectOn σ g` | same | NE at every subtree of `g`; `Iff.rfl`-equal to "∀ subtree, `IsNashAt`". |
| `optStrategy_isSubgamePerfect` | same | **The real Kuhn content**: `optStrategy` is an SPE. |
| `Kuhn_exists_SPE` | same | `∃ σ, IsSubgamePerfect σ` (existence form). |
| `Kuhn_exists_SPE_on g` / `Kuhn_exists_NE g` | same | root-scoped SPE / NE existence at `g`. |
| `IsSubgamePerfect.toNE` | same | SPE ⇒ NE (the classical one-way implication). |

`optStrategy_isSubgamePerfect` is proved by `strong_induction`: at a node owned
by the deviating player `i`, the deviation lands in some child where the IH plus
`value_Node_ge` caps it; at any other node, `IVariant` forces the same child and
the IH applies directly. Existence (`Kuhn_exists_SPE*`) is then immediate.
`GameTreeStrategicForm.lean` additionally bridges a tree to the normal-form
`StrategicGame` (`toStrategicGame`, `toStrategicGame_nash_iff_isNashAt`).

**Kuhn naming.** This is the backward-induction theorem (Kuhn 1953). The
behavioral-strategy Kuhn theorem is unrelated and lives on the Arena side.

---

## 5. Zero-sum specialization — Zermelo determinacy

File: [`Zermelo.lean`](../../../EconCSLib/GameTheory/ExtensiveGame/Zermelo.lean)

This is the only GameTree file that uses `ℚ`: zero-sum needs sums and negation.

```lean
def IsZeroSum : GameTree (Fin 2) ℚ → Prop        -- payoffs sum to 0 at every leaf
noncomputable def value₀ (g) : ℚ := (value g) 0  -- player 0's value
```

| name | Minimal assumptions | Meaning |
|------|--------------------|---------|
| `IsZeroSum g` | `Fin 2`, `ℚ` | `p 0 + p 1 = 0` at every leaf (propagated over the tree). |
| `IsZeroSum.of_subtree` | same | zero-sum is inherited by every subgame. |
| `value_zero_sum` | same | the BI value vector is zero-sum: `value g 0 + value g 1 = 0`. |
| `value_one_eq_neg_value₀` | same | `value g 1 = -value₀ g`. |
| `outcome_zero_sum` | same | **any** strategy's terminal outcome is zero-sum. |
| `value₀_Node_zero_isMax` / `value₀_Node_one_isMin` | same | player 0 maximizes `value₀` at their nodes; player 1 minimizes it at theirs. |
| `value₀_eq_outcome_and_zeroSum` | same | packaging: `optStrategy` realizes `value₀`, value vector is zero-sum. *Not* a minimax statement. |
| **`zermelo_determinacy`** | same | **determinacy / saddle value** (below). |
| `zermelo_exists_pure_SPE` / `_NE` | same | `Fin 2`/`ℚ` instances of Kuhn existence — **no** zero-sum hypothesis needed. |

```lean
theorem zermelo_determinacy (g : GameTree (Fin 2) ℚ) (hzs : IsZeroSum g) :
    (∀ σ', IVariant 1 optStrategy σ' → value₀ g ≤ outcome σ' g 0) ∧   -- P0 secures ≥ value₀
    (∀ σ', IVariant 0 optStrategy σ' → outcome σ' g 0 ≤ value₀ g)     -- P1 caps  ≤ value₀
```

`zermelo_determinacy` is **the genuine Zermelo content**: `optStrategy` is a
saddle point with value `value₀ g`. Player 0, playing `optStrategy`, secures at
least `value₀ g` against every opponent play; player 1, playing `optStrategy`,
holds player 0 to at most `value₀ g`. The two directions come from
`optStrategy_isSubgamePerfect` at `i = 1` and `i = 0` respectively, with the
player-0 side closing via `outcome_zero_sum` (`outcome σ' g 0 = -outcome σ' g 1`).

The split between the layers is the design point:

- existence of an equilibrium is **Kuhn**, needs only `[TotalPreorder U]`, and
  does *not* use zero-sum — hence `zermelo_exists_pure_SPE`/`_NE` carry no
  `IsZeroSum` hypothesis;
- the **value** being determined (a saddle) is **Zermelo**, and is exactly where
  the zero-sum hypothesis does real work.

---

## Relation to the Arena framework

`GameTree` is an inductive specialization for finite perfect-information games.
The `Arena` framework (`ExtensiveGame/{Basic,Strategy,Play,Subgame}.lean`) is a
state-space model that also represents infinite and imperfect-information games;
behavioral strategies, perfect recall, and the *behavioral* Kuhn theorem live
there (EG-L2). A future `Embedding.lean` is intended to bridge finite Arena →
GameTree. The two coexist on purpose; this note is only about the GameTree side.
