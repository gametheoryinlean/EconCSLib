# StrategicGame — Nash Existence, Zero-Sum, Evolutionary

Continuation of [`strategic_game.md`](strategic_game.md). Covers Nash existence
via the ℝ / Brouwer route (§5) and the zero-sum / evolutionary specialization
tracks (§6). For the core model and pure-strategy concepts see the main file;
for the decidable checkers and mixed-strategy layer see
[`strategic_game-2-checkers-and-mixed.md`](strategic_game-2-checkers-and-mixed.md).

---

## 5. Nash existence (the ℝ / Brouwer route)

File: [`Nash.lean`](../../../EconCSLib/GameTheory/StrategicGame/Nash.lean)

This is the one place in the strategic-game module that *commits to `ℝ`*.
Everything else is polymorphic; existence of a mixed Nash equilibrium needs a
fixed-point theorem, and the fixed-point theorem needs the topology of `ℝ`. The
file builds the best-response map, proves it continuous, and feeds it to Brouwer.

### Why `ℝ` here and nowhere else

```lean
variable (G : StrategicGame N ℝ)
variable [Fintype N] [DecidableEq N]
variable [∀ i, Fintype (G.strategy i)] [∀ i, DecidableEq (G.strategy i)]
variable [∀ i, Inhabited (G.strategy i)]
```

§4 kept `U` an arbitrary ordered field. Here `U` is fixed to `ℝ` from the first
line. The reason is singular: the proof is a fixed-point argument
(`Brouwer_Product`), and Brouwer needs a compact convex set in a
finite-dimensional *real* vector space plus a *continuous* self-map. `ℚ` has
neither completeness nor the topology, so the polymorphism of §4 has to stop at
the door of this file. Everything `ℚ`-flavoured (executable examples) stays in
§4's world; everything existence-flavoured lives here.

### Working with the raw product simplex

```lean
abbrev MixedS := ∀ i, stdSimplex ℝ (G.strategy i)
```

| name | Minimal assumptions | Meaning |
|------|--------------------|---------|
| `MixedS G` | the ℝ block above | Product of per-player standard simplices. |

Deliberately **not** `MixedProfile G` from §4 (even though they are defeq). It is
an `abbrev` over the raw `∀ i, stdSimplex ℝ …` so that Lean's typeclass search
finds the *product topology* automatically. A named `def` would hide the product
structure and break instance resolution for continuity. Small but load-bearing:
the existence proof is entirely about topology, so the type must wear its
topology on its sleeve.

### The payoff functional and best-response map

```lean
def evaluate_at_mixed (i) (σ : MixedS G) : ℝ := ∑ s : G.Profile, (∏ j, (σ j).val (s j)) * G.payoff s i
def mixed_g (i) (m : ∀ i, G.strategy i → ℝ) : ℝ := ∑ s, (∏ j, m j (s j)) * G.payoff s i
def g_function (i) (σ) (a) : ℝ := (σ i).val a + max 0 (evaluate_at_mixed G i (update σ i (pure a)) - evaluate_at_mixed G i σ)
def nash_map (σ : MixedS G) : MixedS G := fun i => ⟨nash_map_aux G σ i, nash_map_cert G σ i⟩
```

| name | Meaning |
|------|---------|
| `evaluate_at_mixed G i σ` | Player `i`'s expected payoff under mixed profile `σ`. |
| `mixed_g G i m` | Same multilinear sum on *un-normalized* weights `m`; the form continuity is proved on. |
| `g_function G i σ a` | `σ_i(a)` **plus** the positive part of the gain from deviating to pure `a`. |
| `nash_map G σ` | Normalize `g_function` over `a` to a mixed profile; the Brouwer self-map. |

The construction is the classic Nash 1951 map. `g_function` adds, to each pure
strategy's current weight, the "regret" `max 0 (gain from switching to a)`. Three
lemmas certify the normalization is well-defined:

| name | Meaning |
|------|---------|
| `sigma_le_g_function` | `σ_i(a) ≤ g_function i σ a` (adding a nonneg term). |
| `g_function_nonneg` | `0 ≤ g_function i σ a`. |
| `one_le_sum_g` | `1 ≤ ∑_a g_function i σ a` (so dividing by the sum is safe). |

`mixed_g` exists only as an intermediate: continuity is easiest to prove on the
un-normalized multilinear form, then transferred to `evaluate_at_mixed` via
`evaluate_at_mixed_eq_mixed_g`.

### Continuity and existence

```lean
theorem nash_map_cont : Continuous (nash_map G)
def mixedNashEquilibrium (G) … : MixedS G → Prop :=
  fun σ => ∀ i (τ : stdSimplex ℝ (G.strategy i)),
    evaluate_at_mixed G i (update σ i τ) ≤ evaluate_at_mixed G i σ
theorem exists_mixed_nash_equilibrium_finite (G) … [Inhabited N] :
    ∃ σ : MixedS G, mixedNashEquilibrium G σ
```

| name | Minimal assumptions | Meaning |
|------|--------------------|---------|
| `nash_map_cont` | ℝ block | `nash_map G` is a continuous self-map of `MixedS G`. |
| `mixedNashEquilibrium G σ` | `[Fintype N] [∀ i, Fintype (G.strategy i)]` | No player improves by deviating to any **mixed** strategy `τ`. |
| `exists_mixed_nash_equilibrium_finite` | `+ [DecidableEq N] [∀ i, DecidableEq] [∀ i, Inhabited] [Inhabited N]` | Every finite n-player game has a mixed Nash equilibrium. |

Two things to note about the existence theorem:

1. **`mixedNashEquilibrium` is the mixed-deviation form** — it quantifies over
   arbitrary `τ : stdSimplex`, not just pure deviations like §4's `IsMixedNashEq`.
   The proof produces a fixed point of `nash_map`, and reading Nash off a fixed
   point naturally gives the mixed-deviation statement. The two forms agree by
   linearity (§4), but the existence proof speaks this one.

2. **The proof is "transport to `Fin n`, Brouwer, transport back".** Per the
   source docstring: reindex players as `Fin n` and strategies by cardinality,
   land in a `ProductSimplices`, apply `Brouwer_Product` (from
   `Math/FixedPoint/Brouwer_product`) to get a fixed point, transport back along
   the equivalences, then use the fixed-point equation `nash_map σ = σ` together
   with `wsum_magic_ineq` (a weighted-average lemma) to certify no profitable
   deviation. The extra `[Inhabited]` assumptions are what make the reindexing
   total.

`Brouwer_Product` lives in the `Math/` layer
([`Math/FixedPoint/Brouwer_product`](../../../EconCSLib/Math/FixedPoint/Brouwer_product.lean)),
not here. That is the layering rule (`design.md` §2) at work: the fixed-point
theorem is *reusable mathematics*, so it belongs in `Math/`; this file is the
*domain application* that wires a game's best-response map into it. The
strategic-game module imports `Math`, never the reverse.

---

## 6. Zero-sum and evolutionary tracks

Files: [`ZeroSum/`](../../../EconCSLib/GameTheory/StrategicGame/ZeroSum/),
[`ESS.lean`](../../../EconCSLib/GameTheory/StrategicGame/ESS.lean)

The two "specialization" tracks: zero-sum games (where the general-game machinery
collapses into the cleaner minimax/value theory) and evolutionary games (a
different equilibrium notion on symmetric games). This is a *survey with
pointers* — each sub-area has its own source docstrings and, where relevant, its
own knowledge node. The goal here is the map, not every signature.

### Zero-sum predicates on a two-player game

File: [`ZeroSum/Basic.lean`](../../../EconCSLib/GameTheory/StrategicGame/ZeroSum/Basic.lean)

```lean
def IsZeroSum [Add U] [Zero U] (G : StrategicGame (Fin 2) U) : Prop
def IsConstantSum [Add U] (G : StrategicGame (Fin 2) U) (c : U) : Prop
```

| name | Minimal assumptions | Meaning |
|------|--------------------|---------|
| `IsZeroSum G` | `[Add U] [Zero U]` | `payoff σ 0 + payoff σ 1 = 0` for all `σ`. |
| `IsConstantSum G c` | `[Add U]` | The two payoffs always sum to a constant `c`. |
| `IsZeroSum.decidable` | `+ [DecidableEq U] [∀ i, Fintype (G.strategy i)]` | `decide`/`native_decide` checkable (§3). |
| `IsZeroSum.nash_payoff_eq` (`[MSZ 4.44]`) | `[Field U] [LinearOrder U] [IsStrictOrderedRing U]` | All Nash equilibria give player 0 the same payoff. |

The same layering discipline as everywhere else: the *predicates* sit at
`[Add U] [Zero U]` (almost nothing), the decidability instance adds finiteness,
and only the *value/interchangeability theorems* (`nash_payoff_eq`,
`nash_payoff_eq_p1`, `expectedPayoff_neg`, …) step up to the ordered field.
`IsZeroSum ⇄ IsConstantSum 0` is bridged by `isZeroSum_iff_isConstantSum_zero`.

### Matrix games: the value-theory core

File: [`ZeroSum/MatrixGame.lean`](../../../EconCSLib/GameTheory/StrategicGame/ZeroSum/MatrixGame.lean)

```lean
structure MatrixGame (I J : Type*) (𝕜 : Type := ℚ) where
  g : I → J → 𝕜
```

A `MatrixGame` is *its own structure*, separate from `StrategicGame`. It is just
a payoff matrix `g : I → J → 𝕜`, with `𝕜` defaulting to `ℚ`. Why a second
structure rather than a specialized `StrategicGame (Fin 2)`? Because the zero-sum
value theory is naturally stated on a single matrix from player I's perspective
(player II minimizes the same number player I maximizes), and a one-matrix
encoding makes the maximin/minimax duality direct instead of threading two payoff
columns.

The arithmetic layer is field-generic
(`[Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]`):

| name | Meaning |
|------|---------|
| `payoffAgainstColumn x j`, `payoffAgainstRow i y` | mixed-vs-pure dot products. |
| `expectedPayoff x y`, `E x y` | mixed-vs-mixed expected payoff. |
| `Ej x j`, `Ei i y` | shorthand for the two mixed-vs-pure forms. |
| `guarantee_I x`, `guarantee_II y` | the `inf'`/`sup'` a mixed strategy guarantees. |
| `IsMaximin A v`, `IsMinimax A v`, `IsValue A v` | value predicates (existence + extremality / saddle form). |

`IsMaximin/IsMinimax/IsValue` are **inequality predicates only**, so they live at
the Layer-2 ordered-field hypotheses and work over `ℚ`, `ℝ`, any ordered field —
even where the `sSup`-based `maximin`/`minimax` (which need order completeness)
are unavailable. The headline results `minimax_theorem` (`maximin = minimax`),
`nash_value_unique`, and `nash_interchangeable` are the von Neumann minimax
theorem and its corollaries, aliased from the simplified Loomis development.

### Minimax and Nash over any ordered field (symmetrisation route)

The `minimax_theorem` above is ℝ-only (the Loomis route uses compactness /
continuity). The **field-generic** von Neumann minimax lives in `Math/Minimax/`
and needs no order-completeness and no compactness:

- `Minimax.minimax (A : I → J → 𝕜)` — over any `[Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜]`: `∃ x ∈ Δ(I), y ∈ Δ(J), v`, with `xA ≥ v` and
  `Ay ≤ v` (the **existence / saddle form** — the value `v` is carried as
  field data, never an `iSup`; see the existence-form-over-`iSup` rationale).
  Proof: **von Neumann symmetrisation**. Shift the game positive, embed it into
  the skew-symmetric matrix `S` on `I ⊕ J ⊕ Unit`, and read `(x, y, v)` off
  `S`'s value-0 optimal strategy (`SkewSymmetric.optimal`). That optimal
  strategy exists as a pure **feasibility** fact via the Theorem of the
  Alternative (`Math/LinearAlgebra/FourierMotzkin.lean`): a Farkas certificate
  would give `w ≥ 0, w ≠ 0, S w < 0`, contradicting the skew identity
  `wᵀ S w = 0`. No "LP optimum attained" lemma is needed — routing through a
  skew game (whose value is `0` a priori) is exactly what avoids it.
- `MatrixGame.exists_mixed_nash_equilibrium` (`MatrixGameNash.lean`) is now
  **field-generic too**: it packages `Minimax.minimax`'s saddle into the
  `IsMixedNashEq` form via `isMixedNashEq_of_pure`. So *"a finite zero-sum
  matrix game has a mixed Nash equilibrium"* is a theorem over **any** linearly
  ordered field, not only ℝ; the ℝ consumers are the `𝕜 := ℝ` instance.

Two parallel minimax routes coexist by design — neither subsumes the other:

| route | field | `B` |
|-------|-------|-----|
| `Loomis` (`Loomis.lean`, `minmax_from_general`) | ℝ only (compactness) | general positive `B` |
| `Minimax.minimax` (`Minimax.lean`) | any ordered field | `B = 𝟙` |

The ℝ `B = 𝟙` minimax sits at the intersection and is taken, by choice, as the
corollary of the ℝ Loomis theorem (`Loomis.minmax_from_general`), keeping
`Loomis` the canonical ℝ value-theory. `MinimaxLoomis.lean` holds the shared
ℝ value-form scaffold (`lam0`/`mu0` aggregates, drop/extend infra).

### The rest of `ZeroSum/` — pointers

| File | What it adds |
|------|-------------|
| [`MatrixGameNash.lean`](../../../EconCSLib/GameTheory/StrategicGame/ZeroSum/MatrixGameNash.lean) | `IsSaddlePoint`, `isMixedNashEq_iff_isSaddlePoint`, optimal row/column strategy sets, ε-optimality, support complementarity, `value_eq_maximin`/`value_eq_minimax`. |
| [`OptimalStrategySetPolytope.lean`](../../../EconCSLib/GameTheory/StrategicGame/ZeroSum/OptimalStrategySetPolytope.lean) | The optimal-strategy sets are convex, closed, compact, nonempty, and polytopes. |
| [`Antisymmetric.lean`](../../../EconCSLib/GameTheory/StrategicGame/ZeroSum/Antisymmetric.lean) | `IsAntisymmetric B` (`B i j = -B j i`); symmetric games have value 0 and a symmetric optimal strategy. |
| [`StochasticMatrix.lean`](../../../EconCSLib/GameTheory/StrategicGame/ZeroSum/StochasticMatrix.lean) | `IsStochasticMatrix`; existence of an invariant distribution. |
| [`StrongComplementarity.lean`](../../../EconCSLib/GameTheory/StrategicGame/ZeroSum/StrongComplementarity.lean) | existence of a strongly complementary optimal pair. |
| [`Learning/`](../../../EconCSLib/GameTheory/StrategicGame/ZeroSum/Learning/) | `IsFictitiousPlay`, Robinson's `AdmissibleSequence` + convergence (Cesàro/continuity/convergence), the learning-dynamics track. |
| [`Approachability/`](../../../EconCSLib/GameTheory/StrategicGame/ZeroSum/Approachability/) | Blackwell approachability. |

Most of these rest on the `Math/` layer (minimax via Loomis / symmetrisation, LP duality,
Farkas) rather than re-deriving anything — the layering rule again: reusable
mathematics in `Math/`, game-specific wiring here.

### Evolutionary stability

File: [`ESS.lean`](../../../EconCSLib/GameTheory/StrategicGame/ESS.lean)

```lean
def IsESS {S : Type*} (u : S → S → ℝ) (s : S) : Prop :=
  (∀ t, u s s ≥ u t s) ∧ (∀ t, u s s = u t s → s ≠ t → u s t > u t t)
def IsNSS {S : Type*} (u : S → S → ℝ) (s : S) : Prop :=
  (∀ t, u s s ≥ u t s) ∧ (∀ t, u s s = u t s → u s t ≥ u t t)
```

| name | Minimal assumptions | Meaning |
|------|--------------------|---------|
| `IsESS u s` | `u : S → S → ℝ` only | Nash condition **+** strict invasion barrier. |
| `IsNSS u s` | same | Neutrally stable: invasion barrier with `≥` instead of `>`. |
| `IsESS.isNSS` | same | ESS ⇒ NSS. |
| `strict_nash_implies_ess` | same | A strict symmetric Nash is automatically ESS. |
| `IsESS.nash_condition` (`[MSZ 5.51]`) | same | ESS satisfies the symmetric Nash condition. |
| `IsESS.strict_against_other` | same | Distinct ESS are strictly separated. |

ESS departs from the rest of the module in two ways:

1. **It is stated on a bare payoff function `u : S → S → ℝ`, not a
   `StrategicGame`.** Evolutionary stability is about a *symmetric* two-player
   interaction, fully captured by `u s t` = payoff to an `s`-player meeting a
   `t`-player. Wrapping it in `StrategicGame` would add nothing, so per the
   "stable predicates over placeholder abstractions" rule it stays a predicate
   on `u`.

2. **It hard-codes `ℝ`** rather than being field-polymorphic. The two-clause
   definition (Nash condition + strict invasion barrier with `>`) is naturally
   real-valued and the track currently has no `ℚ`/executable ambitions, so the
   extra polymorphism would be speculative.

### Take-aways for §5–§6

- `ℝ` is forced **only** by the fixed-point argument; existence = continuous Nash
  map + Brouwer, with the fixed-point theorem factored into the reusable `Math/`
  layer. `MixedS` is a raw `abbrev` so the product topology is found
  automatically.
- Zero-sum collapses the n-player machinery into matrix-game value theory; the
  predicates stay cheap (`[Add] [Zero]`), value theorems step up to an ordered
  field, and order-completeness is isolated to the `sSup`-based `maximin/minimax`.
- ESS lives on a bare `u : S → S → ℝ` (no `StrategicGame`, no field
  polymorphism).
