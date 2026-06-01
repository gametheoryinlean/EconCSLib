# StrategicGame — API Design

Developer-facing design notes for `EconCSLib/GameTheory/StrategicGame/`:
**how the Lean API is built** — what the data structures are, where each
typeclass assumption enters, and why the module is layered the way it is.

This is the module's main file. Two continuation files carry the later
topics; they exist only because a single file would run past ~300 lines:

- **This file** — overview, the core `StrategicGame` model (§1), and the
  pure-strategy solution concepts (§2).
- [`strategic_game-2-checkers-and-mixed.md`](strategic_game-2-checkers-and-mixed.md)
  — decidable `Prop`/`Bool` checkers (§3) and the mixed-strategy layer (§4).
- [`strategic_game-3-existence-and-zero-sum.md`](strategic_game-3-existence-and-zero-sum.md)
  — Nash existence via Brouwer (§5) and the zero-sum / evolutionary tracks (§6).

Part of the [design documentation set](README.md). These notes complement,
they do not replace:

- [`docs/design.md`](../design.md) — project-wide architecture and rules.
- [`docs/research/design_decisions.md`](../research/design_decisions.md)
  — dated rationale for individual choices.
- `docs/knowledge/` — the published mathematical blueprint (the *textbook*
  layer; these notes are the *API* layer).

## Design principles that shape everything here

1. **Bourbaki discipline — structures hold data, not assumptions.**
   `StrategicGame` has *zero* typeclass constraints; `[Fintype]`,
   `[DecidableEq]`, order, and algebra are attached at the theorem or
   definition that needs them. Every "minimal assumptions" column below shows
   exactly where a constraint enters.
2. **Two-layer `Prop` / `Bool`.** Every decidable `IsX : Prop` gets a
   computable mirror `isX : Bool` and a bridge `isX_iff` (File 2, §3).
3. **Game-bound profiles.** A profile is `G.Profile = ∀ i, G.strategy i`;
   solution concepts are predicates on it, not a standalone profile API (§1).
4. **Field polymorphism for the mixed layer.** Mixed strategies live under
   `[Field U] [LinearOrder U] [IsStrictOrderedRing U]`, so one body of
   definitions serves `ℚ` (executable, `native_decide`) and `ℝ`
   (existence / minimax). See File 2 §4 and File 3 §5.

## Module map

```
GameTheory/StrategicGame/
  Basic.lean              -- StrategicGame, Profile, deviate, welfare        (§1)
  BestResponse.lean       -- IsBestResponse                                  (§2)
  Dominance.lean          -- weak/strict dominance, dominant strategies      (§2)
  NashEquilibrium.lean    -- IsNashEquilibrium                               (§2)
  IESDS.lean              -- iterated strict dominance, rationalizability    (§2)
  PotentialGame.lean      -- exact / ordinal potential                       (§2)
  CorrelatedEq.lean       -- degenerate correlated equilibrium               (§2)
  Checker.lean            -- isNashEq + isNashEq_iff                         (File 2 §3)
  MixedStrategy.lean      -- MixedStrategy/Profile, expectedPayoff, mixed NE (File 2 §4)
  Nash.lean               -- nash_map, Brouwer existence                     (File 3 §5)
  ESS.lean                -- evolutionarily / neutrally stable strategies    (File 3 §6)
  ZeroSum/                -- zero-sum, matrix games, minimax, learning       (File 3 §6)
```

Conventions: `[MSZ X.Y]` = Maschler/Solan/Zamir, *Game Theory* (Cambridge,
2013); `[AGT Ch.Z]` = Nisan/Roughgarden/Tardos/Vazirani. "Minimal
assumptions" lists the typeclasses a declaration *itself* needs on top of the
always-present `{N U : Type*}`. Signatures are abbreviated; the source file is
authoritative.

---

## 1. Core model

File: [`Basic.lean`](../../../EconCSLib/GameTheory/StrategicGame/Basic.lean)

One data structure and the three pieces of vocabulary that travel with it:
profiles, unilateral deviation, and welfare.

### The `StrategicGame` structure

```lean
structure StrategicGame (N : Type*) (U : Type*) where
  strategy : N → Type*                       -- each player's strategy space
  payoff   : (∀ i, strategy i) → N → U       -- profile ↦ per-player utility
```

| Field / def | Minimal assumptions | Meaning |
|-------------|--------------------|---------|
| `StrategicGame N U` | **none** | A normal-form game: player type `N`, utility type `U`. |
| `strategy : N → Type*` | none | Strategy space *per player* — a dependent family. |
| `payoff` | none | Maps a full strategy profile to each player's utility. |

**Design rationale (Bourbaki discipline).**

- `N` (players) and `U` (utilities) are completely unconstrained. No
  `Fintype`, no `DecidableEq`, no order, no `ℝ`. A game is *data*; everything
  computational or order-theoretic is a hypothesis at the use site.
- `strategy` is a **dependent** family `N → Type*`, so different players may
  have genuinely different strategy spaces. A two-player game where one player
  picks a `Fin 3` and the other a `Bool` is expressible directly.
- `payoff` returns utilities for *every* player given the full profile — the
  normal-form payoff matrix in function form.

### Profiles are game-bound

```lean
abbrev Profile (G : StrategicGame N U) := ∀ i, G.strategy i
```

A profile belongs to a specific game. This is the deliberate "Option C" choice
(`design_decisions.md`, 2026-04-02): solution concepts are predicates on
`G.Profile` rather than an abstract free-standing profile type. Coupling the
profile to `G` keeps everything that depends on `G.strategy` in one place and
lets dot-notation (`G.payoff σ i`) read naturally.

> A legacy abstract profile (`Profile N S` over a bare strategy family) still
> exists in `Foundation/Profile.lean` as a compatibility shim with its own
> `deviate`. Strategic-game code uses `G.Profile`.

### Unilateral deviation

```lean
abbrev deviate {G} [DecidableEq N] (σ : G.Profile) (i : N) (s' : G.strategy i) : G.Profile :=
  Function.update σ i s'

notation:max σ "[" i " ↦ " s "]" => StrategicGame.deviate σ i s
```

| def / lemma | Minimal assumptions | Meaning |
|-------------|--------------------|---------|
| `deviate σ i s'` | `[DecidableEq N]` | Player `i` switches to `s'`; everyone else unchanged. |
| `deviate_self` | `[DecidableEq N]` | `σ[i ↦ σ i] = σ`. (`@[simp]`) |
| `deviate_same` | `[DecidableEq N]` | `σ[i ↦ s'] i = s'`. (`@[simp]`) |
| `deviate_of_ne` | `[DecidableEq N]` | `j ≠ i → σ[i ↦ s'] j = σ j`. (`@[simp]`) |

`deviate` is literally `Function.update`. The only assumption it forces is
`[DecidableEq N]` (to decide "is this player `i`?"). The three `@[simp]` lemmas
are the entire algebraic interface downstream proofs rely on — best response,
dominance, and IESDS all reduce deviation reasoning to these three rewrites.

The `σ[i ↦ s']` notation is defined, but the codebase writes `deviate σ i s'`
(or `G.payoff (deviate σ i s') i`) almost everywhere. Treat the bracket form as
documentation sugar; prefer the explicit `deviate` spelling in new code.

### Welfare

```lean
noncomputable def welfare [Fintype N] [AddCommMonoid U]
    (G : StrategicGame N U) (σ : G.Profile) : U := ∑ i, G.payoff σ i
```

| def | Minimal assumptions | Meaning |
|-----|--------------------|---------|
| `welfare G σ` | `[Fintype N] [AddCommMonoid U]` | Sum of all players' payoffs at `σ`. |

This is the first place finiteness and additive structure appear — and they
appear *only here*, because summing over players needs `[Fintype N]` and
`[AddCommMonoid U]`. Nothing upstream (structure, profiles, deviation) pays for
them. The layering principle in miniature: the assumption lives with the
operation that requires it.

---

## 2. Pure-strategy solution concepts

Files: [`BestResponse.lean`](../../../EconCSLib/GameTheory/StrategicGame/BestResponse.lean),
[`Dominance.lean`](../../../EconCSLib/GameTheory/StrategicGame/Dominance.lean),
[`NashEquilibrium.lean`](../../../EconCSLib/GameTheory/StrategicGame/NashEquilibrium.lean),
[`IESDS.lean`](../../../EconCSLib/GameTheory/StrategicGame/IESDS.lean),
[`PotentialGame.lean`](../../../EconCSLib/GameTheory/StrategicGame/PotentialGame.lean),
[`CorrelatedEq.lean`](../../../EconCSLib/GameTheory/StrategicGame/CorrelatedEq.lean)

Every concept here is a **predicate on `G.Profile`** (or on a single strategy).
None require finiteness or computability — only an order on `U`. This is the
"stable predicates over placeholder abstractions" rule: an equilibrium *is* a
proposition about a profile, so it is defined as one. The whole layer needs
only `[DecidableEq N]` (for `deviate`) and `[Preorder U]` (to compare payoffs).

### Best response

```lean
def IsBestResponse (G) (σ : G.Profile) (i : N) : Prop :=
  ∀ s' : G.strategy i, G.payoff (deviate σ i s') i ≤ G.payoff σ i
```

| name | Minimal assumptions | Meaning |
|------|--------------------|---------|
| `IsBestResponse G σ i` | `[DecidableEq N] [Preorder U]` | No unilateral deviation by `i` raises `i`'s payoff. |
| `IsBestResponse.congr_payoff` | same | Best response depends only on player `i`'s payoff column. |

`congr_payoff` is the first structural lemma: `IsBestResponse` is invariant
under changing any payoff *other than player `i`'s own*. This lets later proofs
swap payoff functions freely as long as the `i`-th column is preserved.

### Dominance

```lean
def WeaklyDominates   (G) (i) (s s' : G.strategy i) : Prop := ∀ σ, payoff (σ[i↦s']) i ≤ payoff (σ[i↦s]) i
def StrictlyDominates (G) (i) (s s' : G.strategy i) : Prop := ∀ σ, payoff (σ[i↦s']) i < payoff (σ[i↦s]) i
def IsWeaklyDominant   (G) (i) (s) : Prop := ∀ s', WeaklyDominates G i s s'
def IsStrictlyDominant (G) (i) (s) : Prop := ∀ s', s ≠ s' → StrictlyDominates G i s s'
```

| name | Minimal assumptions | Meaning |
|------|--------------------|---------|
| `WeaklyDominates G i s s'` | `[DecidableEq N] [Preorder U]` | `s` is `≥` `s'` against every opponent profile. |
| `StrictlyDominates G i s s'` | same | `s` is `>` `s'` against every opponent profile. |
| `IsWeaklyDominant G i s` | same | `s` weakly dominates *every* alternative. |
| `IsStrictlyDominant G i s` | same | `s` strictly dominates every *distinct* alternative. |
| `StrictlyDominates.weakly` | same | strict ⇒ weak (pointwise). |
| `IsStrictlyDominant.isWeaklyDominant` | `+ [DecidableEq (G.strategy i)]` | strict dominant ⇒ weakly dominant. |
| `IsWeaklyDominant.isBestResponse` (T2) | base | a weakly dominant strategy is a best response wherever `i` plays it. |

Note the asymmetry: `IsStrictlyDominant` carries the `s ≠ s'` side condition (a
strategy can't strictly beat *itself*), while `IsWeaklyDominant` does not. That
is why upgrading strict-dominant to weakly-dominant needs
`[DecidableEq (G.strategy i)]` — to case on `s = s'`.

### Pure Nash equilibrium

```lean
def IsNashEquilibrium (G) (σ : G.Profile) : Prop := ∀ i : N, IsBestResponse G σ i
```

| name | Minimal assumptions | Meaning |
|------|--------------------|---------|
| `IsNashEquilibrium G σ` | `[DecidableEq N] [Preorder U]` | Every player is best-responding; no profitable unilateral deviation. |
| `IsNashEquilibrium.of_dominant` (T3) | same | If each player has a weakly dominant strategy and `σ` assigns it, `σ` is Nash. |

Nash is the *conjunction over players* of `IsBestResponse`. There is no separate
equilibrium structure — the predicate composed up from best response *is* the
definition. `of_dominant` chains T2 across all players.

### IESDS and rationalizability

```lean
def Survives (G) : ℕ → (i : N) → G.strategy i → Prop
  | 0     => fun _ _ => True
  | n + 1 => fun i s => G.Survives n i s ∧
      ¬ ∃ t, G.Survives n i t ∧
        ∀ σ, (∀ j, G.Survives n j (σ j)) →
          G.payoff (deviate σ i s) i < G.payoff (deviate σ i t) i
```

| name | Minimal assumptions | Meaning |
|------|--------------------|---------|
| `Survives G n i s` | `[DecidableEq N] [Preorder U]` | `s` survives `n` rounds of iterated strict-dominance elimination. |
| `Survives.prev`, `Survives.mono` | same | survival is downward-closed / monotone in the round index. |
| `IsRationalizable G i s` | same | survives *all* rounds: `∀ n, Survives G n i s`. |
| `IsNashEquilibrium.survives` (`[MSZ 4.31]`) | same | Nash strategies survive every round. |
| `IsNashEquilibrium.isRationalizable` | same | Nash strategies are rationalizable. |
| `IsDominanceSolvable G` | same | IESDS leaves a *unique* surviving profile. |
| `dominance_solvable_unique_nash` (`[MSZ 4.37]`) | same | that unique survivor is the unique Nash equilibrium. |

`Survives` is a recursion on the round count: round 0 keeps everything, round
`n+1` keeps a strategy iff it survived round `n` **and** is not strictly
dominated *by another round-`n` survivor, against opponent profiles all of whose
strategies also survived round `n`*. That restriction to surviving opponents is
the subtle part — it makes IESDS the standard iterated-elimination process
rather than a one-shot dominance check.

### Potential games

```lean
def IsExactPotential   (G) (Φ : G.Profile → U) : Prop  -- ΔΦ = Δ(payoff) for unilateral moves
def IsOrdinalPotential (G) (Φ : G.Profile → U) : Prop  -- sign(ΔΦ) = sign(Δ payoff)
```

| name | Minimal assumptions | Meaning |
|------|--------------------|---------|
| `IsExactPotential G Φ` | `[DecidableEq N] [Sub U] [Preorder U]` | A potential whose change equals the deviating player's payoff change. |
| `IsOrdinalPotential G Φ` | same | A potential that agrees with payoff change only in *sign*. |
| `IsExactPotential.maximizer_is_nash` | `+ [Field U] [LinearOrder U] [IsStrictOrderedRing U]` | A potential-maximizing profile is Nash. |
| `IsOrdinalPotential.isNash_iff_localMax` | same | Nash ⇔ local maximizer of an ordinal potential. |

The two theorem statements step up to an ordered field; the *definitions*
deliberately stay at `[Sub U] [Preorder U]` so the notion of a potential is
available even when the downstream maximizer theorems are not.

### Correlated equilibrium (degenerate case)

```lean
def IsDegenerateCorrelatedEq (G) (σ : G.Profile) : Prop
```

| name | Minimal assumptions | Meaning |
|------|--------------------|---------|
| `IsDegenerateCorrelatedEq G σ` | `[DecidableEq N] [Preorder U]` | The point-mass correlated equilibrium supported on `σ`. |
| `nash_iff_degenerate_ce` | same | A profile is a degenerate CE iff it is a pure Nash equilibrium. |

This is the entry point of the correlated-equilibrium track: it pins down the
degenerate (single-profile) case and proves it coincides with pure Nash, so the
general mediated/correlated theory can layer on later without re-deriving the
base case.

### Take-aways for §1–§2

- One structure, zero constraints; deviation is `Function.update` + three
  `simp` lemmas — the workhorse for every pure-strategy concept.
- Everything in §2 is a `Prop` on `G.Profile`, needing only
  `[DecidableEq N] [Preorder U]`; File 2 §3 makes some of them executable.
- Recurring move: definitions sit at the weakest order assumption; only the
  theorems that need arithmetic step up to an ordered field.
