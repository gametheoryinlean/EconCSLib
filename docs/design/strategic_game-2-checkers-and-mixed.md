# StrategicGame — Checkers and Mixed Strategies

Continuation of [`strategic_game.md`](strategic_game.md). Covers the
executable `Prop`/`Bool` layer (§3) and the mixed-strategy layer (§4). For the
core model and pure-strategy concepts see the main file; for Nash existence and
the zero-sum / evolutionary tracks see
[`strategic_game-3-existence-and-zero-sum.md`](strategic_game-3-existence-and-zero-sum.md).

---

## 3. Decidable checkers

Files: [`Checker.lean`](../../../EconCSLib/GameTheory/StrategicGame/Checker.lean),
[`ZeroSum/Basic.lean`](../../../EconCSLib/GameTheory/StrategicGame/ZeroSum/Basic.lean)

§2 defined every solution concept as a `Prop`, with no finiteness and no
computation. This section is the *second layer*: turning those propositions into
`Bool`-valued checkers that actually run, plus the bridge lemma that proves the
checker agrees with the proposition.

### The Prop / Bool two-layer pattern

The rule (from `design.md` §2 and `CLAUDE.md`): for every decidable predicate
`IsX : Prop`, provide

1. a computable mirror `isX : Bool`, and
2. a soundness/completeness bridge `isX_iff : isX … = true ↔ IsX …`.

The `Prop` layer is the *meaning* (§2); the `Bool` layer is the *executable
witness*. They are kept separate on purpose: the `Prop` lives at the weakest
assumptions (`[Preorder U]`), and the `Bool` only appears once you add enough
finiteness/decidability to `decide` it. Downstream code proves things about
`IsX` but *runs* `isX` on concrete games.

### Nash checker

```lean
def isNashEq [Fintype N] (G : StrategicGame N U) [∀ i, Fintype (G.strategy i)]
    (σ : G.Profile) : Bool :=
  decide (∀ i : N, ∀ s' : G.strategy i, G.payoff (deviate σ i s') i ≤ G.payoff σ i)

theorem isNashEq_iff (G) (σ) : isNashEq G σ = true ↔ IsNashEquilibrium G σ
```

| name | Minimal assumptions | Meaning |
|------|--------------------|---------|
| `isNashEq G σ` | `[DecidableEq N] [Preorder U] [DecidableRel (·≤·)] [Fintype N] [∀ i, Fintype (G.strategy i)]` | Runs the pure-Nash test on a finite game. |
| `isNashEq_iff` (T6) | same | `isNashEq G σ = true ↔ IsNashEquilibrium G σ`. |

Three groups of assumptions stack here, and each earns its place:

- `[DecidableEq N] [Preorder U]` — inherited from the `Prop` (§2), needed to even
  *state* `IsNashEquilibrium`.
- `[DecidableRel (·≤·)]` — to decide each `≤` comparison on payoffs.
- `[Fintype N] [∀ i, Fintype (G.strategy i)]` — to turn the two `∀` quantifiers
  (over players, over deviations) into a finite `decide`.

The body is literally `decide (the unfolded IsNashEquilibrium)`, and
`isNashEq_iff` is one line: `simp [isNashEq, IsNashEquilibrium, IsBestResponse]`.
That brevity is the point — the bridge is trivial *because* the `Bool` is defined
as `decide` of exactly the proposition it mirrors. There is no separate algorithm
to keep in sync with the spec.

### Zero-sum is decidable too

```lean
instance IsZeroSum.decidable [Add U] [Zero U] [DecidableEq U]
    {G : StrategicGame (Fin 2) U} [∀ i, Fintype (G.strategy i)] :
    Decidable (IsZeroSum G) :=
  Fintype.decidableForallFintype
```

| name | Minimal assumptions | Meaning |
|------|--------------------|---------|
| `IsZeroSum.decidable` | `[Add U] [Zero U] [DecidableEq U] [∀ i, Fintype (G.strategy i)]` | `IsZeroSum G` is `decide`/`native_decide`-checkable (§6). |

Here the pattern is even lighter: instead of a hand-written `isZeroSum : Bool`,
the predicate `IsZeroSum G = ∀ σ, payoff σ 0 + payoff σ 1 = 0` is exposed as a
`Decidable` *instance* via `Fintype.decidableForallFintype`. Once Lean has the
instance, `decide` and `native_decide` work directly on `IsZeroSum G` with no
extra bridge lemma — the `Decidable` instance *is* the bridge. Note the
assumptions: only `[Add U] [Zero U] [DecidableEq U]`, far weaker than the
ordered-field assumptions the zero-sum *theorems* (§6) require.

### Why two layers instead of one

Why not just define everything as `Bool` from the start? Because the `Prop` is
the load-bearing object for *proofs*. `IsNashEquilibrium` is used in theorems
like `of_dominant`, `survives`, and `nash_iff_degenerate_ce` (§2) that hold over
arbitrary `[Preorder U]` — no finiteness in sight. If the definition were `Bool`,
every one of those theorems would drag in `[Fintype]`/`[DecidableRel]` it doesn't
need, and you could not state Nash for an infinite game at all. The `Bool` layer
is purely additive: execution on the finite fragment without contaminating the
general theory.

### Where this gets used: `native_decide` examples

The executable layer is what makes the `Examples/` developments self-checking.
`PrisonersDilemma.lean`, `RockPaperScissors.lean`, `TicTacToe.lean`, and
`SimpleAuction.lean` all use `native_decide` to verify concrete equilibrium /
zero-sum claims by compilation. This is also why the mixed layer (§4) is built on
`stdSimplex ℚ` rather than `ℝ`: `ℚ` has decidable equality and arithmetic, so
`native_decide` can evaluate a mixed-strategy example, while `ℝ` cannot be run.

---

## 4. Mixed strategies

File: [`MixedStrategy.lean`](../../../EconCSLib/GameTheory/StrategicGame/MixedStrategy.lean)

The pure layer (§1–§2) only ever compared payoffs with `≤`. The mixed layer is
the first place arithmetic enters in earnest: a mixed strategy is a *probability
distribution*, expected payoff is a *weighted sum of products*, and that forces a
field. This section covers how that field is kept polymorphic so the *same*
definitions serve both `ℚ` (executable) and `ℝ` (existence).

### The field-polymorphism contract

Every declaration in this file lives under one variable block:

```lean
variable {N U : Type*} [Field U] [LinearOrder U] [IsStrictOrderedRing U]
```

That triple — `[Field U] [LinearOrder U] [IsStrictOrderedRing U]` — is the
recurring "ordered field" hypothesis across the whole mixed/zero-sum stack. It is
the Mathlib-current replacement for the deprecated `[LinearOrderedField U]`. One
body of definitions then instantiates at:

- `U = ℚ` — decidable arithmetic, so `native_decide` can evaluate a concrete
  mixed equilibrium (the `Examples/` story, §3);
- `U = ℝ` — order completeness, needed for the Brouwer existence theorem (§5) and
  the Loomis minimax theorem (§6).

The Bourbaki point restated: `StrategicGame` and `MixedProfile` carry **no**
finiteness. `[Fintype N]` is added only to the definitions that genuinely sum
over players (expected payoff, mixed Nash) — never to the carrier types.

### Mixed strategies and profiles

```lean
abbrev MixedStrategy (G) (i) [Fintype (G.strategy i)] := stdSimplex U (G.strategy i)
def MixedProfile (G) [∀ i, Fintype (G.strategy i)] := ∀ i, MixedStrategy G i
```

| name | Minimal assumptions | Meaning |
|------|--------------------|---------|
| `MixedStrategy G i` | `[Field U] [LinearOrder U] [IsStrictOrderedRing U] [Fintype (G.strategy i)]` | A distribution over player `i`'s pure strategies. |
| `MixedProfile G` | `+ [∀ i, Fintype (G.strategy i)]` | One mixed strategy per player. |

A mixed strategy *is* a point of Mathlib's `stdSimplex U (G.strategy i)` — the
set of nonneg weight vectors summing to 1. We reuse `stdSimplex` rather than
rolling a bespoke distribution type so that all the convexity/topology lemmas
Mathlib already proves about the simplex are available for free (this is what
§5's continuity argument leans on). Note the asymmetry: `MixedStrategy` needs
`[Fintype (G.strategy i)]` (a single player's strategy set must be finite to be a
simplex), but `MixedProfile` still does **not** need `[Fintype N]` — the player
set may be arbitrary.

### Complete mixing

```lean
def IsCompletelyMixed (G : …ℚ) {i} [Fintype (G.strategy i)] (p : MixedStrategy G i) : Prop :=
  ∀ s : G.strategy i, 0 < p.val s
def IsCompletelyMixedProfile (G : …ℚ) [∀ i, Fintype (G.strategy i)] (p : MixedProfile G) : Prop :=
  ∀ i, IsCompletelyMixed G (p i)
```

| name | Minimal assumptions | Meaning |
|------|--------------------|---------|
| `IsCompletelyMixed G p` | specialized to `U = ℚ`, `[Fintype (G.strategy i)]` | Every pure strategy gets positive probability. (MSZ Def 7.6) |
| `IsCompletelyMixedProfile G p` | `+ [∀ i, Fintype (G.strategy i)]` | Every player is completely mixed. |

These are deliberately pinned to `U = ℚ`. Complete mixing is a notion the
*examples* track uses (support / trembling-hand style arguments), and those want
decidable `ℚ`. The general field-polymorphic definitions above do not need it, so
it stays narrow.

### Constructors

| name | Minimal assumptions | Meaning |
|------|--------------------|---------|
| `pureToMixed s₀` | `+ [DecidableEq (G.strategy i)]` | Point mass on `s₀`: weight `1` on `s₀`, `0` elsewhere. |
| `uniformMixed` | `+ [Nonempty (G.strategy i)]` | Uniform `1 / card` on every pure strategy. |
| `uniformMixedProfile G` | `[∀ i, Fintype] [∀ i, Nonempty]` | Every player plays uniform. |
| `pureProfileToMixed σ` | `[∀ i, Fintype] [∀ i, DecidableEq]` | Lift a pure profile to a (point-mass) mixed profile. |

Supporting lemmas (`uniformMixed_apply`, `uniformMixed_pos`,
`uniformMixed_isCompletelyMixed`, `uniformMixedProfile_isCompletelyMixed`,
`pureToMixed_not_isCompletelyMixed_of_ne`) establish the obvious facts: uniform
is positive everywhere hence completely mixed, and a point mass is *not*
completely mixed once a second strategy exists. `pureToMixed` is the bridge that
lets every pure-strategy result re-enter the mixed world as a degenerate
distribution.

### Expected payoff and pure-deviation Nash

```lean
def expectedPayoff (G) [Fintype N] [DecidableEq N] [∀ i, Fintype (G.strategy i)]
    (p : MixedProfile G) (who : N) : U :=
  ∑ σ : G.Profile, (∏ i : N, (p i).val (σ i)) * G.payoff σ who

def deviateMixed (G) … (p) (who) (s' : G.strategy who) : MixedProfile G :=
  Function.update p who (pureToMixed s')

def IsMixedNashEq (G) [Fintype N] … (p : MixedProfile G) : Prop :=
  ∀ (who) (s' : G.strategy who),
    expectedPayoff G (deviateMixed G p who s') who ≤ expectedPayoff G p who
```

| name | Minimal assumptions | Meaning |
|------|--------------------|---------|
| `expectedPayoff G p who` | `+ [Fintype N] [DecidableEq N]` | `∑_σ (∏_i p_i(σ_i)) · payoff(σ, who)`. |
| `deviateMixed G p who s'` | `+ [DecidableEq N] [∀ i, DecidableEq (G.strategy i)]` | `who` switches to *pure* `s'`, others keep their mix. |
| `IsMixedNashEq G p` | `+ [Fintype N] …` | No player gains by deviating to any pure strategy. (MSZ 5.5, 5.18) |

Two design choices worth flagging:

1. **`[Fintype N]` finally appears — and only here.** Expected payoff sums over
   *all* pure profiles (`∑ σ : G.Profile`), a product over players, so it
   genuinely needs the player set finite. This is the mixed-layer analogue of
   `welfare` in §1: the assumption lives with the operation that forces it.

2. **`IsMixedNashEq` only quantifies over *pure* deviations `s'`.** It does not
   say "no mixed deviation helps". That is sound because expected payoff is
   *linear* in `who`'s own mixed strategy, so the best mixed response is attained
   at a pure strategy — checking pure deviations suffices (MSZ 5.5, 5.18). This
   makes the predicate dramatically cheaper to check and is why `deviateMixed`
   deviates to a `pureToMixed s'` rather than an arbitrary `MixedStrategy`.

`IsMixedNashEq` here is the **pure-deviation** form, over an arbitrary ordered
field. §5's `mixedNashEquilibrium` is a *different*, ℝ-specific predicate that
quantifies over arbitrary mixed deviations `τ` — the two coincide by the same
linearity argument, but are stated separately because the existence proof needs
the mixed-deviation form.

### Take-aways for §3–§4

- The two-layer pattern: `Prop` at minimal assumptions (§2) + `Bool`/`Decidable`
  once finiteness is available + a one-line bridge that is trivial by
  construction. Decidability is the gateway to `native_decide`.
- One ordered-field hypothesis serves both the executable `ℚ` track and the
  existence `ℝ` track; `stdSimplex` is reused to inherit Mathlib's lemmas.
- `[Fintype N]` enters exactly at `expectedPayoff`. Pure-deviation Nash equals
  full mixed-deviation Nash by linearity; the cheaper pure form is the default.
