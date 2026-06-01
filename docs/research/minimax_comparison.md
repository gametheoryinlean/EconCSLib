# Minimax Theorem: math-xmum vs elazarg Comparison

## Overview

| | math-xmum/gametheory | elazarg/GameTheory |
|---|---|---|
| **File** | `Zerosum.lean` (829 lines) | `Theorems/Minimax.lean` (~140 lines) |
| **Placeholders** | 0 | 0 |
| **Proof method** | Loomis's approach (strong induction on |I|+|J|) | Reduces to Nash existence via Brouwer |
| **Reference** | Laraki, Renault, Sorin [LRS] Theorem 2.3.1 | — |
| **Self-contained?** | Mostly (imports Simplex.lean for `S I` type) | No — imports `NashExistenceMixed` (Brouwer chain) |
| **Lean version** | v4.24.0-rc1 | v4.27.0 |

## Architecture Comparison

### math-xmum: Direct proof of minimax equality

```
zerosumGame (I J : Type*)     -- payoff matrix g : I → J → ℝ
  ↓
S I = stdSimplex ℝ (Fin |I|)  -- mixed strategies (from Simplex.lean)
  ↓
E A x y                       -- expected payoff = ∑_i ∑_j x(i) y(j) A(i,j)
  ↓
lam.aux A x = inf_j E(A,x,j)  -- worst-case for player I using x
lam0 A = sup_x lam.aux(A,x)   -- maximin value
mu.aux A y = sup_i E(A,i,y)    -- best-case for player II using y
mu0 A = inf_y mu.aux(A,y)      -- minimax value
  ↓
PROVE: lam0 A = mu0 A          -- the minimax equality (Loomis method)
  ↓
minmax_theorem: ∃ xx yy v, (∀ y, E(A,xx,y) ≥ v) ∧ (∀ x, E(A,x,yy) ≤ v)
```

**Proof of `lam0 = mu0`**: Strong induction on `n = |I| + |J|`.
- Base case: `|I| = |J| = 1` — trivial.
- Inductive case: Assume `lam0 < mu0`, derive contradiction.
  If some column `j₀` has slack (`E(xx, j₀) > lam0`), remove it to get a
  smaller game, apply IH, then show a convex combination contradicts the
  definition of lam0 as a supremum.

### elazarg: Minimax as corollary of Nash existence

```
KernelGame (Fin 2)            -- 2-player kernel game
  ↓
IsZeroSum G                   -- ∀ ω, utility ω 0 + utility ω 1 = 0
  ↓
mixed_nash_exists G           -- Nash exists (from Brouwer, separate module)
  ↓
nash_eu_eq                    -- all Nash have same EU (zero-sum property)
  ↓
von_neumann_minimax: ∃ v σ, Nash σ ∧ EU(σ,0) = v ∧ guarantees
```

**Proof of `von_neumann_minimax`**:
1. Get Nash equilibrium from `mixed_nash_exists` (Brouwer)
2. Zero-sum → deviating player 1 can't decrease player 0's EU
3. Nash → deviating player 0 can't increase player 0's EU
4. So `v = EU(σ, 0)` is the value, and `σ` provides the guarantees

## Detailed Comparison

### Definitions

| Concept | math-xmum | elazarg | Notes |
|---------|-----------|---------|-------|
| Game | `zerosumGame I J` with `g : I → J → ℝ` | `KernelGame (Fin 2)` with `IsZeroSum` | math-xmum: dedicated type; elazarg: predicate on general game |
| Mixed strategy | `S I` = stdSimplex ℝ (custom) | `PMF (Strategy i)` | math-xmum: custom simplex; elazarg: Mathlib PMF |
| Expected payoff | `E A x y` = bilinear form | `eu σ i` = kernel expectation | math-xmum: direct sum; elazarg: via stochastic kernel |
| Maximin/minimax | `lam0`, `mu0` via `iSup`/`iInf` | Not defined (uses Nash directly) | math-xmum defines these explicitly |
| Value | Implicit in `lam0 = mu0` | Implicit in Nash EU | |

### Proof Approach

| Aspect | math-xmum (Loomis) | elazarg (via Nash) |
|--------|--------------------|--------------------|
| **Core idea** | Direct: induction on game size | Indirect: minimax = corollary of Nash |
| **Dependency** | Self-contained (no fixed-point theorem needed) | Needs Brouwer → Nash existence |
| **Lines of proof** | ~600 (proof of `minmax'`) | ~30 (`von_neumann_minimax`) |
| **Supporting lemmas** | ~200 lines of analysis (continuity, convexity) | Reuses `NashExistenceMixed` (~500 lines) |
| **Total effort** | 829 lines | ~140 + ~500 (Nash existence) = ~640 lines |
| **Conceptual** | Constructive feel (builds optimal strategies) | Non-constructive (existence via Brouwer) |
| **Generality** | Works for any `I J : Type*` with `Fintype` | Works for `Fin 2` player games specifically |

### Key Theorems

| Theorem | math-xmum | elazarg |
|---------|-----------|---------|
| `maxmin ≤ minmax` (pure) | `maxmin_le_minmax` ✅ | Not stated |
| `lam0 = mu0` (mixed) | `minmax_theorem'` ✅ | Not stated (implicit in Nash) |
| `∃ v xx yy, guarantees` | `minmax_theorem` ✅ | `von_neumann_minimax` ✅ |
| Nash EU uniqueness | Not stated | `nash_eu_eq` ✅ |
| Nash interchangeability | Not stated | `nash_interchangeable` ✅ |
| Nash p0 optimal | Not stated | `nash_p0_optimal` ✅ |

## Assessment

### math-xmum advantages

1. **Self-contained**: No dependency on Brouwer/Nash existence. The minimax theorem
   IS the fundamental result, proved directly.
2. **Explicit maximin/minimax**: Defines `lam0`, `mu0` and proves they're equal.
   This is the classical formulation.
3. **More definitions**: Has `guarantees1`, `guarantees2`, `maxmin`, `minmax` as
   standalone concepts useful beyond minimax.
4. **Constructive flavor**: The Loomis proof constructs optimal strategies explicitly.

### elazarg advantages

1. **Much shorter**: The minimax theorem itself is ~30 lines (vs ~600).
2. **More theorems**: Has Nash EU uniqueness, interchangeability — properties that
   math-xmum doesn't state.
3. **Modular**: Reuses Nash existence. Adding new consequences is easy.
4. **General framework**: `IsZeroSum` is a predicate on `KernelGame`, not a separate type.
5. **Clean proofs**: Short `linarith`-based proofs using the cross-profile trick.

### math-xmum disadvantages

1. **Long and complex**: 829 lines with analysis arguments (continuity on simplex,
   convex combinations, ContinuousAt lemmas).
2. **Hardcoded to ℝ**: The proof uses `iSup`, `iInf`, compactness — all over ℝ.
3. **Custom simplex type**: Uses its own `S I` instead of Mathlib's `stdSimplex`.
4. **Missing properties**: Doesn't prove Nash uniqueness or interchangeability.

### elazarg disadvantages

1. **Depends on Brouwer**: The proof is "cheat" in some sense — it reduces to Nash,
   which requires the full Brouwer fixed-point machinery.
2. **No explicit maximin/minimax**: Doesn't define the classical minimax concepts.
3. **Hardcoded to ℝ** (via `KernelGame`'s utility type).

## Decision for EconCSLib

**Use Loomis's direct proof (math-xmum), NOT the Nash-based approach (elazarg).**

### Rationale

1. **Generality over ordered fields**: Loomis's proof is algebraic/combinatorial —
   it works over any linearly ordered field `𝕜`, not just `ℝ`. This means we can
   prove minimax for `ℚ`-valued games, enabling `native_decide` verification.
   
   elazarg's approach goes through Brouwer's fixed-point theorem, which requires
   topological structure (compactness, continuity) — only available over `ℝ`.

2. **Independence from Brouwer**: The minimax theorem is a fundamental result that
   should not depend on fixed-point theorems. Loomis's proof is self-contained.

3. **Bourbaki principle**: The theorem holds over any ordered field. A proof that
   only works over `ℝ` imposes an unnecessary assumption.

4. **Constructive value**: Loomis's proof constructs optimal strategies explicitly
   via convex combinations, not just proves existence.

### Plan

1. Port math-xmum's `Zerosum.lean` to EconCSLib's `StrategicGame` framework
2. Replace `ℝ` with a general ordered field `𝕜` where possible
3. Replace custom `S I` (simplex) with `stdSimplex 𝕜`
4. Add elazarg's short corollaries (Nash uniqueness, interchangeability) on top
