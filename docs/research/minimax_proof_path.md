# Minimax Proof Path Analysis

## math-xmum's Loomis proof: what uses ℝ?

### Step 1: Definitions (lines 36-120)

```
zerosumGame I J               -- g : I → J → ℝ           ← uses ℝ
maxmin / minmax                -- via iSup/iInf on EReal  ← needs completeness
E A x y                       -- bilinear form            ← works over any field
lam.aux A x = inf_j E(A,x,j) -- via Finset.inf'          ← works over LinearOrder
lam0 A = sup_x lam.aux(A,x)  -- via iSup on ℝ            ← needs completeness!
mu.aux A y = sup_i E(A,i,y)   -- via Finset.sup'          ← works over LinearOrder
mu0 A = inf_y mu.aux(A,y)     -- via iInf on ℝ            ← needs completeness!
```

**Key issue**: `lam0` and `mu0` are `iSup`/`iInf` over the simplex (uncountable set).
Over a general field, these may not exist.

**But**: `lam.aux` is a continuous function on a compact set (the simplex).
Its supremum is attained. So `lam0 = max lam.aux`, not just `sup`.

**Over finite types**: If I and J are `Fintype`, the simplex is a compact
subset of `𝕜^|I|`. But "compact" needs topology, which needs ℝ.

### Step 2: Attainment of sup/inf (lines 131-247)

```
lam.aux.continuous             -- Continuous (lam.aux A)     ← needs topology on ℝ
exits_xx_lam0                  -- ∃ xx, lam.aux A xx = lam0  ← needs compactness on ℝ
mu.aux.continuous              -- similar
exits_yy_mu0                   -- similar
```

These are ESSENTIAL for the Loomis proof. The induction step constructs
a convex combination that achieves a value > lam0, contradicting maximality.
This needs the sup to be attained.

### Step 3: Loomis induction (lines 500-770)

```
minmax' n (Hn : n = |I| + |J|) : lam0 A = mu0 A
```

Proof by strong induction on n. The key step:
1. Assume `lam0 A < mu0 A`
2. Find column j₀ with slack: `E(xx, j₀) > lam0 A`
3. Remove j₀ to get smaller game A' on I × J'
4. By IH: `lam0 A' = mu0 A'`
5. The optimal xx' for A' satisfies `lam.aux A xx' ≥ lam0 A`
6. But `E(xx', j₀) > lam0 A` (from slack)
7. Convex combination `t·xx + (1-t)·xx'` has `lam.aux > lam0` → contradiction

Steps 5-7 use **convex combinations** and **strict monotonicity** — these work
over any ordered field. The issue is step 2 (finding j₀ with slack) which
requires the optimal `xx` to exist (attainment).

### Step 4: Theorem statement (lines 807-829)

```
minmax_theorem : ∃ xx yy v, guarantees
```

This uses `exits_xx_lam0` and `exits_yy_mu0` again.

## Assessment: What REALLY needs ℝ?

| Step | Uses ℝ for | Can generalize? |
|------|-----------|-----------------|
| `E A x y` bilinear form | Nothing | ✅ Any commutative ring |
| `lam.aux` = `Finset.inf'` | Nothing | ✅ Any `LinearOrder` |
| `mu.aux` = `Finset.sup'` | Nothing | ✅ Any `LinearOrder` |
| `lam0` = `iSup` on simplex | Completeness | ❌ Needs ℝ or similar |
| `mu0` = `iInf` on simplex | Completeness | ❌ Needs ℝ or similar |
| Attainment `∃ xx, lam.aux xx = lam0` | Compactness + continuity | ❌ Needs ℝ topology |
| Convex combination lemmas | Ordered field arithmetic | ✅ Any ordered field |
| Loomis induction logic | Finding j₀ with slack | ⚠️ Needs attainment |

**Conclusion**: The proof fundamentally needs **attainment of sup/inf on the simplex**,
which requires **compactness** (topology) or an equivalent algebraic argument.

## Two Approaches

### Approach A: Port over ℝ first, generalize later

1. Port math-xmum's proof as-is over ℝ
2. All topology/compactness arguments work
3. Later, find an algebraic proof for general fields (open research question?)

**Advantage**: Fast, reuses existing proof.
**Disadvantage**: Locked to ℝ.

### Approach B: Algebraic proof for general ordered fields

For **finite** games (finite I, J), there IS a purely algebraic proof:
- The simplex is defined by finitely many linear constraints
- `lam.aux` is a piecewise-linear function (min of finitely many linear functions)
- Its max over the simplex is a linear programming problem
- LP duality gives minimax without topology

But LP duality itself needs careful formalization, and Mathlib doesn't have it.

Alternative: **finite enumeration**. For finite I and J, the simplex has finitely
many "extreme points" (vertices). The max of a convex function is at a vertex.
But `lam.aux` is concave (min of linear), not convex — its max need not be at a vertex.

### Approach C: Port over ℝ, add transfer principle

1. Prove minimax over ℝ (using math-xmum's proof)
2. State: for any ordered field 𝕜 ⊆ ℝ with 𝕜-valued payoffs,
   the optimal strategies can be taken to have 𝕜-valued probabilities
3. This is a rationality result — optimal strategies for ℚ-valued games are in ℚ

This is mathematically true but non-trivial to formalize.

## Recommendation

**Approach A**: Port over ℝ first. This is a working proof without placeholders.
The generalization to other fields is a separate (harder) research problem.

For concrete verification over ℚ, we already have `native_decide` for
small games (like RPS). The minimax theorem over ℝ still applies to
ℚ-valued games (ℚ ⊂ ℝ).
