# Zero-Sum Games: Minimal Assumptions Analysis

What is the minimum typeclass assumption needed for each zero-sum concept?

---

## Definitions

| Concept | Statement | Minimal Assumption |
|---------|-----------|-------------------|
| `IsZeroSum G` | `∀ σ, G.payoff σ 0 + G.payoff σ 1 = 0` | `[AddZeroClass U]` |
| `IsConstantSum G c` | `∀ σ, G.payoff σ 0 + G.payoff σ 1 = c` | `[Add U]` |
| `IsZeroSum.neg` | `G.payoff σ 1 = -G.payoff σ 0` | `[AddGroup U]` |

These are purely algebraic — no order needed for the definitions.

## Properties Involving Order

| Concept | Statement | Minimal Assumption |
|---------|-----------|-------------------|
| `MaxminValue G i` | `sup_{s_i} inf_{s_{-i}} payoff(s_i, s_{-i}, i)` | `[Preorder U]` + `[Fintype]` for finite sup/inf |
| `maxmin_le_minmax` | Always `maxmin ≤ minmax` | `[Preorder U]` |
| `nash_payoff_ge_maxmin` | Nash payoff ≥ maxmin [MSZ 4.29] | `[Preorder U]` |
| `nash_payoff_eq` | All Nash give same payoff in zero-sum | `[LinearOrder U]` + `[AddGroup U]` |

For finite games, `sup`/`inf` over finite sets only need `[LinearOrder U]`
(use `Finset.sup'` / `Finset.inf'`).

## The Minimax Theorem (Value Existence)

The key question: when does `maxmin = minmax`?

### Pure strategies

For finite games with pure strategies:
- `maxmin_pure` and `minmax_pure` are well-defined with `[LinearOrder U] [Fintype]`
- But `maxmin_pure = minmax_pure` is **false in general** (e.g., Matching Pennies)
- No additional assumption on `U` makes this true — it's a property of the game

### Mixed strategies (the minimax theorem)

The minimax theorem [MSZ 5.11, von Neumann 1928]:

> Every finite two-player zero-sum game has a value in mixed strategies.

This needs:
1. **Mixed strategies** = probability distributions = elements of `stdSimplex`
2. **Expected payoff** = `∑ σ, (∏ j, p j (σ j)) * G.payoff σ i`
3. This requires **multiplication** of probabilities × payoffs

So the statement needs:
- `[Field U]` (or `[CommSemiring U]`) — for multiplication and division in probabilities
- `[LinearOrder U]` — for max/min
- `[IsStrictOrderedRing U]` — for compatibility (ordered field structure)

Or equivalently (old style): `[LinearOrderedField U]`.

**But**: the probabilities live in `[0,1] ⊂ U`, so technically we need an ordered
field for the simplex to make sense. `ℝ` and `ℚ` are the standard instances.

### Can we use `OrderedRing` instead of `LinearOrderedField`?

An `OrderedRing` (ring + partial order + compatibility):
- ✅ Has multiplication for expected payoff
- ✅ Has addition for sums
- ❌ **No division** — can't normalize probabilities
- ❌ **Not total** — can't take max/min
- ❌ `stdSimplex` is defined over `LinearOrder` types

An `OrderedField` (field + partial order):
- ✅ Has all arithmetic
- ❌ **Not total** — can't take max/min

A `LinearOrder` + `Field` + `IsStrictOrderedRing`:
- ✅ Everything needed
- This is exactly what replaces `LinearOrderedField`

**Conclusion**:

```
Level 0: [Add U] [Zero U]           — IsZeroSum definition
Level 1: [AddGroup U]               — IsZeroSum.neg (payoff negation)
Level 2: [LinearOrder U] [AddGroup U] — nash_payoff_eq, maxmin/minmax statements
Level 3: [Field U] [LinearOrder U] [IsStrictOrderedRing U]
                                     — minimax theorem (mixed strategy value existence)
```

## Design Decision

**For definitions**: use Level 0-1 (just algebra, no order).

**For theorem statements about pure strategies**: use Level 2 (order + group).

**For the minimax theorem**: use Level 3. A theorem-facing interface has the
following shape:

```lean
theorem minimax_theorem
    [Field U] [LinearOrder U] [IsStrictOrderedRing U]
    [Fintype (G.strategy 0)] [Fintype (G.strategy 1)]
    (hzs : IsZeroSum G) :
    ∃ v : U, HasValue G v
```

Add such an interface to Lean only with a proof. Until then, keep the
mathematical target in the knowledge blueprint.

**For `ℝ` and `ℚ`**: both satisfy `[Field _] [LinearOrder _] [IsStrictOrderedRing _]`,
so the theorem applies to both. Using the abstract typeclasses instead of fixing `ℝ`
is more general and follows Bourbaki principle.
