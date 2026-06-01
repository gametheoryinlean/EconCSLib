# Minimax Theorem over General Ordered Fields

**Goal**: Prove the minimax theorem over arbitrary ordered fields, not just ℝ.
This enables `native_decide` verification over ℚ.

## Approaches

### 1. Weyl's Elementary Proof (1950)

**Source**: Hermann Weyl, "Elementary Proof of a Minimax Theorem due to von Neumann",
in *Contributions to the Theory of Games*, Annals of Mathematics Studies 24, Princeton 1950.
PDF in `docs/Hermann weyl, Elementray Proof of a Minimax Theorem.pdf`.

**Technique**: Weyl EXPLICITLY works over a general ordered field K:

> "As elementary are considered such operations in an ordered field K
> of numbers as require nothing but addition, subtraction, multiplication
> and division, and the decision whether a given number is > 0 or = 0 or < 0.
> ... As for the field K no continuity axioms, not even the axiom of
> Archimedes, are assumed."

The proof uses:
1. **Lemma 1** (about convex pyramids): either a configuration has an extreme
   support, or every point is a non-negative combination
2. **Lemma 4** (alternative theorem): either `∑ a_{ik} η_k ≥ 0` has a solution
   with η ≥ 0, or `∑ ξ_i a_{ik} < 0` has a solution with ξ ≥ 0
3. A parametric argument: varying λ (time parameter), tracking which
   "combinations" of support hyperplanes are "alive"
4. Finding λ₀ = max of "admissible" λ values — this IS the minimax value

**Ordered field**: ✅ EXPLICITLY over any ordered field K. No Archimedean
property needed. No continuity/compactness.

**Proof length**: ~7 pages, moderately dense.

**Computability**: Semi-constructive. The proof searches over a finite number
of (n-1)-combinations to find admissible ones.

### 2. von Neumann Symmetrisation (Theorem of the Alternative)

**Technique**: Embed the game in a skew-symmetric matrix
(`SkewSymmetric.optimal`) whose value is 0. A value-0 optimal strategy exists by
the **Theorem of the Alternative** (Fourier–Motzkin / Farkas), which is purely
algebraic and needs no compactness or order-completeness. Reading the minimax
value off the embedded game recovers the general statement.

**Ordered field**: ✅ Works over any linearly ordered field. No Archimedean
property, no continuity, no compactness.

**Computability**: ⭐⭐⭐ The Theorem of the Alternative is established by
finite elimination over the ordered field.

**Status**: This is the route actually used in `main`. `Minimax.minimax` in
`EconCSLib/Math/Minimax/Minimax.lean` is proved without placeholders by this
method.

### 3. LP Duality

**Source**: Standard linear programming theory. See e.g.,
*Algorithmic Game Theory* Ch.3.

**Technique**: Both sides of the minimax inequality are formulated as
linear programs (primal and dual). Strong LP duality says optimal values
are equal. The proof of strong duality is purely algebraic (e.g., via
the simplex method or complementary slackness).

```
max   min_j (∑_i x_i · A_{ij})        ←→  Primal LP
s.t.  x ∈ Δ_I

min   max_i (∑_j y_j · A_{ij})        ←→  Dual LP  
s.t.  y ∈ Δ_J

Strong duality: optimal primal = optimal dual
Therefore: maxmin = minimax
```

**Ordered field**: ✅ LP duality is purely algebraic. Farkas' lemma
(the foundation) can be proved over ordered fields.

**Computability**: ⭐⭐⭐ The simplex method is constructive and terminates
in finite steps (with anti-cycling rules like Bland's rule).

## Comparison

| | Weyl (1950) | Symmetrisation | LP Duality |
|---|---|---|---|
| Topology-free | ✅ | ✅ | ✅ |
| Over ordered fields | Likely ✅ | ✅ | ✅ |
| Constructive | Unclear | ⭐⭐⭐ (alternative theorem) | ⭐⭐⭐ (simplex method) |
| Self-contained | ✅ | ✅ | Needs LP theory |
| Produces strategies | Unclear | ✅ from the alternative | ✅ from LP solution |
| Proof length | Short (~5 pages) | Short | Medium (LP theory) |
| Formalization effort | Medium | Done | High (need LP first) |

## Comparison with Current Approaches

| | math-xmum (Loomis) | elazarg (via Nash) | Weyl/Symmetrisation/LP |
|---|---|---|---|
| Over ℝ only | ✅ uses iSup, compact | ✅ uses Brouwer | ❌ general field |
| Topology | Continuity + compactness | Brouwer FPT | None |
| Constructive | Semi (induction) | No (existence) | Yes (simplex) |
| Computability | `noncomputable` | `noncomputable` | Potentially computable |

## Outcome

**The symmetrisation approach is what landed in `main`:**

1. **Purely algebraic** — works over any linearly ordered field (ℚ, ℝ, etc.)
2. **No topology** — the value-0 optimal strategy comes from the Theorem of the
   Alternative (Fourier–Motzkin / Farkas), needing no compactness or
   order-completeness
3. **Self-contained** — doesn't require building full LP duality theory first

This is realised as `Minimax.minimax` in `EconCSLib/Math/Minimax/Minimax.lean`,
proved without placeholders. The ℝ von Neumann minimax theorem is additionally available as
the `B = 𝟙` corollary of the general Loomis theorem,
`Loomis.minmax_from_general` in `EconCSLib/Math/Minimax/Loomis.lean`.

**Alternative**: Implement LP strong duality first (more general, but more work),
then derive minimax as a corollary. This would also give us LP solving for
other applications (mechanism design, welfare optimization).

## References

- Weyl, H. (1950). Elementary proof of a minimax theorem. In *Contributions
  to the Theory of Games*, Annals of Mathematics Studies 24, Princeton.
- Nisan et al. (2007). *Algorithmic Game Theory*, Ch. 3.
- Laraki, Renault, Sorin. *Mathematical Foundations of Game Theory*, Theorem 2.3.1.
