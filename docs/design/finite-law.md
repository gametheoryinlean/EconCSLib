# Executable finite probability

`FiniteLaw` provides exact finite probability calculations for models that
supply nonnegative rational weights. Its algorithms and correctness theorems
live in `Math/Probability/`, with no game-theory dependency. The stable
`EconCSLib` import includes the aggregate
`EconCSLib.Math.Probability.FiniteLaw`.

## §1. Representation and reading order

A `FiniteLaw α` contains a `List (α × ℚ≥0)` and a proof that the weights sum
to one. Repeated outcomes and zero-weight entries are allowed. The carrier
`α` need not be finite or decidably equal: the list supplies the finite data
needed to execute `map`, `bind`, and rational expectation.

Read the implementation in this order:

| Module | Purpose and main entry points |
|--------|-------------------------------|
| `FiniteLaw/Core.lean` | Point laws, composition, mass, expectation, semantic equivalence, normalization |
| `FiniteLaw/Product.lean` | `independentPair`, `finPi`, `fintypePi`, product mass and marginal theorems |
| `FiniteLaw/Conditioning.lean` | `condition?`, `conditionOnFiber`, posterior mass and independent-table conditioning |
| `FiniteLaw/Coupling.lean` | `RelCoupling`, its marginal witnesses, mapping and composition |
| `FiniteLaw/DeferredSampling.lean` | `FreshQueryTree`, execution with a table or on demand, deferred-decisions theorem |

These modules extract the finite-probability foundation developed for the
EFG work. They do not depend on its strategy, history, or compiler APIs.

## §2. Minimal assumptions and equality

| Operation | Additional data or assumptions | Meaning |
|-----------|--------------------------------|---------|
| `pure`, `map`, `bind` | None on the outcome carrier | Construct and compose normalized finite laws |
| `eventMass`, `condition?` | An executable predicate `α → Bool` | Sum or condition on selected occurrences |
| `expectRat` | A supplied payoff `α → ℚ` | Compute an exact rational expectation |
| `mass` | `[DecidableEq α]` | Add all occurrences equal to an outcome |
| `conditionOnFiber` | `[DecidableEq β]`, an observation `α → β` | Condition on an observed value without equality on `α` |
| `finPi` | A family indexed by `Fin k` | Sample independent coordinates |
| `fintypePi` | `[Fintype I] [LinearOrder I]` | Enumerate and sample a general finite index type |

Equality of structures compares atom lists. `FiniteLaw.Equivalent` instead
compares expectations of every rational-valued function. It expresses the
semantic equality needed for composition, reindexing, and deferred sampling
without requiring decidable equality on the carrier. With decidable equality,
`Equivalent.of_mass_eq` derives it from equality of point masses.

The explicit order for `fintypePi` gives an executable enumeration. Its
reindexing and marginal theorems describe the resulting law using
`Equivalent`; they do not require identical atom-list order.

## §3. Partial conditioning and fresh queries

`normalize?` returns `none` for an empty or zero-total-weight list.
`condition?` and `conditionOnFiber` consequently return `none` on a zero-mass
event or fiber. A successful posterior whose expected payoff is zero remains
`some 0` after mapping expectation over the result. Callers must handle an
absent posterior explicitly.

`RelCoupling R left right` carries a finite joint law of related pairs and
proofs that its projections are equivalent to the supplied marginals.
Mapping and binding construct new joint laws from those witnesses.

`FreshQueryTree X R remaining` records the coordinates still available to
query. A query removes its coordinate from that set, so a path cannot query
the same coordinate twice. Chance nodes allow additional supplied finite
randomness. `runPresampled_eq_runOnDemand` proves that sampling the available
table in advance and sampling coordinates when queried produce equivalent
output laws. The caller supplies the tree with its freshness evidence; this
module does not construct that evidence for an arbitrary game or program.

## §4. Source organization

Each mathematical block uses `section` for a coherent group of definitions
and results. Shared type parameters use `variable` where their scope and
elaborated parameter order permit it. Decidability, finiteness, and substantive
hypotheses stay close to the declarations that need them. Proof helpers use
`lemma`; central composition, product, conditioning, and deferred-decisions
results use `theorem`. Both are checked by the same Lean kernel.

This follows Formech's readable progression from local parameters and
hypotheses to helper lemmas and a main theorem. Lean 4 hypotheses are expressed
as proposition-valued parameters or `variable` declarations; no additional
hypothesis abstraction is needed. Section boundaries do not add assumptions
to the `FiniteLaw` structure.

For a concrete reading example, the `MarginalComposition` section in
`Coupling` fixes projection data, then states separate expectation and
positive-atom hypotheses with `variable` and `include`. Two private lemmas
discharge the corresponding obligations for both sides of `RelCoupling.bind`.
`Conditioning` similarly separates marginal event mass, the updated product
formula, and successful posterior equivalence before the main case split.
In `DeferredSampling`, private lemmas for terminal, chance, and query nodes
make the main theorem a short structural induction. These helpers organize
proofs without adding public entry points or changing the sampled data.

## §5. Examples, verification, and scope

[`tests/FiniteLawSmoke.lean`](../../tests/FiniteLawSmoke.lean) exercises exact
coin probabilities, repeated atoms, a function-valued infinite carrier,
zero-mass conditioning, finite products, couplings, and a fresh-query tree.
It evaluates the library algorithms with `#guard` and instantiates their
correctness theorems with ordinary Lean proofs.

[`tests/FiniteLawAudit.lean`](../../tests/FiniteLawAudit.lean) discovers
declarations by their owning module, including private and generated ones.
It rejects noncomputable declarations and axiom dependencies beyond
`propext`, `Quot.sound`, and `Classical.choice`. Unsafe or partial
declarations are accepted only for Lean's recursive implementation helpers
with a safe total definition in the same module; an opaque wrapper from
`partial def` is rejected. Following `Lean.replay`, those
compiler helpers are excluded from kernel replay; every safe declaration is
replayed into an environment containing only external imports. The audit
reports both counts. The standard logical-axiom allowance does not permit
noncomputable runtime definitions.

Run from the repository root:

```bash
lake build
lake build EconCSLib.Examples
lake env lean tests/FiniteLawSmoke.lean
lake env lean tests/FiniteLawAudit.lean
python3 scripts/check_lean_placeholders.py EconCSLib
git diff --check
```

The executable scope is supplied finite rational data. This interface does
not construct arbitrary real-weighted laws, general measure-theoretic
kernels, or infinite path measures. Its lists also make no efficiency claim:
independent products can enumerate exponentially many combinations.
