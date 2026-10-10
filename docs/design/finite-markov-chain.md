# Exact finite absorbing Markov chains

`FiniteMarkovChain.Chain n m` models a fixed finite Markov chain with rational
transition probabilities, `n` transient states, `m` absorbing terminal states,
and a rational terminal reward. This extracts the finite-chain algorithms
developed alongside the EFG work into a mathematics layer that depends only
on `FiniteLaw` and Mathlib.

## Representation and reading order

| Module | Purpose |
|--------|---------|
| `Math/Probability/FiniteMarkovChain.lean` | Transition rows, censored finite execution, absorption checks, exact Bellman solving |
| `Math/Probability/FiniteMarkovChain/Semantics.lean` | Summability, the first-hit probability law, integrability, and correctness of the actual solver output |
| `Examples/FiniteMarkovChain.lean` | Geometric waiting, multiple terminal outcomes, a cyclic chain, domain rejection, and ordinary theorem consumers |

The stable `EconCSLib` aggregate imports the executable module. Import
`EconCSLib.Math.Probability.FiniteMarkovChain.Semantics` explicitly for its
analytic correctness theorems. The executable entry point does not import
this analytic leaf or the examples.

The transient and terminal blocks have type `Matrix (Fin n) (Fin n) ℚ≥0`
and `Matrix (Fin n) (Fin m) ℚ≥0`. Each complete transient row sums to one.
The `Fin` encodings supply executable enumeration and equality. Absorption
is checked later, so the structure also represents chains with closed
transient classes. No inverse, candidate solution, or moment bound is stored
in the model.

This is a fixed Markov specification. Applying it to an EFG requires a
separate justification that the chosen states retain the relevant history
and that transitions implement the intended policy.

## Execution and time

`C.run horizon i` returns a normalized `FiniteLaw` of censored outcomes:

- `Sum.inl j`: execution is still transient at the supplied horizon;
- `Sum.inr (r, a)`: the first terminal outcome is `a`, after **`r + 1`** transitions.

The `r` coordinate counts preceding transient transitions. Distinct first-hit
times remain distinct outcomes. `run_expect` specifies the complete finite
law through transient matrix powers and first-hit coefficients;
`run_firstHit` identifies individual hit coefficients and `run_survival`
identifies unfinished mass. A finite horizon preserves unfinished mass even
for an almost-surely absorbing chain.

For example, a fair repeat-or-stop chain with terminal reward six has
unfinished mass `1/4` after two steps. Its two observed hit outcomes have
masses `1/2` and `1/4`, while `autoSolve` returns expected reward six and
expected duration two.

## Checking and solving

| API | Contract |
|-----|----------|
| `admissible k c` | Checks `0 < k`, `0 ≤ c < 1`, and a common `k`-step survival bound `c` on every transient row |
| `solveLinear A b` | Checks the rational determinant and computes Cramer's solution, or returns `none` for a singular matrix |
| `solve k c` | Checks the supplied bound and solves the reward and duration Bellman systems |
| `autoBound`, `autoCheck` | Compute the largest `(n + 1)`-step survival probability and check full-domain absorption |
| `autoSolve` | Compute the bound and return exact reward and duration functions, including the terminal values |

`finite_horizon_complete` proves that any positive-probability terminal route
has a witness within `n` steps. `autoCheck_iff_reaches` consequently identifies
the automatic test with existence of such a route from every supplied
transient state. The additional step keeps the automatic block length
positive when `n = 0`; the maximum over an empty transient domain is zero.

Rejection returns `SolveError.absorptionBound`. It concerns the entire
supplied transient domain: one start may terminate even when another is a
closed class. `autoCheck_failure` supplies a state whose survival probability
is one at every horizon. No successful start is silently selected or closed
class silently removed.

The low-level solver also exposes `SolveError.singular`. In the semantic
leaf, `det_ne_zero` proves that a valid absorption bound excludes singularity,
and `autoSolve_ne_singular` excludes that error from automatic solving.
Terminal reward is retained verbatim, including negative values, and terminal
duration is zero.

## Correctness and source organization

Read the semantic proof in four stages: summable matrix powers, the normalized
first-hit law, reward and time integrability, then `solve_correct`.
`autoCheck_iff_absorbsAll` proves that the exact finite check is equivalent to
survival tending to zero for every supplied start. `autoSolve_correct` proves
success, both Bellman equations, uniqueness, normalization, integrability,
and equality between the actual rational output and the two real integrals.
`autoSolve_integrals` exposes the equality for an observed output pair.

Following the existing finite-law style, `section` separates mathematical
blocks, shared parameters use `variable`, and the checked-absorption
hypothesis is local to the results that need it. Helper results use `lemma`;
central specifications and correctness results use `theorem`. Both forms are
kernel-checked. The shared hypothesis does not add a field to `Chain` or
become an argument of its executable algorithms.

Analytic sums and integrals occur in propositions and proofs. They do not
provide an algorithm for arbitrary real-weighted chains, infinite-state
kernels, or general infinite path measures. The solver uses dense rational
determinants and Cramer's rule; it makes no scalability claim.

## Verification

`tests/FiniteMarkovChainSmoke.lean` evaluates the formal library through the
worked models with `#guard`, including multi-step and cyclic absorption,
negative terminal rewards, singular systems, invalid bounds, domain-wide
rejection, and an empty transient domain. The geometric example also proves its concrete
reward and duration integrals using the Bellman equations. Normalization and theorem examples
use ordinary Lean proofs rather than native-decision proof axioms.

`tests/FiniteMarkovChainAudit.lean` checks that the executable import excludes
the semantic leaf and examples, then discovers declarations owned by both
library modules and the worked example, including private and generated
ones. It rejects noncomputable declarations and nonstandard axiom dependencies,
then replays safe declarations in a fresh environment containing only external
imports. Compiler recursion helpers must have a safe total definition in the
same owner module and are separately counted, as in `FiniteLawAudit`.

```bash
lake build
lake build EconCSLib.Examples
lake env lean tests/FiniteMarkovChainSmoke.lean
lake env lean tests/FiniteMarkovChainAudit.lean
python3 scripts/check_lean_placeholders.py EconCSLib
git diff --check
```
