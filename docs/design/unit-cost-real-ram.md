# Unit-cost real-RAM complexity interfaces

The open-problem layer uses two complementary levels of cost semantics.

## 1. Compositional `CostM` accounting

`EconCSLib.OpenProblem.Util.UnitCostRAM` specializes the library's writer
monad to natural operation counts and supplies charged arithmetic, comparison,
random-access memory, finite traversals, list folds/maps, counted iteration,
fuelled while loops, oracle calls, distribution samples, randomness,
communication, and peak live-cell accounting.  Its theorems compose local
bounds into polynomial bounds.

This level is intentionally proof-oriented.  Cost annotations are reviewed
and trusted; `Cost.pure` must never hide nontrivial computation.

## 2. Instruction-enforced accounting

`EconCSLib.OpenProblem.Util.UnitCostRAMMachine` is the strict alternative.  A
program is a finite array of instructions and the interpreter generates all
resource counters.  Its words contain exact integers, Booleans, or exact real
numbers.  The instruction set includes:

- constant/move, indirect load/store, and stack-style allocation/free;
- integer and exact-real arithmetic, comparison, and Boolean operations;
- conditional/unconditional control transfer;
- explicit oracle calls, distribution samples, and random-bit reads; and
- checked halt/output decoding.

Out-of-range memory access, word-type mismatch, division by zero, falling past
the code, and insufficient fuel are explicit failures.  Lossless encodings tie
mathematical input/output types to finite RAM-word representations.

The preferred strict certificates are
`StrictRAMComputableInPolyTime` and
`StrictRAMComputableInPolyTimeWithChoice`; dependent search relations use
`StrictRAMSearchableInPolyTime`.  Their input/output encodings are
parameters fixed by the surrounding theorem, rather than fields selected by
the implementation witness.  They contain one finite program, one explicit
`Polynomial ℕ`, and a proof that the actual interpreter trace is bounded by
that polynomial.  This prevents a witness-specific decoder from doing the
mathematical work for an otherwise empty program.

The deterministic strict interface has no random tape or external operation.
The preferred choice-parametric interface,
`StrictRAMComputableInPolyTimeWithFixedEnvironment`, supports seeds and legal
oracles with a single worst-case polynomial bound over every choice.  Both the
external-operation type and its semantics are parameters fixed before the
program witness; otherwise an ad-hoc witness-local oracle could simply return
the desired answer.  The caller must also prove that this fixed external
semantics is exactly the oracle promised by the problem.
The older existential-encoding wrappers remain for compatibility, but new
open-problem statements should fix canonical representations externally.

Bulk syntax is not bulk time.  A strict `halt` pays for every output word,
and an external call/sample pays for all argument and answer words transferred
in addition to incrementing the corresponding oracle counter.  Thus a single
bulk instruction cannot manufacture an exponentially long represented value
at unit local cost.

`FixedEncodingSearchProblem` packages a promise/search relation with fixed
representations.  `FixedEncodingPolynomialSearchReduction` requires finite
strict-RAM programs for both maps and uses a canonical length-prefixed
encoding of the source-input/target-solution pair.  The older
`PolynomialSearchReduction` is only a trusted-instrumentation compatibility
layer.  Likewise, `StrictPPADHard` is the instruction-enforced PPAD predicate;
the original `PPADHard` remains legacy while benchmarks are being migrated to
canonical circuit encodings.

### Design comparison with OpenAI `ten-proofs`

The complexity development in `ten-proofs/GapCVP.lean` uses Mathlib's
`Turing.TM2ComputableInPolyTime`.  Four design choices transfer directly to
the real-RAM layer even though this library deliberately does not model a
Turing tape:

1. binary input/output encodings are fixed before the machine witness;
2. the witness contains a finite program and an explicit `Polynomial ℕ`;
3. the time theorem bounds the actual machine execution producing the output;
4. sequential composition first proves a polynomial output-length bound, then
   substitutes that polynomial into the running-time polynomial of the next
   machine.

The `ten-proofs/Permanent.lean` development likewise represents an arithmetic
circuit by a finite list of instructions and defines its size syntactically.
Both examples support the same principle used here: complexity belongs to an
explicit executable representation, not to an arbitrary Lean function whose
body may conceal uncharged work.

`FixedEncodingFunctionFamily` applies the same lesson to indexed families:
one finite program receives the family index as part of its encoded input.  A
statement `∀ n, ∃ program_n` is nonuniform even if the witnesses share one
coefficient and exponent, because the program texts themselves can contain
unbounded advice.

## 3. Executable yes/no static analysis

`EconCSLib.OpenProblem.Util.StaticComplexity` adds a finite algorithm-shape
language and an executable checker.  Symbolic bounds are built from constants,
the aggregate input size, sums, products, fixed powers, maxima, and logarithms.
Sequencing, conditionals, and bounded loops generate symbolic bounds for time,
oracle queries, distribution samples, random bits, communication, and peak
auxiliary space.

`decidePolynomialTime` and `decideAllPolynomialResources` return `Bool` values.
Their soundness theorems turn a computed `true` into the semantic
`IsPolyBound` propositions used elsewhere in the library.  Linking a real
implementation requires componentwise proofs that its instrumented counters
do not exceed the analyzed shape; after that, no polynomial coefficient or
exponent is selected manually.

For new algorithms, `AnalyzedComputation` is the preferred intrinsic EDSL.
Its `mapUnit`, dependent `bind`, sequencing, branching, counted iteration,
list fold, and fuelled-while combinators construct the executable computation,
its static shape, and their cost inequality together.  Hence only leaf
primitives or external library routines need local audited cost contracts;
there is no global hand-written polynomial proof.  The `primitive` constructor
is polymorphic in dependent input/output types, so it is also the controlled
escape hatch for solvers and domain operations not yet present in the common
instruction vocabulary.

The checker is deliberately conservative.  It returns `false` for explicit
exponential/factorial growth and for unknown bounds.  Therefore `false` means
"not certified by this analyzer", not a semantic lower-bound proof for every
possible implementation of the same mathematical function.  A complete
decider for arbitrary Lean functions would contradict standard
undecidability barriers.

## 4. Reading executable algorithm syntax

`EconCSLib.OpenProblem.Util.AlgorithmCost` removes the remaining duplication
between executable control flow and a separately written `AlgorithmShape`.
It provides two interoperable syntaxes:

- `PrimitiveProgram` is a typed free program.  A `PrimitiveModel` declares
  the result and symbolic unit-cost price of each permitted instruction.
  Traversing the selected continuation gives an exact `GrowthExpr`, and the
  interpreter theorem proves that evaluating this expression equals the
  actual abstract-machine operation count.
- `StructuredProgram` represents state updates, sequencing, conditionals,
  counted loops, state-dependent counted loops, and total fuelled while
  loops.  Its analyzer reads that same executable syntax and generates a
  uniform worst-case expression in the aggregate input size.  A
  `StructuredAlgorithm` adds initialization and final projection.

`StructuredProgram.ofPrimitiveProgram` joins the two layers: detailed typed
data flow is extracted exactly at primitive level, while one local inequality
turns it into a state-independent bound usable under loops.  The analyzer
returns both the symbolic expression and a computable degree upper bound.
Kernel-checked soundness theorems connect a returned degree directly to the
interpreter's real operation counter and also connect accepted polynomial
expressions to Mathlib's `Asymptotics.IsBigO`.

This is intentionally source-level deep embedding rather than post-hoc
inspection of Lean compiler IR.  Compiler IR is optimized, backend-sensitive,
and does not by itself identify which mathematical operations the chosen
unit-cost RAM model regards as primitive.  Arbitrary external routines remain
usable through a local proved cost contract; they are never assigned a cost
merely from their Lean name.

## 5. Conservative reader for ordinary Lean `def`s

`EconCSLib.OpenProblem.Util.SourceCost` is a front end for code that was not
written in an instrumented EDSL.  The command

```lean
#source_cost declarationName
```

reads the declaration value stored in Lean's environment and traverses its
`Lean.Expr` syntax.  It beta-reduces direct lambda applications, follows
transparent and stored opaque helper bodies (including imported helpers),
recognizes conditionals and structural recursors, and uses audited contracts
for common list/array traversals and sorting routines. It also recognizes
ordinary deterministic `Id`-monad `do` blocks, direct `for` loops over audited
finite containers, and explicit-fuel pure loops from
`EconCSLib.OpenProblem.Util.FiniteControl`. The generated report
contains a symbolic cost expression, a polynomial degree upper bound when one
is available, construct counts, every expanded helper and primitive, and a
deduplicated list of unresolved obligations.

The reader treats overloaded arithmetic as one unit only on admitted scalar
types using an audited standard scalar instance. A local replacement of
`HAdd Nat Nat Nat`, a non-scalar `HAdd`, a function-valued structure field, or
a runtime callback is not silently charged one unit. Opaque/foreign solvers and oracles
can be declared in the source model with, for example,

```lean
source_cost_contract solver := polynomial 3
source_cost_contract traversal := linear_callbacks 0
```

Such assumptions persist through module imports and are displayed under
`assumed source contracts`.  Reports using them say
`CONDITIONAL-SYNTAX-POLYNOMIAL`; a proof-backed semantic result still needs the
local bound required by `AlgorithmCost.external`.

The source variable `n` is a dominating algorithmic size parameter. A runtime
natural or runtime container contributes `n`; explicit arithmetic bounds and
explicitly constructed standard containers are analyzed compositionally.
For example, a fuel value `n * n` yields a quadratic loop bound, whereas
`2 ^ n` yields an extracted exponential bound. The statuses distinguish a
complete polynomial certificate, a complete extracted bound rejected by the
polynomial checker, and a genuinely unresolved cost obligation. The command
`#guard_source_cost` makes all three outcomes regression-testable.

Relating this convention to a particular `sizeOf : Input → ℕ` is necessarily
domain-specific. Consequently this reader is total as a diagnostic but not a
universal semantic decider: it reports an unresolved obligation whenever a
decrease argument, input-size relation, callback contract, custom iterator,
or external implementation is unavailable. This is required for soundness;
no program can decide exact polynomial-time behavior for every arbitrary Lean
function.

## Resource conventions

- One permitted RAM/BSS primitive costs one local step.
- Reading or writing a variable-length block costs the number of transferred
  words; only the internal work of a declared external oracle is abstracted.
- An exact real occupies one word; this is not a bit-complexity claim.
- Oracle calls, distribution samples, random bits, communication units, and
  peak live cells are separate counters.
- A continuous real sample is a distribution-sampling operation, not a finite
  string of random bits.
- Multi-parameter polynomial bounds use the sum of nonnegative size
  parameters.  This is equivalent to a multivariate polynomial bound when the
  parameter list is fixed.
- Family-level predicates choose their coefficient and exponent before the
  domain/algorithm index, preventing nonuniform constants from depending on
  the instance size.
- Genuine uniform polynomial time additionally uses one program for the whole
  indexed family (`FixedEncodingFunctionFamily`).  Uniform constants alone do
  not rule out nonuniform program advice.
- In a family statement, the intended order is
  `∃ c k, ∀ n m, ∃ Aₙₘ, cost(Aₙₘ) ≤ c * (n + m + 1)^k`; placing `∃ c k`
  inside the `∀ n m` block does not express a uniform polynomial-time family.

## Sources

- S. A. Cook and R. A. Reckhow, “Time Bounded Random Access Machines,”
  *Journal of Computer and System Sciences* 7 (1973), 354–375.
- L. Blum, M. Shub, and S. Smale, “On a Theory of Computation and Complexity
  over the Real Numbers,” *Bulletin of the AMS* 21 (1989), 1–46.
- N. A. Danielsson, “Lightweight Semiformal Time Complexity Analysis for
  Purely Functional Data Structures,” POPL 2008.
- Shreyas Srinivas, *Algolean*: a Lean free-monad/query-combinator framework
  with explicit primitive operations and cost models (2026).
- Lean Computer Science Library contributors, `TimeM`/`AddWriter`: writer
  monads for compositional cost semantics.
- R. E. Tarjan, “Amortized Computational Complexity,” *SIAM Journal on
  Algebraic and Discrete Methods* 6 (1985), 306–318.
- A. C.-C. Yao, “Some Complexity Questions Related to Distributive
  Computing,” STOC 1979, 209–213.
- G. E. Blelloch and B. M. Maggs, “Parallel Algorithms,” in the *Handbook of
  Algorithms and Theory of Computation* (work–span framework).
- C. H. Papadimitriou, “On the Complexity of the Parity Argument and Other
  Inefficient Proofs of Existence,” *JCSS* 48 (1994), 498–532.
- OpenAI, `ten-proofs`, especially `GapCVP.lean` (fixed encodings, explicit
  polynomial-time Turing-machine certificates, and polynomial-time
  composition) and `Permanent.lean` (finite arithmetic-circuit syntax).

These interfaces do not claim that unit-cost real-RAM complexity equals
Turing bit complexity.  A problem requiring bit complexity must use a binary
encoding and bit-sized arithmetic costs instead of exact-real words.
