# Finite EFG representations and canonical compilation

**Status:** audited against Lean source, 2026-08-12

This note records the canonical compilation path among the finite extensive
game presentations that predate the history-indexed observed-EFG layer.  It is
an API map, not a claim that the source types are mutually isomorphic.

## 1. Representation matrix

| Representation | Player and chance nodes | History or node identity | Information | Payoff | Termination | Current evaluator | Compiler or semantic bridge |
|---|---|---|---|---|---|---|---|
| `GameTree N U` | `Node mover head tail`; no chance constructor | The value is a subtree. The endpoint compiler therefore identifies equal subtree values; the occurrence compiler uses complete typed histories and does not | Perfect information is implicit in the syntax. The endpoint compiler exposes node context; the occurrence compiler gives each player-controlled complete history a singleton information state | A leaf stores `N → U` | Structurally finite; `size` supports strong induction and total stopped-play proofs | Structural `outcome`, backward induction, global endpoint-policy optimality, Nash/SPE and Zermelo specializations | `toObservedGame` preserves the historical endpoint strategy language. `toOccurrenceObservedGame` is the canonical perfect-information presentation. The latter refines, but is not generally strictly isomorphic to, the former |
| `StochasticGameTree N` | `Player mover arity child`; `Chance arity child law`, with `law : PMF (Fin (arity + 1))` | Source policies receive the numeric occurrence path. The compiler state is the subtree but observations and information states are complete typed histories | Perfect information by occurrence after compilation | A leaf stores `N → ℝ`; the compiled total field is zero away from leaves | The inductive tree is finite, but the legacy executable API exposes an explicit fuel rather than a public total-depth certificate | `expectedPayoffWithFuel` / `expectedPayoffAtFuel` | `toObservedChanceGame`; pure policy to Dirac behavioral profile; exact bounded endpoint and vector-payoff `PMF` equalities; exact source-unilateral-deviation commutation |
| `ZeroSumChance.GameTree` | Binary `Pnode`; binary `Nnode` with `prob : Set.Icc (0 : ℚ) 1` | A strategy is `GameTree → GameTree → Select`, so it sees the ordered pair of child values, not a complete occurrence | Perfect information is implicit, but repeated equal child pairs are intentionally identified by the strategy type | One scalar `ℚ` value for A; B is understood to receive its negation | Structurally finite | Exact rational `value`, `outcome`, maximin/minimax strategies, and saddle theorems | No whole-API lossless compiler yet. The rational syntax remains a specialized proof/evaluation layer; see §4 |
| `FiniteImperfectGame N U` | `mover : State → Option N`; a nonterminal `none` state is chance, but the legacy record stores no chance law | Compact state identity can merge different histories. `toExtensiveGame` reuses the state transition system; the observed compiler indexes observations over its complete typed unfolding | Optional raw labels, one abstract `InfoAction` per label, and explicit concrete action equivalences. Unlabeled player nodes become singleton information states during compilation | Total `State → N → U`, semantically relevant at terminals | Only `State` is structurally finite. Cycles and nontermination remain possible | No source execution or equilibrium evaluator | `ObservedCompiler.toObservedGame`; new `ObservedChanceCompiler.toObservedChanceGame` adds a state-indexed normalized chance law without changing the legacy record |
| `ObservedGame N U` | `ExtensiveGame.mover`; chance states are identified but carry no law | Complete dependent histories are first-class; endpoints may still merge in the base Arena without merging histories | The minimal decision layer has player-indexed raw `InfoState`, represented decision coordinates, `InfoAction`, and concrete action equivalences; private/public observations are an additive extension | Total base payoff, consumed semantically at terminal histories | Not structural; theorem-local termination or stopped finite fuel | Pure stopped execution and continuation semantics; strategies range only over `RepresentedInfo` | Canonical deterministic/structural theorem target; attach `NoChance` or an explicit chance kernel before stochastic behavioral execution |
| `ObservedChanceGame N U` | Same observed base plus a normalized history-indexed legal-action `PMF` at every chance history | Complete dependent histories | Same full observed information presentation | Same terminal payoff vector | Not structural; finite-fuel laws are total, total outcomes require explicit termination or limit hypotheses | Behavioral and mixed bounded history/payoff laws; discrete infinite-path and analytic extensions; Nash/SPE layers under their stated hypotheses | Preferred canonical stochastic EFG target. Strict isomorphism, information refinement, coupling, and weak simulation remain distinct relation classes |

The two source notions called “finite” are different. `GameTree` and
`StochasticGameTree` are structurally finite inductive values.
`FiniteImperfectGame` only supplies a `Fintype State`; it may contain cycles.

## 2. Recommended canonical routes

```text
GameTree
  ├─ endpoint compatibility compiler ───────────────▶ ObservedGame
  └─ occurrence compiler (preferred) ──────────────▶ ObservedGame
                                                        │
                                           NoChance / explicit kernel
                                                        ▼
StochasticGameTree ── occurrence compiler ────────▶ ObservedChanceGame
                                                        ▲
FiniteImperfectGame + ObservedChanceCompiler ──────────┘

ZeroSumChance.GameTree ── retained exact-ℚ specialist layer
                          (future certified relation, not an assumed iso)
```

`ObservedChanceGame` is the preferred target when chance or behavioral laws
matter. `ObservedGame` remains the right target for structural information,
pure play, and no-chance results. A deterministic game should use the existing
`ObservedChanceGame.ofNoChance` route rather than invent dummy chance nodes.

The `GameTree` endpoint compiler remains compatibility support because its
strategy type is already used by downstream proofs. New perfect-information
EFG work should prefer the occurrence compiler.

## 3. Implemented preservation boundaries

### `StochasticGameTree → ObservedChanceGame`

The compiler in
`Compiler/StochasticGameTreeObserved.lean` has the following checked
properties.

| Property | Lean witness | Strength and boundary |
|---|---|---|
| Legal player execution | `policyHistoryPolicy_player` | The induced history policy is the Dirac law at exactly the source path-sensitive choice |
| Legal chance execution | `policyHistoryPolicy_chance` | The constructor `PMF` is reused exactly; it is neither inferred nor renormalized |
| Bounded terminal/endpoint distribution | `stochasticHistoryPMFFrom_map_endpoint` | Exact equality after mapping complete target histories to endpoint subtrees |
| Payoff distribution | `stochasticHistoryPMFFrom_map_payoff` | Exact equality of vector-valued payoff `PMF`s for the total compiled payoff field; at leaves this is exactly the source payoff |
| Unilateral pure deviation | `policyToBehavioralProfile_deviate` | Translating a source `Policy.IVariant` commutes exactly with target profile update |

The endpoint-law theorem is deliberately not called an isomorphism. Mapping a
complete history to its endpoint forgets occurrence identity and is generally
noninjective.

The legacy source has no Nash or SPE predicate. Moreover, the target
behavioral strategy space contains randomized deviations that are not source
pure policies. Therefore the current bridge does not claim Nash or SPE
transfer. Such a theorem needs either a source behavioral strategy language
and deviation-surjectivity proof, or a separate finite perfect-information
purification/backward-induction theorem.

`expectedPayoffWithFuel` returns zero at fuel zero, even at a leaf, whereas
stopped target execution at fuel zero retains the current history and its
terminal payoff. The exact invariant is consequently the endpoint/payoff law
at the same execution horizon; any scalar expectation wrapper must state the
legacy evaluator's one-step convention explicitly rather than use a false
definitional equality.

### `FiniteImperfectGame + chance law → ObservedChanceGame`

`ObservedChanceCompiler` extends the existing compiler certificate with

```lean
chanceLaw :
  (state : G.State) →
    G.toExtensiveGame.isChanceState state →
    PMF (G.Action state)
```

`toObservedChanceGame` preserves the existing `ObservedGame` projection
definitionally, and `toHistoryPolicy_of_chance` proves that behavioral
execution uses the supplied state law exactly at every complete history ending
there.

This route is lossless for the data the compact source actually stores:
dynamics, movers, concrete actions, labeled information action equivalences,
terminal payoff, designated roots, and the new chance law. It does not invent
missing nonacting-player observations or public information; those remain the
existing conservative `none`/`Unit` presentation. A state-indexed chance law
also intentionally assigns the same law to every complete history with the
same endpoint state. Clients needing history-dependent nature must construct
an `ObservedChanceGame` directly.

The source has no evaluator, termination certificate, behavioral strategy
space, Nash predicate, or SPE predicate, so there is nothing source-side to
transfer for those notions. Finiteness of `State` alone is insufficient:
a one-state nonterminal self-loop is a counterexample to automatic
termination. The compiler therefore makes no termination claim.

## 4. Why `ZeroSumChance.GameTree` is retained

There is a straightforward *data* embedding into a binary stochastic tree:
cast the rational probability and terminal value to real numbers and assign
payoffs `(r, -r)`. It is not yet a lossless bridge for the existing whole API.

The obstruction is strategic, not numeric. Suppose the same ordered child pair
`(L, R)` appears at two different player occurrences. A source
`Strategy = GameTree → GameTree → Select` must make the same choice at both.
An occurrence-observed target strategy can choose left at one occurrence and
right at the other. Target behavioral strategies add randomized deviations as
well. Thus the obvious forward map is not deviation-surjective, so it cannot
justify two-way Nash/SPE transfer or a strict strategy isomorphism.

The exact `ℚ` evaluator and saddle proofs are also useful computationally and
should not be replaced by a real-valued PMF evaluator merely for uniformity.
The retained module is therefore a specialized proof language, not the
canonical general EFG model.

A safe staged plan is:

1. add a binary rational-law adapter and prove leaf and chance-weight
   preservation;
2. define an explicit endpoint-information refinement from the occurrence
   target and prove casted `outcome` preservation for translated source
   strategy pairs;
3. expose only directional equilibrium transfer unless a separately stated
   occurrence-consistency/deviation-coverage hypothesis is proved.

No existing declaration is deprecated until those theorems exist.

## 5. Compatibility and record migration

This change adds declarations and one opt-in import to
`Interface.Compilation.Discrete`; it does not rename existing declarations or
change any existing record field.

In particular, adding `chanceLaw` directly to `FiniteImperfectGame` would be a
source-breaking record change. Lean record fields cannot be preserved by an
ordinary compatibility alias: every record literal would still need the new
field, and old projections cannot manufacture history-dependent probability
data. The separate `ObservedChanceCompiler` certificate is the migration
mechanism:

```lean
def compiler : G.ObservedChanceCompiler :=
  FiniteImperfectGame.ObservedChanceCompiler.initialRoot
    infoWellFormed
    chanceLaw
```

Existing clients that need only `ObservedGame` keep using
`ObservedCompiler` unchanged. Chance-aware clients opt into the new
certificate and then call `compiler.toObservedChanceGame`.

## 6. Boundaries Lean imports cannot enforce

Lean imports can enforce that the governed root does not expose these reference
compilers and that `Interface.Compilation.Discrete` does not pull in the
analytic kernel stack. They cannot enforce semantic authoring rules such as:

- using terminal payoffs only at terminal histories;
- choosing occurrence rather than endpoint information for a new theorem;
- supplying economically correct chance laws;
- treating `Unit` public observation as a conservative placeholder rather
  than a claim of public equivalence;
- proving termination for a cyclic finite-state presentation;
- calling a relation an isomorphism only when its maps are bijective and its
  chance/action/information diagrams commute;
- deriving Nash/SPE transfer only after the target deviation space is covered.

Those remain theorem hypotheses, explicit certificates, review rules, and
regression examples rather than import-boundary properties.
