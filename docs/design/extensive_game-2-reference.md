# Extensive Games — Detailed API Reference

Developer-facing design notes for the **finite perfect-information, no-chance**
extensive-game line in `EconCSLib/GameTheory/ExtensiveGame/`, built on the
inductive `GameTree` type: **how the Lean API is built** — the data model, where
each typeclass assumption enters, and how backward induction climbs from a value
function to Kuhn's SPE-existence theorem and Zermelo determinacy.

> Scope. This continuation records the detailed **`GameTree`** API and the
> theorem-by-theorem relationship with the simulation-oriented Arena stack.
> It covers the **`GameTree`** files (`GameTree`, `BackwardInduction`,
> `GameTreeSPE`, `GameTreeNE`, `GameTreeStrategicForm`, `Zermelo`, plus the
> `Examples/SimpleGameTree` smoke test). The *other* extensive-game framework —
> the state-space **`Arena`** model (`Basic`/`Strategy`/`Play`/`Subgame`), which
> supports infinite state spaces — is a separate design and is cross-referenced
> here. The implemented history-indexed observed-EFG framework compiles
> `GameTree` into that layer and proves strategy/outcome recovery; see
> [`../research/extensive_game_architecture.md`](../research/extensive_game_architecture.md).

Continuation of the [main extensive-game design note](extensive_game.md).
Complements, does not replace:

- [`docs/design.md`](../design.md) — project-wide architecture and rules.
- `docs/knowledge/` — the published mathematical blueprint (textbook layer).

## Design principles, as they land here

1. **Bourbaki discipline.** `GameTree N U` constrains *neither* `N` nor `U`: no
   `Fintype`, no `DecidableEq`, no order. Finiteness is structural (the inductive
   type); `[TotalPreorder U]` is added only at the theorems that compare payoffs.
2. **Minimal order, no field.** The entire value / SPE / Kuhn stack needs only
   `[TotalPreorder U]` (reflexive + transitive + total) and a decidable
   comparison `[DecidableLE U]` for backward-induction choice — *no*
   antisymmetry and *no* arithmetic. Numbers (`ℚ`) enter only in the zero-sum
   `Zermelo` layer, where sums and negation are genuinely used.
3. **Stable predicates over wrappers.** Equilibria are predicates on
   strategies, not bespoke structures. Within the historical endpoint
   `GameTree` API, structural descendants use `Subtree`; canonical standard
   subgames use occurrence histories satisfying
   `ObservedGame.IsLawfulSubgameRoot` and a complete `SubgameSystem`.
4. **One "Kuhn".** "Kuhn's theorem" here = backward-induction / SPE existence
   (Kuhn 1953). The *other* Kuhn theorem (mixed ≡ behavioral under perfect
   recall) is formalized in the history-indexed imperfect-information layer.
   Don't conflate them.

## Module map

```
GameTheory/ExtensiveGame/
  GameTree.lean               -- finite no-chance tree frontend
  BackwardInduction.lean      -- computable value recursion (§2)
  Zermelo.lean                -- rational zero-sum saddle theorem (§5)

  Execution/
    History.lean              -- typed histories and Arena unfolding
    StoppedExecution.lean     -- bounded deterministic execution
    StochasticExecution.lean  -- bounded normalized PMF execution
    Discrete/                 -- PMF kernel arena and finite trajectories
    InfiniteTrajectory.lean   -- infinite discrete-event paths

  Relations/Discrete/         -- strict, coupling, and weak relations

  Observed/
    Game.lean                 -- information and lawful subgame roots
    Chance.lean               -- normalized chance kernels
    SPE.lean                  -- lawful-root and standard SPE
    PerfectRecall.lean
    Behavior.lean
    Mixed.lean
    Kuhn.lean
    Morphism*/ Refinement*    -- exact structural transfer
    Continuation.lean         -- representation-neutral adapter

  Simulation/
    Kernel/                   -- non-atomic analytic execution
    Presentation/             -- measurable observed/chance adapters
    Equilibrium/ Continuation/ Restart/

  Compiler/
    GameTreeOccurrenceObserved.lean -- canonical occurrence bridge
    GameTreeObserved.lean           -- historical endpoint bridge

  Interface/
    Core.lean
    Execution/{Finite,Infinite,Analytic}.lean
    Relations/Discrete.lean
    Equilibrium/{Discrete,Analytic}.lean
    Restart.lean
    Compilation/Discrete.lean
```

The former complete-stack aggregate was deleted before API stability. New
code imports the smallest granular facade above and combines sibling branches
explicitly. The complete lifecycle register is
[`efg-module-status.md`](efg-module-status.md), and the supported declaration
surface is documented in [`efg-public-api.md`](efg-public-api.md).

Conventions: `[MSZ, Ch. 3]` = Maschler/Solan/Zamir, *Game Theory* (Cambridge,
2013), extensive games. "Minimal assumptions" lists what a declaration needs on
top of the always-present `{N U : Type*}`. Signatures abbreviated; source is
authoritative.

---

## 1. Core model — the `GameTree` type

File: [`GameTree.lean`](../../EconCSLib/GameTheory/ExtensiveGame/GameTree.lean)

```lean
inductive GameTree (N : Type*) (U : Type*) : Type _
  | Leaf (payoff : N → U)
  | Node (mover : N) (head : GameTree N U) (tail : List (GameTree N U))
```

| name | Minimal assumptions | Meaning |
|------|--------------------|---------|
| `GameTree N U` | **none** | Finite perfect-info game: players `N`, payoffs `U`. |
| `Leaf payoff` | none | Terminal node with payoff vector `N → U`. |
| `Node mover head tail` | none | Decision node owned by `mover`, children `head :: tail`. |

Two modelling choices are load-bearing:

- **Finiteness is the inductive type itself** — no separate well-foundedness
  hypothesis is ever needed.
- **Children are non-empty by construction.** A `Node` carries `head` *plus*
  `tail : List`, so `children = head :: tail` is always non-empty
  (`children_node_ne_nil`). This is why backward induction can always pick a
  child — there is no empty-node edge case.
- **No `Nature` constructor.** The core stays chance-free. Separate stochastic
  tree modules model chance where the additional utility infrastructure is
  appropriate.

The supporting vocabulary every later proof leans on:

| name | Meaning |
|------|---------|
| `size` | structural size (`Leaf = 1`, `Node = 1 + head + Σ tail`); `size_pos`, `size_mem_children_lt` feed well-founded recursion. |
| `Subtree s g` | `s` occurs structurally inside `g` (reflexive / in head / in a tail child). This is not by itself an observed-game lawfulness certificate. |
| `strong_induction` | to prove `motive g`, handle `Leaf` and each `Node` given the motive for **every** child. Stronger than the default recursor (which gives IH on the head only) — exactly what backward induction needs. |

`strong_induction` is the workhorse: `value`, `outcome`, and every zero-sum
invariant are proved by it.

---

## 2. Backward-induction value

File: [`BackwardInduction.lean`](../../EconCSLib/GameTheory/ExtensiveGame/BackwardInduction.lean)

```lean
mutual
  def value : GameTree N U → (N → U)
    | Leaf p => p
    | Node m h t => List.argMaxOn (fun v => v m) (value h) (valueList t)
  def valueList : List (GameTree N U) → List (N → U)
    | [] => [] | x :: xs => value x :: valueList xs
end
```

| name | Minimal assumptions | Meaning |
|------|--------------------|---------|
| `value g` | `[TotalPreorder U] [DecidableLE U]` | BI value vector: at a `Node`, the mover picks a child maximizing *their own* coordinate. |
| `value_Node_ge` | same | the mover's coordinate of `value (Node …)` dominates every child's. |
| `value_Node_eq_some_child_value` | same | `value (Node …)` *is* the value of some child (the argmax). |

`value` is computable: `argMaxOn` folds over the finite child list using
`[DecidableLE U]`. The two lemmas are the entire interface used downstream: one
gives optimality (`≥` every child for the mover), the other says the optimum is
realized by an actual child.  The canonical strategy remains `noncomputable`
because it chooses a child witness from the realization theorem.

---

## 3. Strategies, outcome, and the BI strategy

File: [`GameTreeSPE.lean`](../../EconCSLib/GameTheory/ExtensiveGame/GameTreeSPE.lean)

```lean
def Strategy (N U) := (m : N) → (h : GameTree N U) → (t : List (GameTree N U)) →
  { c : GameTree N U // c ∈ h :: t }
noncomputable def outcome (σ : Strategy N U) : GameTree N U → (N → U)
def optStrategy : Strategy N U          -- picks an argmax child at every node
def IVariant (i) (σ σ') : Prop          -- σ, σ' agree on every node with mover ≠ i
```

| name | Minimal assumptions | Meaning |
|------|--------------------|---------|
| `Strategy N U` | none | A **global** child-selector at every `(mover, head, tail)`, bundled with the membership proof. Covers all players at once. |
| `outcome σ g` | none | The leaf payoff reached by following `σ` from `g` (well-founded on `size`). |
| `optStrategy` | `[TotalPreorder U] [DecidableLE U]` | Canonical BI strategy: picks a child whose value equals the node's value. `noncomputable` (classical choice). |
| `IVariant i σ σ'` | none | `σ'` is a unilateral deviation by player `i` only. |
| `outcome_optStrategy_eq_value` | `[TotalPreorder U] [DecidableLE U]` | the bridge: `outcome optStrategy g = value g`. |

A single `Strategy` is **player-agnostic** (one function for all movers); a
"player-`i` strategy" is conceptualised as its behaviour on `mover = i` nodes,
and `IVariant i` captures "change only player `i`'s choices". `outcome` is a
tree walk; `outcome_optStrategy_eq_value` is the load-bearing lemma that lets
every value fact transfer to an actual play.

---

## 4. Equilibrium and Kuhn's theorem

Files: [`GameTreeSPE.lean`](../../EconCSLib/GameTheory/ExtensiveGame/GameTreeSPE.lean),
[`GameTreeNE.lean`](../../EconCSLib/GameTheory/ExtensiveGame/GameTreeNE.lean)

```lean
def IsGlobalEndpointSubgamePerfect (σ) : Prop :=                 -- global: optimal at every tree
  ∀ g i σ', IVariant i σ σ' → outcome σ' g i ≤ outcome σ g i
def IsNashEquilibrium (σ) (g) : Prop :=            -- root-scoped (GameTreeNE)
  ∀ i σ', IVariant i σ σ' → outcome σ' g i ≤ outcome σ g i
def IsGlobalEndpointSubgamePerfectOn (σ) (g) : Prop :=           -- SPE on subgames of a fixed root
  ∀ s, Subtree s g → IsNashEquilibrium σ s
```

| name | Minimal assumptions | Meaning |
|------|--------------------|---------|
| `IsGlobalEndpointSubgamePerfect σ` | `[TotalPreorder U]` | Historical endpoint-policy predicate: no `i`-deviation improves `i` at any tree value. |
| `IsNashEquilibrium σ g` | same | Same, but only at the fixed root `g`. Weaker — allows off-path threats. |
| `IsGlobalEndpointSubgamePerfectOn σ g` | same | Endpoint-policy NE at every structural subtree of `g`; not the canonical occurrence-sensitive standard-SPE predicate. |
| `optStrategy_isGlobalEndpointSubgamePerfect` | plus `[DecidableLE U]` | Backward-induction optimality for the historical global endpoint policy. |
| `Kuhn_exists_globalEndpointSPE` | plus `[DecidableLE U]` | Existence for that historical endpoint-policy predicate. |
| `Kuhn_exists_globalEndpointSPE_on g` / `Kuhn_exists_NE g` | plus `[DecidableLE U]` | Structural-subtree endpoint optimality / root NE existence at `g`. |
| `IsGlobalEndpointSubgamePerfect.toNE` | `[TotalPreorder U]` | The historical global endpoint predicate implies root NE. |

`optStrategy_isGlobalEndpointSubgamePerfect` is proved by `strong_induction`: at a node owned
by the deviating player `i`, the deviation lands in some child where the IH plus
`value_Node_ge` caps it; at any other node, `IVariant` forces the same child and
the IH applies directly. Existence (`Kuhn_exists_globalEndpointSPE*`) is then
immediate. Canonical standard SPE is obtained after compiling to
`GameTree.toOccurrenceObservedGame`, whose
`occurrenceCompleteSubgameSystem` selects every history occurrence; the
endpoint predicate alone must not be used as a replacement for that result.
`GameTreeStrategicForm.lean` additionally bridges a tree to the normal-form
`StrategicGame` (`toStrategicGame`, `toStrategicGame_nash_iff_isNashAt`).

**Kuhn naming.** This is the backward-induction theorem (Kuhn 1953). The
behavioral-strategy realization theorem is a different result, formalized for
finite perfect-recall observed EFGs in `KuhnConditioning.lean`.

---

## 5. Zero-sum specialization — Zermelo determinacy

File: [`Zermelo.lean`](../../EconCSLib/GameTheory/ExtensiveGame/Zermelo.lean)

This is the only GameTree file that uses `ℚ`: zero-sum needs sums and negation.

```lean
def IsZeroSum : GameTree (Fin 2) ℚ → Prop        -- payoffs sum to 0 at every leaf
noncomputable def value₀ (g) : ℚ := (value g) 0  -- player 0's value
```

| name | Minimal assumptions | Meaning |
|------|--------------------|---------|
| `IsZeroSum g` | `Fin 2`, `ℚ` | `p 0 + p 1 = 0` at every leaf (propagated over the tree). |
| `IsZeroSum.of_subtree` | same | zero-sum is inherited by every subgame. |
| `value_zero_sum` | same | the BI value vector is zero-sum: `value g 0 + value g 1 = 0`. |
| `value_one_eq_neg_value₀` | same | `value g 1 = -value₀ g`. |
| `outcome_zero_sum` | same | **any** strategy's terminal outcome is zero-sum. |
| `value₀_Node_zero_isMax` / `value₀_Node_one_isMin` | same | player 0 maximizes `value₀` at their nodes; player 1 minimizes it at theirs. |
| `value₀_eq_outcome_and_zeroSum` | same | packaging: `optStrategy` realizes `value₀`, value vector is zero-sum. *Not* a minimax statement. |
| **`zermelo_determinacy`** | same | **determinacy / saddle value** (below). |
| `zermelo_exists_pure_globalEndpointSPE_on` / `zermelo_exists_pure_NE` | same | `Fin 2`/`ℚ` structural endpoint / root-Nash instances — **no** zero-sum hypothesis needed. |

```lean
theorem zermelo_determinacy (g : GameTree (Fin 2) ℚ) (hzs : IsZeroSum g) :
    (∀ σ', IVariant 1 optStrategy σ' → value₀ g ≤ outcome σ' g 0) ∧   -- P0 secures ≥ value₀
    (∀ σ', IVariant 0 optStrategy σ' → outcome σ' g 0 ≤ value₀ g)     -- P1 caps  ≤ value₀
```

`zermelo_determinacy` is **the genuine Zermelo content**: `optStrategy` is a
saddle point with value `value₀ g`. Player 0, playing `optStrategy`, secures at
least `value₀ g` against every opponent play; player 1, playing `optStrategy`,
holds player 0 to at most `value₀ g`. The two directions come from
`optStrategy_isGlobalEndpointSubgamePerfect` at `i = 1` and `i = 0` respectively, with the
player-0 side closing via `outcome_zero_sum` (`outcome σ' g 0 = -outcome σ' g 1`).

The split between the layers is the design point:

- existence of an equilibrium is **Kuhn**, needs only `[TotalPreorder U]`, and
  does *not* use zero-sum — hence
  `zermelo_exists_pure_globalEndpointSPE_on`/`zermelo_exists_pure_NE` carry no
  `IsZeroSum` hypothesis;
- the **value** being determined (a saddle) is **Zermelo**, and is exactly where
  the zero-sum hypothesis does real work.

---

## Relation to the Arena framework

`GameTree` is an inductive specialization for finite perfect-information games.
The `Arena` framework (`ExtensiveGame/{Basic,Strategy,Play,Subgame}.lean` plus
`ExtensiveGame/Execution/History.lean`) is a state-space model that also
represents infinite and cyclic dynamics.
`History.lean` separates world states from action histories and supplies the
history unfolding; `FiniteArenaExtraction.lean` records assumptions for the
partial Arena-to-tree direction.

`StoppedExecution.lean` repairs the operational terminal boundary: a
`HistoryPolicy` is queried only with a proof that its endpoint is nonterminal.
`Morphism.lean` maps typed histories through strict Arena morphisms, proves
stopped-execution naturality under explicit terminal/policy preservation, and
defines relational simulations and bisimulations for non-functional
correspondences.
`Game.lean` separates observations at every history from decision information;
strategies index abstract actions by the represented-information subtype rather
than by unused raw information values.
`PerfectRecall.lean` extracts each player's ordered history of prior
decision information states and own abstract actions. Equality of current
information states must preserve that sequence; strict observed-EFG
isomorphisms preserve and reflect this perfect-recall predicate.
Perfect recall now also implies `NoAbsentMindedness`: after a player acts at
an information state, no extension of that history can ask the same player to
act at the same information state again. This is the structural freshness
condition used when comparing a pre-sampled pure-plan table with on-demand
behavioral randomization.
`RecallCertificate` is the compiler-facing factorization form: it assigns one
remembered personal-decision sequence to every information state and proves
that assignment agrees with every represented complete history. Certificate
existence is equivalent to perfect recall and is invariant under strict
observed-EFG isomorphism.
`GameTreeObserved.lean` validates the interface by proving
`playerStrategyEquiv`, plus stopped-history and stopped-payoff equality with
the existing `GameTree.outcome` for both global strategies and normal-form
player profiles.  It additionally packages the two strategy/outcome semantics
as a `GameForm.Iso` and proves pure-Nash equivalence with the existing
root-scoped `GameTree.IsNashAt`. Its endpoint-based information states
intentionally preserve the historical `GameTree.PlayerStrategy` API, so equal
subtree values at distinct occurrences may be identified.

`GameTreeOccurrenceObserved.lean` supplies the complementary
occurrence-sensitive compiler. Its private and public observations are complete
typed histories, and its decision information states are player-controlled
history occurrences. It therefore has perfect information and perfect recall.
Explicit forgetting maps send occurrence observations and information states
to the endpoint compiler; every endpoint pure profile lifts to the occurrence
compiler with exactly the same concrete history policy, stopped history, and
bounded terminal payoff. The two compilers are not claimed to be strictly
isomorphic: forgetting an occurrence can be non-injective, and the occurrence
model admits contingent plans that the endpoint model deliberately identifies.
`not_injective_forgetOccurrenceInfo_of_merged_histories` makes this obstruction
explicit whenever two distinct player histories merge at one decision node.
`endpointInformationRefinement` packages this bridge in the generic refinement
API. The occurrence compiler terminates under all path-dependent profiles, so
both bounded and termination-certified pure SPE reflection are available.

`FiniteImperfectObserved.lean` gives the compact
`FiniteImperfectGame` presentation a conservative route into this theorem
layer. A player node labeled `some k` receives a shared, player-indexed
decision information state; a node labeled `none` receives a singleton
decision information state. Each label declares one abstract `InfoAction`
type, and an explicit `actionEquiv` transports it to every concrete node
carrying the label. The acting
player observes precisely this completed information, while other-player and
public observations are trivial because the compact structure contains no such
data. Presentation-designated continuation roots are explicit
compiler-certificate data; standard subgames require a separate lawful
`SubgameSystem`.

The compact `PureStrategy` and compiled `ObservedGame.PureStrategy` are both
genuinely information-indexed and cannot prescribe different abstract actions
at two states carrying the same label. The compiler adds singleton information
for unlabeled player decisions rather than claiming a literal strategy-space
isomorphism. The tiny imperfect-information regression proves that its left
and right hidden nodes compile to one information state and hence receive one
packaged abstract choice. It also supplies a `RecallCertificate`: both
hidden histories are player 1's first decision, so their shared current
information state consistently remembers the empty personal-decision
sequence. Thus the compiled imperfect-information game has perfect recall
without having singleton information.

`Morphism.lean` strengthens this semantic bridge at the EFG layer. Its strict
history-Arena isomorphism preserves private observations, public states,
information-indexed actions, terminal payoffs, and
presentation-designated continuation roots. It induces exact bounded
continuation game-form isomorphisms and transports explicit lawful subgame
systems separately.

`SPE.lean` adds the termination certificate required for total outcomes on a
general Arena. The bound may depend on the lawful subgame root and pure
profile; terminal-run uniqueness proves that the resulting payoff is
independent of the selected witness. Strict observed-EFG isomorphisms preserve
termination, total continuation outcomes, subgame perfection on transported
lawful systems, and complete standard pure SPE in both directions.
`GameTreeObserved.lean` instead identifies the endpoint compiler's
Nash predicate on presentation-designated continuations with the structural
endpoint-policy predicate
`GameTree.IsGlobalEndpointSubgamePerfectOn`. Canonical standard SPE for a
root-bound finite tree is supplied by the occurrence-sensitive compiler and
its all-history `CompleteSubgameSystem`.

`Refinement.lean` handles changes of information structure. Complete
history dynamics remain strictly isomorphic, while private observations,
public states, and decision information forget from a finer game to a coarser
game. Coarse strategies lift through indexed action equivalences with exact
bounded and total terminal outcomes. Refinements have identity and composition
operations. Nash and pure SPE reflect from the lifted fine profile to its
coarse source. The converse is exposed only under the explicit
`StrategySurjective` hypothesis saying that every fine deviation lifts from a
coarse strategy.

`Chance.lean` attaches a normalized `PMF` to every nonterminal chance
history. Its strict isomorphism requires exact equality after pushing the
source kernel through the dependent action equivalence.
`Behavior.lean` defines behavioral strategies directly on decision
information states, with normalized laws on the corresponding indexed
abstract actions. For an observed chance EFG, such a profile induces a genuine
history policy whose player laws are the transported behavioral laws and whose
chance laws are the declared kernels exactly.
`BehaviorMorphism.lean` strengthens strict observed-EFG isomorphism
with a local information-action/concrete-action coherence square. It transports
behavioral strategies and profiles by exact PMF pushforward, proves equality
of every bounded continuation history law and optional-terminal-payoff law,
and derives two-way behavioral Nash and bounded behavioral Nash on
presentation-designated continuations at corresponding designated roots.
`BehaviorRefinement.lean` adds exact chance-law and behavioral-policy
naturality to information refinements. `Continuation.lean` compiles
pure and behavioral refinements to representation-neutral continuation
morphisms and graph-root simulations; the latter compose directly with
relational weak-serialization simulations.
`Realization.lean` factors the same bounded behavioral semantics
through `LawGameForm`: the underlying outcome is an optional terminal payoff
vector and the evaluator directly returns its `PMF`. Its deterministic
`toGameForm` view is definitionally the existing behavioral continuation game
form. Strict observed chance-EFG isomorphisms induce law-game isomorphisms;
chance-aware information refinements induce law-game morphisms. In both cases
the exact payoff-law theorem is exposed uniformly as
`LawGameForm.RealizesVia`; the root-scoped conditional mixed-to-behavioral
construction later instantiates this interface.
`Mixed.lean` supplies the complementary classical mixed semantics.
Each player's mixed strategy is a `PMF` on that player's complete
information-indexed pure contingent plan. For a finite player type,
`PMF.fintypePi` independently samples those plans once before play; it is not
an arbitrary correlated law on pure profiles. The sampled profile is embedded
as point-mass behavioral choices and then executed against the genuine chance
kernels. Dirac mixing is proved equal to pure-as-behavioral execution. Strict
observed chance-EFG isomorphisms commute with the independent product and the
complete bounded payoff law, yielding exact mixed-law game-form isomorphisms
and two-way bounded mixed Nash on presentation-designated continuations transfer.
`Kuhn.lean` separates the next theorem boundary from strict
isomorphism. A root-scoped mixed/behavioral realization certificate asks for a
playerwise behavioralization map, exact bounded payoff-law equality, and
semantic coverage of every unilateral behavioral deviation by a mixed
deviation. This induces a `LawGameForm.Hom` and two-way Nash transfer even
though the strategy map need not be surjective. A deliberately stronger
continuation-wide certificate induces a `ContinuationGameForm.Hom` and
bounded designated-continuation Nash transfer. The distinction is necessary: perfect recall gives the
standard root-scoped Kuhn realization, but ex-ante correlations inside an
arbitrary mixed plan need not admit one behavioralization that preserves every
off-path continuation simultaneously. For finite represented
decision-information spaces,
the behavioral-to-mixed construction is implemented by independently sampling
one action at each represented information coordinate, with every local
marginal proved equal to the source behavioral law. The corresponding concrete legal-action
marginal at every player history is also proved exact, including the outer
independent product over players.
`DeferredSampling.lean` proves the representation-neutral multi-step
random-table/on-demand theorem. Its typed fresh-query tree may interleave
arbitrary chance draws with adaptive queries; every query removes its key, and
pre-sampling the independent finite table is exactly equal to sampling on
demand as a `PMF`.
`DeferredSampling.lean` compiles bounded observed chance-EFG execution
to that tree. A future-closed availability invariant is preserved by chance
steps and, using `NoAbsentMindedness`, deletes exactly one information key at
each player step. Under `FiniteKuhnHypotheses`, the compiler proves exact
behavioral-to-mixed equality of complete history laws and optional payoff
laws from every continuation root and at every fuel. These equations induce
one behavioral-to-mixed `ContinuationGameForm.Hom`. It reflects bounded mixed
SPE to behavioral SPE unconditionally; the converse is stated precisely
under rootwise semantic deviation completeness, rather than asserting a
false literal strategy-space surjectivity.
`ConditionalSampling.lean` and `ConditionalProduct.lean` provide normalized
fiber conditioning, exact disintegration, and the coordinate-update theorem
for finite independent dependent products. `KuhnConditioning.lean`
uses those results with perfect recall to condition an arbitrary mixed plan on
the player's continuation-relative personal decision history. It proves exact
bounded history and payoff-law realization from each chosen root, constructs
root-scoped mixed-to-behavioral certificates, proves two-way Nash transfer,
and discharges the semantic-deviation premise of the global
behavioral-to-mixed continuation morphism. Consequently
`isBehavioralNashOnRootsAtFuel_iff_mixed` gives the full two-way bounded
explicit-root Nash
equivalence for a behavioral profile and its independently sampled complete
plans. This remains a realization theorem, not a strict isomorphism of
strategy spaces or a root-independent behavioralization of every arbitrary
mixed profile.
`MorphismHierarchy.lean` proves that every strict observed-EFG
isomorphism is a special information refinement. Its pure and behavioral
strategy lifts agree with the strict transports and are automatically
surjective, so strict explicit-root Nash transfer factors through the same
refinement/continuation theorem path.
`Relations/Discrete/KernelWeakSimulation.lean` supplies the deliberately weaker serialization
layer: source and target endpoint laws must have an exact
relation-supported coupling, and forgetting probabilities yields a proved
progressing `Arena.WeakSimulation`.
`Execution/Discrete/KernelTrajectory.lean` composes those exact couplings under
terminal-aware, coupling-compatible randomized Markov policies. Policies are
queried only at nonterminal states, and executions stop when an action type is
empty. The module proves exact finite-horizon state and complete-trace
couplings, plus equality of pushforward laws for every observable that agrees
on related traces.
`FOSG.lean` provides simultaneous joint actions, stochastic world
transitions, realized history augmentation, private/public observation
histories, and a chance-consistent weak-serialization interface.
`FOSGBehavioralSerialization.lean` adds the reusable finite-player strategic
semantic interface for such serializers. A serializer supplies playerwise
behavioral-strategy equivalences, genuine target payoff laws, exact law
equalities at related macro roots and initialization, and source-root
coverage. The module then constructs a relational-root continuation
simulation and initialized game-form isomorphism, deriving two-way
finite-horizon behavioral Nash on caller-declared macro continuations transfer generically.
`FOSGSequentialization.lean` instantiates that interface for
`Fin (n + 1)` players. It compiles one simultaneous joint action into `n + 1`
hidden player decisions followed by the original transition chance kernel,
proves the exact `n + 2`-step endpoint law and initial-law coupling, exposes the
serializer as a macro-boundary `KernelArena.Simulation`, compiles every
history-level randomized joint-action policy to canonical serialized macro
executions, constructs those joint-action laws from independently randomized
information-indexed behavioral profiles, and proves exact stopped
finite-horizon trace and optional-terminal-payoff-law transfer including random
initialization. Every utility computed from the payoff vector therefore has
the same PMF as well. It also constructs the corresponding genuine target
observed-EFG behavioral profile, proves its local player and chance laws, and
shows that profile compilation commutes exactly with unilateral deviation.
The genuine target policy's full micro execution is proved equal to the
canonical macro-controller mixture for one block and for every stopped finite
macro horizon. Consequently the initialized source and genuine target
optional terminal-payoff PMFs are equal, and an induced `GameForm.Iso` transfers
finite-horizon behavioral Nash equilibrium in both directions. It derives a
progressing support-path weak simulation as well.
`FOSGContinuation.lean` packages those exact concrete laws as a
`WeakSerialization.BehavioralBridge`; its macro-root and full Nash on caller-declared macro continuations
theorems are direct instances of the generic transfer theorem.

The generic discrete event-time boundary now lives in
`Execution/InfiniteTrajectory.lean`. It computes finite path marginals,
unfinished mass, and stopped-payoff laws with `FiniteLaw`; performs
fuel-bounded terminal search with `Option`; and projects complete path and
terminal-payoff probability measures supplied by callers. Exact
finite-marginal and legality statements consume explicit certificates rather
than invoking an internal extension construction. Remaining extensions include
model-specific equilibrium applications, true continuous-time semantics, more
general finite-player index presentations, general imperfect-information
well-formedness, and a direct finite-EFG pure-SPE existence proof independent
of the `GameTree` transfer.

For analytic `MeasurableKernelArena` transitions,
`Simulation/Kernel/StatePath.lean` separately constructs the
Ionescu--Tulcea state-path law. Its coordinate marginals agree exactly with
`Simulation.Kernel.Endpoint`, so an embedded discrete policy recovers
`KernelArena.stateLawFrom` at every time. This is a discrete-event state
process; it does not yet attach observed information-indexed strategies,
terminal payoffs, or continuous-time regularity.

`Simulation/Kernel/HistoryPath.lean` permits each action kernel to
depend measurably on the complete finite state prefix and event time. Its
stationary embedding preserves both the finite-history step kernels and the
entire path measure exactly. The strict boundary example exhibits two
reachable prefixes with the same latest state and different selected action
laws.

`Simulation/Kernel/EventPath.lean` uses the fixed coordinate
`State × (Unit ⊕ ActionBundle)`: the initial and terminal-absorption events
carry `Sum.inl ()`, while a nonterminal successor carries the sampled action
in `Sum.inr`. Its policy kernel can inspect the complete finite event prefix.
The recorded transition is Markov without assuming an `IsSFiniteKernel`
instance for a killed policy kernel, and forgetting actions from the embedded
state-history executor preserves every finite prefix marginal and the whole
infinite state-path measure exactly. The strict event regression has one
state and two looping actions, so equal state prefixes can still carry
distinct action occurrences. A fixed analytic information partition and its
consistency law are supplied by the next module; player-indexed observed-game
integration remains separate.

`Simulation/Kernel/ObservedEvent.lean` supplies that first analytic
information layer without changing the raw executor. An `EventInformation`
is a fixed time-indexed measurable statistic of complete finite event
prefixes. Its `ActionPolicy` is indexed only by information values, so equal
information forces exactly equal action measures. `EventInformation.Hom`
forgets finer information to coarser information; pulling a coarse policy
back along such a map preserves the compiled raw event policy, every stopped
step, and the complete event-path law exactly. Full event, complete
state-prefix, and latest-state information recover the preceding three policy
interfaces exactly. The strict blind-information regression separates full
event dependence from policies that merge all same-time histories.
`latestEventState_eq_of_informationAt_eq` now makes an important boundary
formal: a concrete `ActionBundle`-valued information policy can identify two
nonterminal prefixes only if their latest concrete states agree.

`Simulation/Kernel/RealizedInformation.lean` removes that codomain
obstruction by separating the information-indexed abstract action law from a
fixed history-dependent realization kernel. The abstract kernel, not its
concrete realization, is equal at equal information. Composition-product and
projection compile it to the raw event executor, with explicit s-finiteness,
normalization, and almost-sure concrete legality assumptions. Concrete laws
are equal only when the two realization sections agree almost everywhere
under the shared abstract law. Pullback along an information factor preserves
the compiled raw policy, stopped steps, and whole event-path law. The
terminal-tagged absent-minded regression proves strict expressiveness over the
direct concrete-bundle policy while exhibiting unequal legal concrete laws at
two histories with one common abstract law.

`Simulation/Presentation/Chance/KernelBridge.lean` performs the part of the
player/mover-aware bridge that this codomain supports truthfully. Complete
histories become states of a deterministic `KernelArena`, so the existing
behavioral/chance history policy becomes stationary. Player nodes use
`BehavioralProfile.actionLawAt`, chance nodes use the declared chance kernel,
and every finite analytic endpoint measure is exactly `PMF.toMeasure` of the
old stopped-history PMF. It does not force a player's `InfoState` partition
into concrete action bundles: distinct complete histories have disjoint
bundle fibers even when one abstract information action law is realized at
both. The generic realization layer now supports that semantics, but a general
observed-chance instantiation still needs an explicit analytic presentation
certifying measurable tagged histories, information, abstract actions, and
dependent realization. No such certificate follows from the current
unmeasured `ObservedGame` carriers alone.

`Simulation/Presentation/Chance/Realized.lean` packages exactly that
missing model-specific evidence. An `AnalyticPresentation` fixes measurable
event information and action realization, compiles every behavioral profile
to a realized abstract policy, factors player histories through the original
`InfoState`, and certifies equality with the established raw observed-chance
executor. Generic theorems then give equal abstract laws at equal player
information, exact concrete player/chance branches, exact complete joint
event and state paths, and exact finite stopped-history measures. The
absent-minded regression constructs the certificate extensionally for all
profiles and prefixes. No theorem says every observed chance game has such a
certificate without assumptions.

`Simulation/Presentation/Chance/Countable.lean` now separates executable
selectors from supplied analytic certificates. The reachable player subtype
and tagged action carrier remain occurrence-sensitive. `informationAtHistory`
requires an executable terminal decision; `informationOfPlayerInformation`
requires an explicit reachability decision and returns `Option`.
`realizedAction` takes a concrete complete history and executable tag equality,
uses `actionEquiv` for matching player tags, preserves matching chance actions,
and returns `none` on mismatch. No arbitrary off-tag fallback remains.
Countable models provide actual encoders and partial decoders instead of
extracting them from `Countable` or `Nonempty`. The absent-minded and
sparse-player regressions construct these data and execute them with
`native_decide`; unused real-valued player and information/action fibers are
not enumerated. Analytic measures and kernels are supplied through the
existing `AnalyticPresentation`/`MeasurableKernelPresentation` owners. Their
generic represented-information, compilation, and finite-marginal theorems
remain the comparison boundary; no second countable analytic facade is kept.

`Simulation/Presentation/Chance/MeasurableHistory.lean` separates the measurable
history-unfolding obligation from countability. A `MeasurableHistoryModel`
chooses measurable spaces on complete histories and the dependent
history/action bundle, proves projection and deterministic append measurable,
records measurable terminality and state singletons, and supplies a Markov
kernel pointwise equal to `PMF.toMeasure (PMF.pure append)`.

`Simulation/Presentation/Chance/Measurable.lean` adds the corresponding
local realized-information certificate. Its fixed information and realization
objects are shared by all profiles. Exact player and chance equations are
stated directly for the compiled concrete bundle kernel, while terminal zero,
normalization, legality, abstract information consistency, and complete path
construction are reused from `Simulation.Kernel.RealizedInformation`.
`AnalyticPresentation.toMeasurablePresentation` proves exact specialization
of the established supplied top-space presentation. The former
`CountablePresentation.measurablePresentation` constructor has been removed.

The uncountable regression uses a root `ℝ` action and one terminal history per
real. It proves both complete histories and legal history/action bundles
non-countable, transports measurable structures along explicit measurable
equivalences to `Unit ⊕ ℝ` and `ℝ`, constructs the full presentation for every
behavioral PMF, and proves the concrete player kernel exactly.

`Simulation/Presentation/Kernel/Core.lean` removes that
action-law restriction without changing the executable PMF layer. The
measurable history model is now structural data over `ObservedGame`.
`MeasurableKernelPresentation` fixes measurable information, action
realization, and a concrete s-finite chance-action kernel;
`KernelBehavioralProfile` supplies the normalized information-indexed
abstract kernel and exact realized chance consistency. Generic theorems give
abstract information consistency, fixed chance-law equality across profiles,
abstract-kernel unilateral deviations, and complete joint/state path laws.

The PMF presentation adapter selects a reference realized kernel only to name
the fixed chance kernel; exact local chance theorems prove that choice
irrelevant for every admitted profile. Countability is no longer an alternate
constructor for this analytic adapter. `ObservedNonAtomicKernelBoundary` pushes
unit-interval volume into the legal real-action bundle at both a player root
and a separate chance root, proves every singleton has zero mass, and proves
neither compiled law is `PMF.toMeasure` of any PMF. On the actual generated
state-path law it also defines the first-action lower-half cylinder, proves
the event measurable, nonempty, and proper, and computes its probability as
exactly one half.

The representations coexist while the remaining preservation theorems described in
[`../research/extensive_game_architecture.md`](../research/extensive_game_architecture.md)
are tested.
