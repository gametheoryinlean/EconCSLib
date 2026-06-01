# Solution Concept: Analysis and Decision

## Finding: SolutionConcept = Set

Our definition:
```lean
abbrev SolutionConcept (ι : Type*) (S : ι → Type*) := (∀ i : ι, S i) → Prop
```

This is literally `Set (∀ i, S i)`. And:
- `IsRefinement C₁ C₂` = `C₁ ⊆ C₂` (subset)
- `IsEquivalent C₁ C₂` = `C₁ = C₂` (equality as sets)
- `IsRefinement.refl` = `Set.Subset.refl`
- `IsRefinement.trans` = `Set.Subset.trans`

We were reinventing Mathlib's `Set`. No need for a custom type.

## MSZ: Two Different Meanings of "Solution Concept"

### Meaning 1: Predicate on profiles (non-cooperative games)

In strategic/extensive-form games, a "solution concept" is a property of
profiles: Nash equilibrium, SPE, etc. Given a game G, it's a set of profiles.

```
IsNashEquilibrium G : G.Profile → Prop
```

This is just `Set G.Profile`. No separate abstraction needed.

### Meaning 2: Function from games to solutions (cooperative games)

In bargaining and coalitional games, a "solution concept" is a **function**
that maps each game to a recommended solution. [MSZ Definition 15.4]:

> "A solution concept is a function φ associating every bargaining game
> (S,d) with an alternative φ(S,d) ∈ S."

Examples:
- Nash bargaining solution: `φ : BargainingGame → ℝ²` (single-valued)
- Core: `φ : CoalitionalGame N → Set (PayoffVector N)` (set-valued)
- Shapley value: `φ : CoalitionalGame N → PayoffVector N` (single-valued)

The axiomatic characterization is about THIS function:
- Efficiency: `∀ G, ∑ φ(G) = v(N)`
- Symmetry: `i ≈ j in G → φ(G)(i) = φ(G)(j)`
- Additivity: `φ(G + H) = φ(G) + φ(H)`

This is NOT a `Set` — it's a function on the space of games.

## Decision

1. **Delete `Core/SolutionConcept.lean`** — the abbrev adds no value over `Set`.
2. **Delete `Core/` directory entirely** — no files remain.
3. For non-cooperative games: use `G.Profile → Prop` (or `Set G.Profile`) directly.
4. For cooperative games: define solution concepts as functions in
   `CoalitionalGame/` and `Bargaining/` where they naturally belong.
   These are domain-specific and don't need a shared abstraction.
5. `IsRefinement` between Nash and SPE is just `⊆` on sets — use Mathlib's `Set.Subset`.
