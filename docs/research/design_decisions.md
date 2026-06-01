# Architecture Rationale

This note records durable decisions that shape the current EconCSLib API.

## Profiles Are Game-Bound

Use `G.Profile` for strategic-game profiles. It makes the owning game explicit
and avoids a standalone wrapper around a dependent function type. Reusable
profile operations such as unilateral deviation remain available through the
foundation compatibility helpers where appropriate.

## Arenas Are The General Extensive-Game Model

Use a state-space `Arena` as the general extensive-game representation.

- It supports finite and infinite state spaces.
- Terminal states can be modeled through the action type.
- A subgame is the same arena with a different initial state.
- Finite inductive game trees remain useful for backward induction and
  executable developments.

## Mixed Strategies Use `stdSimplex`

Use Mathlib's `stdSimplex` rather than a custom probability structure. The
shared interface supports reusable convexity and compactness results. Keep
numeric assumptions local: finite executable developments can instantiate to
`ℚ`, while analytic existence results may use `ℝ`.

## Keep Numeric Assumptions Decomposed

When ordered-field arithmetic is needed, use the Mathlib decomposition:

```lean
[Field U] [LinearOrder U] [IsStrictOrderedRing U]
```

Many definitions need less: often a preorder, additive structure, or no
numeric assumptions at all.

## Keep Structures Lean

Do not store avoidable typeclass assumptions in domain structures. Add
finiteness, decidable equality, topology, and algebra only at the declarations
that need them.

## Prefer Predicates Over Wrapper Abstractions

When a solution concept is literally a property of profiles or a set of
profiles, expose it as a predicate or `Set`. Introduce a wrapper only when it
provides meaningful structure or behavior.

## Use Reducible Concrete Examples When Computation Needs It

Concrete finite examples intended for `native_decide` may need
`@[reducible]` so typeclass inference can see strategy carriers through the
game definition. Keep this local to executable examples.
