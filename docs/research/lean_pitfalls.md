# Lean Implementation Notes

Reusable Lean and Mathlib details encountered in EconCSLib development.

## Ordered Fields

Use:

```lean
[Field U] [LinearOrder U] [IsStrictOrderedRing U]
```

instead of deprecated semibundled ordered-field classes.

## Function Types And Propositions

`∀ i, S i → Prop` parses as `∀ i, (S i → Prop)`, not
`(∀ i, S i) → Prop`. Use explicit parentheses:

```lean
((i : N) → S i) → Prop
```

## Targeted Imports

- `Function.update` comes from `Mathlib.Logic.Function.Basic`.
- `Finset` sum notation requires a suitable BigOperators import.
- Rational literals require an import that provides the relevant `ℚ`
  instances.

Use the narrowest import that is clear from neighboring modules.

## Scoped Options

`set_option ... in` applies to the next command only, not to an entire section.
Place a persistent option inside the section:

```lean
section Foo
set_option linter.unusedSectionVars false
...
end Foo
```

## Concrete Games And `native_decide`

Typeclass inference may need to unfold a concrete game definition to find
instances such as `Fintype (G.strategy i)`. Mark executable examples
`@[reducible]` when appropriate:

```lean
@[reducible] def RPS : StrategicGame (Fin 2) ℚ where
  ...
```

For finite `ℚ`-valued computations over custom finite types, `native_decide`
is often more robust than manually unfolding the internal `Finset`
representation.

## Build Cache Version Skew

After switching Lean or Mathlib versions, remove stale local build output and
rebuild:

```bash
rm -rf .lake/build
lake exe cache get
lake build
```
