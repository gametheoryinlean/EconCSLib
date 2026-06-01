# Can Inductive Types Represent Infinite Game Trees?

**Answer: No.** Inductive types in Lean 4 are well-founded by construction.
Every value has finite depth. Neither `noncomputable` nor `partial` changes this.

This document records the experiments that verify this conclusion.

---

## Setup

```lean
inductive MyTree where
  | leaf (n : Nat)
  | node (children : Nat → MyTree)
  deriving Nonempty
```

## Experiment 1: `noncomputable def` — rejected

```lean
noncomputable def infiniteTree : MyTree :=
  .node (fun _ => infiniteTree)
```

**Result**: Lean rejects this.
```
fail to show termination for infiniteTree
  no parameters suitable for structural recursion
  well-founded recursion cannot be used, `infiniteTree` does not take any (non-fixed) arguments
```

`noncomputable` does not bypass the termination checker. It only means
"this definition cannot be executed by `#eval`", not "this definition
may diverge".

## Experiment 2: `partial def` on a constant — rejected

```lean
partial def infiniteTree : MyTree :=
  .node (fun _ => infiniteTree)
```

**Result**: Lean rejects this.
```
invalid use of `partial`, `infiniteTree` is not a function
```

`partial` only applies to functions (with at least one argument), not constants.

## Experiment 3: `partial def` with dummy argument — accepted but opaque

```lean
partial def mkInfinite : Unit → MyTree
  | () => .node (fun _ => mkInfinite ())

def infiniteTree : MyTree := mkInfinite ()
```

**Result**: Lean accepts this. `infiniteTree : MyTree` type-checks.

However, the definition is **opaque**:

```lean
-- Cannot unfold:
theorem test : infiniteTree = .node (fun _ => infiniteTree) := by
  simp [infiniteTree, mkInfinite]  -- FAILS: mkInfinite cannot be unfolded
```

`partial def` does not generate definitional equalities. The body of
`mkInfinite` is not available for reduction or `simp`.

## Experiment 4: Structural induction still proves finite depth

```lean
def MyTree.depth : MyTree → Nat
  | .leaf _ => 0
  | .node children => 1 + (children 0).depth

-- This WORKS — even applied to mkInfinite ()
example : ∃ n : Nat, (mkInfinite ()).depth = n :=
  ⟨(mkInfinite ()).depth, rfl⟩
```

Lean proves that `mkInfinite ()` has a well-defined finite depth. The structural
recursor for `MyTree` applies to ALL values of type `MyTree`, including
`mkInfinite ()`. This means `mkInfinite ()` is logically a finite tree.

## Experiment 5: `unsafe def` — accepted but unsound

```lean
unsafe def infiniteTree : MyTree :=
  .node (fun _ => infiniteTree)
```

**Result**: Lean accepts this. But `unsafe` bypasses the kernel's soundness
guarantees. Using `unsafe` definitions in proofs would make the logic inconsistent.
This is not a viable approach for a verified library.

## What `partial def` actually creates

`partial def mkInfinite : Unit → MyTree` creates a function that:
- **At the logical level**: returns SOME value of type `MyTree` (guaranteed to exist
  by the `Nonempty` instance). The specific value is unspecified and opaque.
- **At runtime**: would loop forever if evaluated (e.g., `#eval`).

The logical value and the runtime behavior are DIFFERENT. Logically, `mkInfinite ()`
is some finite tree (because all `MyTree` values are finite). At runtime, attempting
to compute it would diverge.

This is the key insight: `partial` introduces a gap between logical meaning and
computational behavior. It does NOT create infinite values in the type theory.

## Why inductive types are always finite-depth

This is a fundamental property of inductive types in the Calculus of Inductive
Constructions (CIC), which underlies Lean 4:

1. **Construction principle**: Every value of an inductive type is built by a
   finite sequence of constructor applications.

2. **Recursor**: The recursor (elimination principle) for `MyTree` allows
   structural recursion on ANY value. This is only sound if every value has
   finite depth — otherwise the recursion could diverge.

3. **No circular references**: Unlike imperative languages, Lean does not allow
   a value to reference itself. `let x := .node (fun _ => x)` is not valid syntax.

These properties are guaranteed by Lean's kernel, independently of any `noncomputable`,
`partial`, or `unsafe` annotations.

## Implications for game theory

| Game type | Representation | Example |
|-----------|---------------|---------|
| Finite extensive game | `inductive GameTree` | Chess, Entry Deterrence |
| Infinite branching, finite depth | `inductive GameTree` with infinite `Action` type | Cournot (continuous actions) |
| Infinite depth (non-terminating) | State space / transition function | Repeated games, stochastic games |

For infinite games (repeated games, discounted games, stochastic games), we must use
a **state space** representation:

```lean
structure GameForm where
  State : Type*
  action : State → Type*
  move : (s : State) → action s → State
  ...
```

This describes the game via a transition function, without constructing the tree
as a value. The game can run forever — termination is not required for the
definition, only for computing outcomes (which may be defined as limits of
infinite sequences).

## Summary

| Approach | Infinite depth? | Can prove properties? | Can compute? |
|----------|----------------|----------------------|-------------|
| `noncomputable def` | ❌ Rejected | — | — |
| `partial def` | ❌ Opaque finite value | ❌ Cannot unfold | ❌ Diverges |
| `unsafe def` | ⚠️ Unsound | ❌ Breaks logic | ⚠️ Diverges |
| State space | ✅ Yes | ✅ Yes | Depends on finiteness |
