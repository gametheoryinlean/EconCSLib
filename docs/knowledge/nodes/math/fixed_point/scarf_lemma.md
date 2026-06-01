---
id: math.fixed_point.scarf_lemma
title: Scarf Combinatorial Lemma (Colorful Room Existence)
kind: lemma
status: proved
primary_topic: math
topics:
  - math
  - math.fixed_point
lean:
  repository: econcslib
  modules:
    - EconCSLib.Math.FixedPoint.Scarf
  declarations:
    - IndexedLOrder.Scarf
    - IndexedLOrder.isColorful
    - IndexedLOrder.internal_door_two_rooms
    - IndexedLOrder.typed_colorful_room_odd
verification:
  statement: accepted
  proof: accepted
  alignment: aligned
tags:
  - fixed-point
  - combinatorics
  - scarf
---

# Scarf Combinatorial Lemma (Colorful Room Existence)

For any finite coloring $c : T \to I$ of the vertices of an indexed simplicial
triangulation (an `IndexedLOrder I T`), the set of **colorful rooms** is
nonempty: there is a cell whose vertex colors realize the full index set
$I$.

This is the combinatorial heart of the Brouwer fixed-point proof
([[math.fixed_point.brouwer_simplex]]). It plays the role classically filled by
Sperner's lemma, but is established here through a door-counting /
room-orientation parity argument rather than Sperner labeling.

## Proof

An orientation (door-counting) argument:

1. **Two rooms per internal door.** Each internal door is a face of exactly two
   rooms (`IndexedLOrder.internal_door_two_rooms`).
2. **Parity.** Fixing an index $i \in I$, the number of typed nearly-colorful
   rooms of type $i$ in the double-counting set is **odd**
   (`IndexedLOrder.typed_colorful_room_odd`), by counting outside doors,
   internal doors, and nearly-colorful rooms modulo two.
3. **Existence.** An odd count is positive, so a colorful room exists
   (`IndexedLOrder.Scarf`: `(IST.colorful c).Nonempty`).

The Lean development is axiom-clean:
`#print axioms IndexedLOrder.Scarf` = `propext, choice, Quot.sound`.

## Lean route note

The blueprint dependency `brouwer_simplex → scarf_lemma` reflects the **actual
Lean proof route**. MFoGT presents Brouwer for a simplex via Sperner's lemma;
the Lean port (adapted from `github.com/math-xmum/Brouwer`) instead uses
Scarf's room-based combinatorial lemma, which is equivalent for the
fixed-point conclusion.

## References

- [MFoGT, §4.11] Laraki, Renault, and Sorin, *Mathematical Foundations of Game
  Theory*. Combinatorial route to
  Brouwer's fixed-point theorem (presented in the Sperner formulation; the Lean
  port uses the equivalent Scarf room-counting formulation).
- Scarf, H. E. (1967). "The Core of an N-Person Game". *Econometrica* 35(1):
  50–69. Origin of the constructive primitive-set / room-orientation
  combinatorial argument.
