/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.StrategicGame.Checker
import EconCSLib.GameTheory.StrategicGame.NashEquilibrium
import Mathlib.Data.Fintype.Pi

/-!
# EconCSLib.Examples.PrisonersDilemma

The classic Prisoner's Dilemma: two players simultaneously choose to Cooperate or Defect.

Payoff matrix (row = player 0, column = player 1):
```
             Cooperate   Defect
Cooperate      3, 3       0, 5
Defect         5, 0       1, 1
```

Key results:
- T4a: Defect is weakly dominant for both players.
- T4b: (Defect, Defect) is a Nash equilibrium (follows from T3).
- T4c: (Defect, Defect) is the unique pure Nash equilibrium.

Note: Defect is actually *strictly* dominant. We use `IsWeaklyDominant` here because
`IsStrictlyDominant` requires an explicit `s ≠ s'` guard (see `Dominance.lean`), making
`IsWeaklyDominant` the simpler interface for this proof.

Payoffs are `ℕ`-valued (all entries are non-negative integers: 0, 1, 3, 5); `ℕ` has
decidable `≤` as a core Lean 4 instance, enabling `native_decide` and `decide` throughout.

**Proof technique**: `native_decide` is used after `show` to expose concrete types.
The `show` tactic rewrites `PD.strategy i` → `PDMove` and
`PD.Profile` → `Fin 2 → PDMove` via definitional equality,
making all types explicit so that `native_decide` can synthesize `Decidable` instances.

**`Fintype PDMove`**: `deriving Fintype` is not available without
`Mathlib.Tactic.DeriveFintype`; the instance is provided explicitly instead.

**`Mathlib.Data.Fintype.Pi`**: imported explicitly to provide `Pi.instFintype`
(`Fintype (Fin 2 → PDMove)`) and `Pi.instDecidableEq`, both required for
`native_decide` to synthesize `Decidable` over profiles.
-/

/-- The two moves in the Prisoner's Dilemma. -/
inductive PDMove | Cooperate | Defect
  deriving DecidableEq, Repr

instance : Fintype PDMove :=
  ⟨⟨[PDMove.Cooperate, PDMove.Defect], by decide⟩, fun x => by cases x <;> decide⟩

namespace PrisonersDilemma

open PDMove
open StrategicGame

/-- The Prisoner's Dilemma as a strategic game with natural number payoffs. -/
def PD : StrategicGame (Fin 2) ℕ where
  strategy := fun _ => PDMove
  payoff σ i :=
    match σ 0, σ 1 with
    | Cooperate, Cooperate => 3
    | Cooperate, Defect    => if i = 0 then 0 else 5
    | Defect,    Cooperate => if i = 0 then 5 else 0
    | Defect,    Defect    => 1

/-- T4a: Defect is weakly dominant for both players.
    Proof: expose concrete types via `show`, then decide by exhaustive computation. -/
theorem pd_defect_weakly_dominant : ∀ i : Fin 2, IsWeaklyDominant PD i Defect := by
  show ∀ (i : Fin 2) (s' : PDMove) (σ : Fin 2 → PDMove),
    PD.payoff (deviate σ i s') i ≤ PD.payoff (deviate σ i PDMove.Defect) i
  native_decide

/-- T4b: (Defect, Defect) is a Nash equilibrium, by T3 (dominant profile → Nash). -/
theorem pd_defect_nash : IsNashEquilibrium PD (fun _ => Defect) :=
  IsNashEquilibrium.of_dominant (fun i => pd_defect_weakly_dominant i)

/-- T4c: (Defect, Defect) is the *unique* pure Nash equilibrium. -/
theorem pd_nash_unique : ∀ σ : PD.Profile,
    IsNashEquilibrium PD σ → σ = fun _ => Defect := by
  show ∀ (σ : Fin 2 → PDMove),
    (∀ (i : Fin 2) (s' : PDMove), PD.payoff (deviate σ i s') i ≤ PD.payoff σ i) →
    σ = fun _ => PDMove.Defect
  native_decide

/-- The social optimum (Cooperate, Cooperate) is Pareto-superior to the Nash outcome. -/
theorem pd_pareto_suboptimal :
    PD.payoff (fun _ => Cooperate) 0 > PD.payoff (fun _ => Defect) 0 := by decide

end PrisonersDilemma
