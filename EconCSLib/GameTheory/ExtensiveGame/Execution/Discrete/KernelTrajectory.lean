/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Execution.Discrete.KernelArena

/-!
# EconCSLib.GameTheory.ExtensiveGame.Execution.Discrete.KernelTrajectory

Finite-horizon stochastic execution and exact trajectory transfer for
`KernelArena`.

A randomized Markov policy chooses a normalized action distribution only when
the current action type is nonempty.  Execution stops at terminal states, so
the interface remains inhabited for arenas which genuinely have leaves.
`KernelArena.Simulation.PolicyMatch` strengthens a one-sided simulation with
terminal agreement and a coupling of the two policies' action laws.  Positive
mass may be paired only between actions whose successor kernels themselves
admit a state-relation coupling.

The resulting transfer theorem is stronger than support-level reachability:
it constructs a joint finite law of complete finite traces, has the two trace laws as
its exact marginals, and is supported on pointwise-related traces.

## Main definitions

* `KernelArena.Policy` — randomized Markov policies.
* `KernelArena.stepLaw` — the one-step successor-state distribution.
* `KernelArena.stateLawFrom` — the state distribution after a finite horizon.
* `KernelArena.traceLawFrom` — the distribution of complete finite traces.
* `KernelArena.Simulation.PolicyMatch` — coupling-compatible policies.

## Main results

* `KernelArena.Simulation.PolicyMatch.stepCoupling` — exact one-step transfer.
* `KernelArena.Simulation.PolicyMatch.stateLawCoupling` — exact
  finite-horizon endpoint transfer.
* `KernelArena.Simulation.PolicyMatch.traceLawCoupling` — exact
  finite-horizon trajectory transfer.
* `KernelArena.Simulation.PolicyMatch.traceObservableLaw_equivalent` — exact
  semantic equivalence of any related trace-observable laws.
-/

namespace KernelArena

/-- A terminal-aware randomized Markov policy for a stochastic arena.

The nonterminal certificate prevents a policy from being required to produce
a `FiniteLaw` on an empty action type at a terminal state. -/
abbrev Policy (A : KernelArena) :=
  (s : A.State) → ¬ IsEmpty (A.Action s) → FiniteLaw (A.Action s)

/-- The successor-state law produced by one policy-controlled step. -/
def stepLaw (A : KernelArena) (policy : A.Policy)
    (s : A.State) (hnonterminal : ¬ IsEmpty (A.Action s)) :
    FiniteLaw A.State :=
  (policy s hnonterminal).bind (A.next s)

/-- The stopped state law after at most `horizon` policy-controlled steps. -/
def stateLawFrom (A : KernelArena)
    [(s : A.State) → Decidable (IsEmpty (A.Action s))]
    (policy : A.Policy) :
    Nat → A.State → FiniteLaw A.State
  | 0, s => FiniteLaw.pure s
  | horizon + 1, s =>
      if hterminal : IsEmpty (A.Action s) then
        FiniteLaw.pure s
      else
        (A.stepLaw policy s hterminal).bind
          (A.stateLawFrom policy horizon)

/-- The law of the stopped state trace over at most `horizon` transitions.

The initial state is included.  A trace has `horizon + 1` entries unless it
reaches a terminal state first. -/
def traceLawFrom (A : KernelArena)
    [(s : A.State) → Decidable (IsEmpty (A.Action s))]
    (policy : A.Policy) :
    Nat → A.State → FiniteLaw (List A.State)
  | 0, s => FiniteLaw.pure [s]
  | horizon + 1, s =>
      if hterminal : IsEmpty (A.Action s) then
        FiniteLaw.pure [s]
      else
        (A.stepLaw policy s hterminal).bind fun nextState =>
          (A.traceLawFrom policy horizon nextState).map fun tail =>
            s :: tail

namespace Simulation

variable {A B : KernelArena}

/-- Two randomized policies match along a stochastic simulation.

Related states are terminal simultaneously.  At related nonterminal states,
their action laws admit an exact coupling.  Every positive-mass action pair in
that coupling must in turn have successor laws coupled along the simulation's
state relation. -/
structure PolicyMatch (simulation : A.Simulation B)
    (sourcePolicy : A.Policy) (targetPolicy : B.Policy) where
  /-- Matched execution stops on both sides at the same macro boundary. -/
  terminal_iff :
    ∀ {source target},
      simulation.Rel source target →
        (IsEmpty (A.Action source) ↔ IsEmpty (B.Action target))
  /-- Relation describing which action pairs carry matched transition
  kernels. -/
  actionRel :
    ∀ {source target},
      simulation.Rel source target →
        A.Action source → B.Action target → Prop
  /-- Coupling of action laws, carrying a successor-kernel coupling at every
  supported action pair. -/
  actionCoupling :
    ∀ {source target}
      (_hrelated : simulation.Rel source target)
      (hsource : ¬ IsEmpty (A.Action source))
      (htarget : ¬ IsEmpty (B.Action target)),
      FiniteLaw.RelCoupling
        (actionRel _hrelated)
        (sourcePolicy source hsource)
        (targetPolicy target htarget)
  /-- Every related action pair has an explicit coupling of its successor
  laws. -/
  kernelCoupling :
    ∀ {source target}
      (hrelated : simulation.Rel source target)
      (sourceAction : A.Action source)
      (targetAction : B.Action target),
      actionRel hrelated sourceAction targetAction →
        FiniteLaw.RelCoupling simulation.Rel
          (A.next source sourceAction)
          (B.next target targetAction)

namespace PolicyMatch

variable
  [(source : A.State) → Decidable (IsEmpty (A.Action source))]
  [(target : B.State) → Decidable (IsEmpty (B.Action target))]
  {simulation : A.Simulation B}
variable {sourcePolicy : A.Policy} {targetPolicy : B.Policy}

/-- Matched policies produce exactly coupled one-step state laws. -/
def stepCoupling
    (matchPolicy : simulation.PolicyMatch sourcePolicy targetPolicy)
    {source : A.State} {target : B.State}
    (hrelated : simulation.Rel source target)
    (hsource : ¬ IsEmpty (A.Action source))
    (htarget : ¬ IsEmpty (B.Action target)) :
    FiniteLaw.RelCoupling simulation.Rel
      (A.stepLaw sourcePolicy source hsource)
      (B.stepLaw targetPolicy target htarget) := by
  exact
    (matchPolicy.actionCoupling hrelated hsource htarget).bind
      (fun sourceAction targetAction haction =>
        matchPolicy.kernelCoupling hrelated sourceAction targetAction haction)

/-- Matched policies produce exactly coupled finite-horizon state laws. -/
def stateLawCoupling
    (matchPolicy : simulation.PolicyMatch sourcePolicy targetPolicy)
    {source : A.State} {target : B.State}
    (hrelated : simulation.Rel source target) (horizon : Nat) :
    FiniteLaw.RelCoupling simulation.Rel
      (A.stateLawFrom sourcePolicy horizon source)
      (B.stateLawFrom targetPolicy horizon target) := by
  induction horizon generalizing source target with
  | zero =>
      simpa only [stateLawFrom] using FiniteLaw.relCoupling_pure hrelated
  | succ horizon ih =>
      by_cases hsource : IsEmpty (A.Action source)
      · have htarget :
            IsEmpty (B.Action target) :=
          (matchPolicy.terminal_iff hrelated).mp hsource
        simp only [stateLawFrom]
        simp [hsource, htarget]
        exact FiniteLaw.relCoupling_pure hrelated
      · have htarget :
            ¬ IsEmpty (B.Action target) :=
          (not_congr (matchPolicy.terminal_iff hrelated)).mp hsource
        simp only [stateLawFrom]
        simp [hsource, htarget]
        exact
          (matchPolicy.stepCoupling hrelated hsource htarget).bind
            (fun _ _ hnext => ih hnext)

/-- Matched policies produce exactly coupled complete finite traces.

The support relation is `List.Forall₂ simulation.Rel`: corresponding trace
positions are related, not merely their terminal states. -/
def traceLawCoupling
    (matchPolicy : simulation.PolicyMatch sourcePolicy targetPolicy)
    {source : A.State} {target : B.State}
    (hrelated : simulation.Rel source target) (horizon : Nat) :
    FiniteLaw.RelCoupling (List.Forall₂ simulation.Rel)
      (A.traceLawFrom sourcePolicy horizon source)
      (B.traceLawFrom targetPolicy horizon target) := by
  induction horizon generalizing source target with
  | zero =>
      apply FiniteLaw.relCoupling_pure
      exact List.Forall₂.cons hrelated List.Forall₂.nil
  | succ horizon ih =>
      by_cases hsource : IsEmpty (A.Action source)
      · have htarget :
            IsEmpty (B.Action target) :=
          (matchPolicy.terminal_iff hrelated).mp hsource
        simp only [traceLawFrom]
        simp [hsource, htarget]
        apply FiniteLaw.relCoupling_pure
        exact List.Forall₂.cons hrelated List.Forall₂.nil
      · have htarget :
            ¬ IsEmpty (B.Action target) :=
          (not_congr (matchPolicy.terminal_iff hrelated)).mp hsource
        simp only [traceLawFrom]
        simp [hsource, htarget]
        exact
          (matchPolicy.stepCoupling hrelated hsource htarget).bind
            (fun _ _ hnext =>
              (ih hnext).map
                (f := fun sourceTail => source :: sourceTail)
                (g := fun targetTail => target :: targetTail)
                (fun _ _ htail => List.Forall₂.cons hrelated htail))

/-- Any observables agreeing on related traces have exactly equal laws.

Terminal outcomes and utilities are important instances: once their readings
agree on `List.Forall₂ simulation.Rel`, the two pushforward laws are
semantically equivalent. -/
theorem traceObservableLaw_equivalent
    (matchPolicy : simulation.PolicyMatch sourcePolicy targetPolicy)
    {source : A.State} {target : B.State}
    (hrelated : simulation.Rel source target) (horizon : Nat)
    {Outcome : Type*}
    (sourceOutcome : List A.State → Outcome)
    (targetOutcome : List B.State → Outcome)
    (houtcome :
      ∀ sourceTrace targetTrace,
        List.Forall₂ simulation.Rel sourceTrace targetTrace →
          sourceOutcome sourceTrace = targetOutcome targetTrace) :
    ((A.traceLawFrom sourcePolicy horizon source).map sourceOutcome).Equivalent
      ((B.traceLawFrom targetPolicy horizon target).map targetOutcome) :=
  (matchPolicy.traceLawCoupling hrelated horizon).map_eq houtcome

end PolicyMatch

end Simulation

end KernelArena
