/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.FOSG.Sequentialization.MacroLaw

/-!
# EconCSLib.GameTheory.ExtensiveGame.FOSG.Sequentialization.Trajectory

Policy compilation, finite-horizon coupling, and payoff-law equality.
-/

namespace ExtensiveGame.FOSG.Sequentialization

universe uU uSA uO uP

variable {n : ℕ} {U : Type uU}
  (G : FOSG.{0, uU, uSA, uSA, uO, uP} (Fin (n + 1)) U)

/-- The FOSG history kernel uses the model's executable world terminal test. -/
local instance historyKernelActionEmptinessDecidable
    [(world : G.WorldState) → Decidable (G.isTerminal world)] :
    (history : G.historyKernelArena.State) →
      Decidable (IsEmpty (G.historyKernelArena.Action history)) :=
  fun history =>
    decidable_of_iff
      (G.isTerminal history.1)
      (G.historyKernelArena_isTerminal_iff history).symm

/-- The concrete weak serializer is an exact kernel simulation when observed
at macro boundaries.

This repackaging is what permits generic finite-horizon coupling theorems to
iterate the compiler's one-step correctness proof. -/
def macroKernelSimulation
    [(world : G.WorldState) → Decidable (G.isTerminal world)]
    (D : G.DecisionModel)
    (rootPayoff : Fin (n + 1) → U)
    (sourceDeclaredRoot : G.HistoryState → Prop) :
    MacroPolicyData G D rootPayoff sourceDeclaredRoot →
    G.historyKernelArena.Simulation
      (macroExecutionKernelArena G D rootPayoff sourceDeclaredRoot)
  | data =>
  (probabilisticWeakSimulation G D rootPayoff data.micro
    sourceDeclaredRoot).toKernelSimulation

/-- The concrete policy compiler supplies the `PolicyMatch` required by the
generic finite-horizon trajectory theorems. -/
def serializedMacroPolicy_match
    [(world : G.WorldState) → Decidable (G.isTerminal world)]
    (D : G.DecisionModel)
    (rootPayoff : Fin (n + 1) → U)
    (sourceDeclaredRoot : G.HistoryState → Prop)
    (data : MacroPolicyData G D rootPayoff sourceDeclaredRoot)
    (sourcePolicy : G.historyKernelArena.Policy) :
    (macroKernelSimulation G D rootPayoff sourceDeclaredRoot data).PolicyMatch
      sourcePolicy
      (serializedMacroPolicy G D rootPayoff sourceDeclaredRoot data
        sourcePolicy) where
  terminal_iff := by
    intro source target hrelated
    exact
      (probabilisticWeakSimulation G D rootPayoff data.micro
        sourceDeclaredRoot).toKernelSimulation_terminal_iff hrelated
  actionRel := by
    intro source target hrelated sourceAction targetAction
    have hsource :
        ¬ IsEmpty (G.historyKernelArena.Action source) := by
      intro hempty
      exact hempty.false sourceAction
    have htarget :
        ¬ (game G rootPayoff).isTerminal target.1 := by
      intro hterminal
      exact hsource
        (((probabilisticWeakSimulation G D rootPayoff data.micro
          sourceDeclaredRoot).terminal_iff hrelated).mpr hterminal)
    exact targetAction =
      macroExecutionAction G D rootPayoff data.micro sourceDeclaredRoot
        source sourceAction target htarget
  actionCoupling := by
    intro source target hrelated hsource htarget
    classical
    rw [serializedMacroPolicy_eq_map G D rootPayoff
      sourceDeclaredRoot data sourcePolicy hrelated hsource htarget]
    let actionMap :
        G.historyKernelArena.Action source →
          (macroExecutionKernelArena G D rootPayoff
            sourceDeclaredRoot).Action target :=
      fun sourceAction =>
        macroExecutionAction G D rootPayoff data.micro sourceDeclaredRoot
          source sourceAction target
            (macroTargetNonterminal G D rootPayoff
              sourceDeclaredRoot target htarget)
    change
      FiniteLaw.RelCoupling
        (fun sourceAction targetAction => targetAction = actionMap sourceAction)
        (sourcePolicy source hsource)
        ((sourcePolicy source hsource).map fun jointAction =>
          macroExecutionAction G D rootPayoff data.micro sourceDeclaredRoot
            source jointAction target
              (macroTargetNonterminal G D rootPayoff
                sourceDeclaredRoot target htarget))
    have hmap :
        (fun jointAction =>
          macroExecutionAction G D rootPayoff data.micro sourceDeclaredRoot
            source jointAction target
              (macroTargetNonterminal G D rootPayoff
                sourceDeclaredRoot target htarget)) = actionMap := by
      funext sourceAction
      rfl
    rw [hmap]
    let base :=
      (FiniteLaw.relCoupling_refl
        (sourcePolicy source hsource)).map
          (S := fun sourceAction targetAction =>
            targetAction = actionMap sourceAction)
          (f := id) (g := actionMap)
          (by
            intro left right hsame
            subst right
            rfl)
    have hid := FiniteLaw.map_id (sourcePolicy source hsource)
    exact
      { joint := base.joint
        leftEquivalent :=
          base.leftEquivalent.trans (FiniteLaw.Equivalent.of_eq hid)
        rightEquivalent := base.rightEquivalent
        leftPositive := fun outcome => by
          calc
            (base.joint.map fun pair => pair.1.1).HasPositiveAtom
                outcome ↔
                ((sourcePolicy source hsource).map id).HasPositiveAtom
                  outcome := base.leftPositive outcome
            _ ↔ (sourcePolicy source hsource).HasPositiveAtom outcome := by
              rw [hid]
        rightPositive := base.rightPositive }
  kernelCoupling := by
    intro source target hrelated sourceAction targetAction haction
    subst targetAction
    simpa only [macroKernelSimulation] using
      ((macroKernelSimulation G D rootPayoff
        sourceDeclaredRoot data).match_action hrelated sourceAction).2

/-- Compile an information-indexed behavioral profile all the way to the
serialized EFG's terminal-aware macro policy. -/
def serializedBehavioralMacroPolicy
    [(world : G.WorldState) → Decidable (G.isTerminal world)]
    (D : G.DecisionModel)
    (rootPayoff : Fin (n + 1) → U)
    (sourceDeclaredRoot : G.HistoryState → Prop)
    (data : MacroPolicyData G D rootPayoff sourceDeclaredRoot)
    (profile : D.BehavioralProfile) :
    (macroExecutionKernelArena G D rootPayoff
      sourceDeclaredRoot).Policy :=
  serializedMacroPolicy G D rootPayoff sourceDeclaredRoot data
    (D.behavioralHistoryPolicy profile)

/-- The genuine target observed-EFG behavioral policy realizes exactly one
step of the compiled macro policy at every related nonterminal boundary. -/
theorem serializedBehavioralExecution_eq_macroStepLaw
    [(world : G.WorldState) → Decidable (G.isTerminal world)]
    (D : G.DecisionModel)
    (rootPayoff : Fin (n + 1) → U)
    (sourceDeclaredRoot : G.HistoryState → Prop)
    (data : MacroPolicyData G D rootPayoff sourceDeclaredRoot)
    (profile : D.BehavioralProfile)
    (source : G.HistoryState)
    (hsource : ¬ G.isTerminal source.1)
    (target :
      (game G rootPayoff).toArena.HistoryFrom
        (game G rootPayoff).init)
    (hrelated : Rel G source target)
    (htarget :
      ¬ IsEmpty
        ((macroExecutionKernelArena G D rootPayoff
          sourceDeclaredRoot).Action target)) :
    ((game G rootPayoff).toArena.stochasticHistoryLawFrom
        (serializedBehavioralHistoryPolicy G D rootPayoff
          sourceDeclaredRoot profile)
        target (n + 2)).Equivalent
      ((macroExecutionKernelArena G D rootPayoff
        sourceDeclaredRoot).stepLaw
          (serializedBehavioralMacroPolicy G D rootPayoff
            sourceDeclaredRoot data profile)
          target htarget) := by
  refine
    (serializedBehavioralExecution_eq_jointActionLaw_bind_macro
      G D rootPayoff data.micro sourceDeclaredRoot profile source hsource target
      hrelated).trans (FiniteLaw.Equivalent.of_eq ?_)
  have hsourceActions :
      ¬ IsEmpty (G.historyKernelArena.Action source) := by
    rw [G.historyKernelArena_isTerminal_iff]
    exact hsource
  rw [KernelArena.stepLaw, serializedBehavioralMacroPolicy]
  rw [serializedMacroPolicy_eq_map G D rootPayoff sourceDeclaredRoot
    data (D.behavioralHistoryPolicy profile) hrelated hsourceActions
    htarget]
  rw [FiniteLaw.bind_map]
  change
    (D.jointActionLaw profile source hsource).bind _ =
      (D.jointActionLaw profile source hsource).bind _
  apply congrArg
    (FiniteLaw.bind (D.jointActionLaw profile source hsource))
  funext jointAction
  rfl

/-- Continuous execution of the genuine serialized observed-EFG behavioral
policy for `horizon * (n + 2)` micro steps is exactly the stopped
`horizon`-step law of its compiled macro policy.

The induction uses the one-block realization theorem at every related
boundary. Coupling support supplies the related source witness needed for the
next block, so the result includes early terminal stopping. -/
theorem serializedBehavioralMicroStateLaw_eq_macro
    [(world : G.WorldState) → Decidable (G.isTerminal world)]
    (D : G.DecisionModel)
    (rootPayoff : Fin (n + 1) → U)
    (sourceDeclaredRoot : G.HistoryState → Prop)
    (data : MacroPolicyData G D rootPayoff sourceDeclaredRoot)
    [(target :
        (macroExecutionKernelArena G D rootPayoff
          sourceDeclaredRoot).State) →
      Decidable
        (IsEmpty
          ((macroExecutionKernelArena G D rootPayoff
            sourceDeclaredRoot).Action target))]
    (profile : D.BehavioralProfile)
    {source : G.HistoryState}
    {target :
      (game G rootPayoff).toArena.HistoryFrom
        (game G rootPayoff).init}
    (hrelated : Rel G source target) :
    ∀ horizon : ℕ,
      ((game G rootPayoff).toArena.stochasticHistoryLawFrom
          (serializedBehavioralHistoryPolicy G D rootPayoff
            sourceDeclaredRoot profile)
          target (horizon * (n + 2))).Equivalent
        ((macroExecutionKernelArena G D rootPayoff
          sourceDeclaredRoot).stateLawFrom
            (serializedBehavioralMacroPolicy G D rootPayoff
              sourceDeclaredRoot data profile)
            horizon target) := by
  intro horizon
  induction horizon generalizing source target with
  | zero =>
      apply FiniteLaw.Equivalent.of_eq
      simp [KernelArena.stateLawFrom]
      rfl
  | succ horizon ih =>
      by_cases hsourceTerminal : G.isTerminal source.1
      · have hsourceActions :
            IsEmpty (G.historyKernelArena.Action source) :=
          (G.historyKernelArena_isTerminal_iff source).mpr
            hsourceTerminal
        have htargetActions :
            IsEmpty
              ((macroExecutionKernelArena G D rootPayoff
                sourceDeclaredRoot).Action target) :=
          ((serializedMacroPolicy_match G D rootPayoff
              sourceDeclaredRoot data
              (D.behavioralHistoryPolicy profile)).terminal_iff hrelated).mp
              hsourceActions
        have htargetTerminal :
            (game G rootPayoff).isTerminal target.1 := by
          rw [hrelated]
          exact
            (boundary_isTerminal_iff G rootPayoff source).mpr
              hsourceTerminal
        apply FiniteLaw.Equivalent.of_eq
        rw [Arena.stochasticHistoryLawFrom_of_terminal
          (serializedBehavioralHistoryPolicy G D rootPayoff
            sourceDeclaredRoot profile)
          target htargetTerminal]
        simp [KernelArena.stateLawFrom, htargetActions]
        rfl
      · have hsourceActions :
            ¬ IsEmpty (G.historyKernelArena.Action source) := by
          rw [G.historyKernelArena_isTerminal_iff]
          exact hsourceTerminal
        have htargetActions :
            ¬ IsEmpty
              ((macroExecutionKernelArena G D rootPayoff
                sourceDeclaredRoot).Action target) :=
          (not_congr
            ((serializedMacroPolicy_match G D rootPayoff
              sourceDeclaredRoot data
              (D.behavioralHistoryPolicy profile)).terminal_iff hrelated)).mp
                hsourceActions
        have hfuel :
            (Nat.succ horizon) * (n + 2) =
              (n + 2) + horizon * (n + 2) := by
          rw [Nat.succ_mul, Nat.add_comm]
        rw [hfuel, Arena.stochasticHistoryLawFrom_add]
        have hblock :=
          serializedBehavioralExecution_eq_macroStepLaw
            G D rootPayoff sourceDeclaredRoot data profile source
            hsourceTerminal target hrelated htargetActions
        refine (hblock.bind (fun middle =>
          FiniteLaw.Equivalent.refl
            ((game G rootPayoff).toArena.stochasticHistoryLawFrom
              (serializedBehavioralHistoryPolicy G D rootPayoff
                sourceDeclaredRoot profile)
              middle (horizon * (n + 2))))).trans ?_
        simp only [KernelArena.stateLawFrom, dif_neg htargetActions]
        apply FiniteLaw.bind_congr_positive
        intro nextTarget hnextTarget
        have hstepCoupling :=
          (serializedMacroPolicy_match G D rootPayoff
              sourceDeclaredRoot data
              (D.behavioralHistoryPolicy profile)).stepCoupling
              hrelated hsourceActions htargetActions
        obtain ⟨nextSource, _, hnextRelated⟩ :=
          hstepCoupling.exists_left_of_hasPositiveAtom_right
            hnextTarget
        exact ih hnextRelated

/-- Under coupling-compatible randomized policies, the source FOSG and its
serialized EFG have an exact coupling of every finite macro trace.

Both marginals are the finite laws of the actual traces.  Every positive-mass pair is related
at each macro boundary by `Rel G`. -/
theorem macroTraceLawCoupling
    [(world : G.WorldState) → Decidable (G.isTerminal world)]
    (D : G.DecisionModel)
    (rootPayoff : Fin (n + 1) → U)
    (sourceDeclaredRoot : G.HistoryState → Prop)
    (data : MacroPolicyData G D rootPayoff sourceDeclaredRoot)
    [(target :
        (macroExecutionKernelArena G D rootPayoff
          sourceDeclaredRoot).State) →
      Decidable
        (IsEmpty
          ((macroExecutionKernelArena G D rootPayoff
            sourceDeclaredRoot).Action target))]
    (sourcePolicy : G.historyKernelArena.Policy)
    (targetPolicy :
      (macroExecutionKernelArena G D rootPayoff
        sourceDeclaredRoot).Policy)
    (matchPolicy :
      (macroKernelSimulation G D rootPayoff sourceDeclaredRoot data).PolicyMatch
        sourcePolicy targetPolicy)
    {source : G.HistoryState}
    {target :
      (game G rootPayoff).toArena.HistoryFrom
        (game G rootPayoff).init}
    (hrelated : Rel G source target)
    (horizon : Nat) :
    Nonempty (FiniteLaw.RelCoupling (List.Forall₂ (Rel G))
      (G.historyKernelArena.traceLawFrom
        sourcePolicy horizon source)
      ((macroExecutionKernelArena G D rootPayoff
          sourceDeclaredRoot).traceLawFrom
        targetPolicy horizon target)) :=
  ⟨matchPolicy.traceLawCoupling hrelated horizon⟩

/-- The concrete policy compiler gives exact finite-horizon endpoint coupling
without requiring a caller-supplied target policy or matching witness. -/
theorem serializedMacroStateLawCoupling
    [(world : G.WorldState) → Decidable (G.isTerminal world)]
    (D : G.DecisionModel)
    (rootPayoff : Fin (n + 1) → U)
    (sourceDeclaredRoot : G.HistoryState → Prop)
    (data : MacroPolicyData G D rootPayoff sourceDeclaredRoot)
    [(target :
        (macroExecutionKernelArena G D rootPayoff
          sourceDeclaredRoot).State) →
      Decidable
        (IsEmpty
          ((macroExecutionKernelArena G D rootPayoff
            sourceDeclaredRoot).Action target))]
    (sourcePolicy : G.historyKernelArena.Policy)
    {source : G.HistoryState}
    {target :
      (game G rootPayoff).toArena.HistoryFrom
        (game G rootPayoff).init}
    (hrelated : Rel G source target)
    (horizon : Nat) :
    Nonempty (FiniteLaw.RelCoupling (Rel G)
      (G.historyKernelArena.stateLawFrom
        sourcePolicy horizon source)
      ((macroExecutionKernelArena G D rootPayoff
          sourceDeclaredRoot).stateLawFrom
        (serializedMacroPolicy G D rootPayoff sourceDeclaredRoot
          data sourcePolicy)
        horizon target)) :=
  ⟨(serializedMacroPolicy_match G D rootPayoff sourceDeclaredRoot
    data sourcePolicy).stateLawCoupling hrelated horizon⟩

/-- The concrete policy compiler gives exact complete-trace coupling without
requiring a caller-supplied target policy or matching witness. -/
theorem serializedMacroTraceLawCoupling
    [(world : G.WorldState) → Decidable (G.isTerminal world)]
    (D : G.DecisionModel)
    (rootPayoff : Fin (n + 1) → U)
    (sourceDeclaredRoot : G.HistoryState → Prop)
    (data : MacroPolicyData G D rootPayoff sourceDeclaredRoot)
    [(target :
        (macroExecutionKernelArena G D rootPayoff
          sourceDeclaredRoot).State) →
      Decidable
        (IsEmpty
          ((macroExecutionKernelArena G D rootPayoff
            sourceDeclaredRoot).Action target))]
    (sourcePolicy : G.historyKernelArena.Policy)
    {source : G.HistoryState}
    {target :
      (game G rootPayoff).toArena.HistoryFrom
        (game G rootPayoff).init}
    (hrelated : Rel G source target)
    (horizon : Nat) :
    Nonempty (FiniteLaw.RelCoupling (List.Forall₂ (Rel G))
      (G.historyKernelArena.traceLawFrom
        sourcePolicy horizon source)
      ((macroExecutionKernelArena G D rootPayoff
          sourceDeclaredRoot).traceLawFrom
        (serializedMacroPolicy G D rootPayoff sourceDeclaredRoot
          data sourcePolicy)
        horizon target)) :=
  macroTraceLawCoupling G D rootPayoff sourceDeclaredRoot data
    sourcePolicy
    (serializedMacroPolicy G D rootPayoff sourceDeclaredRoot
      data sourcePolicy)
    (serializedMacroPolicy_match G D rootPayoff sourceDeclaredRoot
      data sourcePolicy)
    hrelated horizon

/-- Information-indexed behavioral profiles have exactly coupled stopped
finite traces after serialization. -/
theorem serializedBehavioralTraceLawCoupling
    [(world : G.WorldState) → Decidable (G.isTerminal world)]
    (D : G.DecisionModel)
    (rootPayoff : Fin (n + 1) → U)
    (sourceDeclaredRoot : G.HistoryState → Prop)
    (data : MacroPolicyData G D rootPayoff sourceDeclaredRoot)
    [(target :
        (macroExecutionKernelArena G D rootPayoff
          sourceDeclaredRoot).State) →
      Decidable
        (IsEmpty
          ((macroExecutionKernelArena G D rootPayoff
            sourceDeclaredRoot).Action target))]
    (profile : D.BehavioralProfile)
    {source : G.HistoryState}
    {target :
      (game G rootPayoff).toArena.HistoryFrom
        (game G rootPayoff).init}
    (hrelated : Rel G source target)
    (horizon : Nat) :
    Nonempty (FiniteLaw.RelCoupling (List.Forall₂ (Rel G))
      (G.historyKernelArena.traceLawFrom
        (D.behavioralHistoryPolicy profile) horizon source)
      ((macroExecutionKernelArena G D rootPayoff
          sourceDeclaredRoot).traceLawFrom
        (serializedBehavioralMacroPolicy G D rootPayoff
          sourceDeclaredRoot data profile)
        horizon target)) :=
  serializedMacroTraceLawCoupling G D rootPayoff sourceDeclaredRoot data
    (D.behavioralHistoryPolicy profile) hrelated horizon

/-- The concrete serializer's payoff field agrees with the FOSG payoff vector
at every related macro boundary.

For nonterminal states this is an operational field equality; at terminal
states it is the economically meaningful terminal-payoff equality. -/
theorem payoff_eq_of_rel
    [(world : G.WorldState) → Decidable (G.isTerminal world)]
    (rootPayoff : Fin (n + 1) → U)
    (source : G.HistoryState)
    (target :
      (game G rootPayoff).toArena.HistoryFrom
        (game G rootPayoff).init)
    (hrelated : Rel G source target) :
    (game G rootPayoff).payoff target.1 =
      G.payoff source.1 := by
  rw [hrelated]
  by_cases hterminal : G.isTerminal source.1
  · rw [boundary_of_terminal G source hterminal]
    rfl
  · rw [boundary_of_not_terminal G source hterminal]
    rfl

/-- Terminal payoff represented at a complete serialized history.

Nonterminal histories map to `none`; in particular, administrative states and
fuel-exhausted macro boundaries do not expose their operational payoff field.
-/
def serializedStoppedPayoffAtHistory
    [(world : G.WorldState) → Decidable (G.isTerminal world)]
    (rootPayoff : Fin (n + 1) → U)
    (history :
      (game G rootPayoff).toArena.HistoryFrom
        (game G rootPayoff).init) :
    Option (Fin (n + 1) → U) :=
  match history.1 with
  | .terminal source _ => some (G.payoff source.1)
  | _ => none

/-- Related macro boundaries have exactly the same optional terminal payoff.
-/
theorem stoppedPayoff_eq_of_rel
    [(world : G.WorldState) → Decidable (G.isTerminal world)]
    (rootPayoff : Fin (n + 1) → U)
    (source : G.HistoryState)
    (target :
      (game G rootPayoff).toArena.HistoryFrom
        (game G rootPayoff).init)
    (hrelated : Rel G source target) :
    serializedStoppedPayoffAtHistory G rootPayoff target =
      G.stoppedPayoffAtHistory source := by
  by_cases hsourceTerminal : G.isTerminal source.1
  · change
      (match target.1 with
        | .terminal source _ => some (G.payoff source.1)
        | _ => none) = G.stoppedPayoffAtHistory source
    rw [hrelated, boundary_of_terminal G source hsourceTerminal]
    simp [FOSG.stoppedPayoffAtHistory, hsourceTerminal]
  · change
      (match target.1 with
        | .terminal source _ => some (G.payoff source.1)
        | _ => none) = G.stoppedPayoffAtHistory source
    rw [hrelated, boundary_of_not_terminal G source hsourceTerminal]
    simp [FOSG.stoppedPayoffAtHistory, hsourceTerminal]

/-- Exact equality of finite-horizon optional terminal-payoff laws under the
concrete policy compiler. -/
theorem serializedMacroPayoffLaw_eq
    [(world : G.WorldState) → Decidable (G.isTerminal world)]
    (D : G.DecisionModel)
    (rootPayoff : Fin (n + 1) → U)
    (sourceDeclaredRoot : G.HistoryState → Prop)
    (data : MacroPolicyData G D rootPayoff sourceDeclaredRoot)
    [(target :
        (macroExecutionKernelArena G D rootPayoff
          sourceDeclaredRoot).State) →
      Decidable
        (IsEmpty
          ((macroExecutionKernelArena G D rootPayoff
            sourceDeclaredRoot).Action target))]
    (sourcePolicy : G.historyKernelArena.Policy)
    {source : G.HistoryState}
    {target :
      (game G rootPayoff).toArena.HistoryFrom
        (game G rootPayoff).init}
    (hrelated : Rel G source target)
    (horizon : Nat) :
    ((G.historyKernelArena.stateLawFrom
        sourcePolicy horizon source).map
          G.stoppedPayoffAtHistory).Equivalent
      (((macroExecutionKernelArena G D rootPayoff
          sourceDeclaredRoot).stateLawFrom
        (serializedMacroPolicy G D rootPayoff sourceDeclaredRoot
          data sourcePolicy)
        horizon target).map
          (serializedStoppedPayoffAtHistory G rootPayoff)) := by
  obtain ⟨coupling⟩ :=
    serializedMacroStateLawCoupling G D rootPayoff
      sourceDeclaredRoot data sourcePolicy hrelated horizon
  exact
    coupling.map_eq
        (fun sourceState targetHistory hrel =>
          (stoppedPayoff_eq_of_rel G rootPayoff sourceState
            targetHistory hrel).symm)


end ExtensiveGame.FOSG.Sequentialization
