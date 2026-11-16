/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Simulation.Presentation.Kernel.Core

/-!
# Presentation.Kernel.ProfileAssembly — measurable player-profile assembly

`KernelBehavioralProfile` is an admissible complete joint policy. This module
adds a constructive layer: one jointly measurable player kernel on explicitly
tagged player inputs and a fixed abstract chance lift are combined into that
joint policy.

An `InformationRoles` certificate exposes measurable terminal and player
regions of the common information carrier and a measurable player tag.
`ProfileAssembly` additionally supplies an abstract chance kernel whose
history-dependent realization is the presentation's fixed concrete chance
law.

`PlayerKernelProfile` stores all player laws in one measurable kernel on a
tagged input carrier. This joint measurability is intentional: an arbitrary
family indexed by an uncountable player type need not glue to a kernel.
`PlayerStrategy` stores one replacement player's law.
Piecewise kernel composition implements `deviate`, while the role certificate
implements terminal/player/chance assembly.

No measurable ownership test, fallback player, or measurable selection is
inferred. Every set and map used by the branching construction is explicit
certificate data.
-/

open MeasureTheory ProbabilityTheory

namespace ExtensiveGame.ObservedGame

universe uN uU

variable {N : Type uN} {U : Type uU}

namespace MeasurableKernelPresentation

variable
  {G : ObservedGame N U}
  {model : MeasurableHistoryModel G}
  (presentation : MeasurableKernelPresentation G model)

/-- Measurable ownership and terminal/player/chance classification on the
presentation's common information carrier.

The player tag has type `Option N` so it is globally defined without choosing
a fallback player. It is semantically constrained only on represented player
prefixes. -/
structure InformationRoles where
  /-- Measurable structure used for player tags. -/
  playerTagMeasurable : MeasurableSpace (Option N)
  /-- Executable equality for player tags used by unilateral replacement. -/
  playerTagDecidableEq : DecidableEq (Option N)
  /-- A tagged player singleton is measurable, as required by unilateral
  piecewise update. -/
  playerTagSingleton_measurable :
    ∀ i : N,
      @MeasurableSet
        (Option N) playerTagMeasurable
        ({some i} : Set (Option N))
  /-- Information values classified as terminal. -/
  terminalInformationSet :
    (time : ℕ) →
      Set (presentation.information.Information time)
  /-- Executable classification of terminal information. -/
  terminalInformationDecidable :
    ∀ time, DecidablePred (· ∈ terminalInformationSet time)
  /-- Terminal information is measurable. -/
  terminalInformationSet_measurable :
    ∀ time, MeasurableSet (terminalInformationSet time)
  /-- Information values classified as player-controlled. -/
  playerInformationSet :
    (time : ℕ) →
      Set (presentation.information.Information time)
  /-- Executable classification of player-controlled information. -/
  playerInformationDecidable :
    ∀ time, DecidablePred (· ∈ playerInformationSet time)
  /-- Player-controlled information is measurable. -/
  playerInformationSet_measurable :
    ∀ time, MeasurableSet (playerInformationSet time)
  /-- Globally defined measurable player tag. -/
  playerTag :
    (time : ℕ) →
      presentation.information.Information time →
        Option N
  /-- Player tagging is measurable for the explicitly supplied tag sigma
  algebra. -/
  playerTag_measurable :
    ∀ time,
      @Measurable
        (presentation.information.Information time)
        (Option N)
        inferInstance playerTagMeasurable
        (playerTag time)
  /-- Every represented terminal prefix is classified as terminal. -/
  terminal_at :
    ∀ (time : ℕ)
      (events : model.toArena.EventPrefix time),
      G.base.isTerminal
          (MeasurableKernelArena.latestEventState time events).1 →
        presentation.information.informationAt time events ∈
          terminalInformationSet time
  /-- Every represented nonterminal player prefix is classified as
  nonterminal/player and receives its actual player tag. -/
  player_at :
    ∀ (time : ℕ)
      (events : model.toArena.EventPrefix time)
      (i : N)
      (_hnonterminal :
        ¬ G.base.isTerminal
          (MeasurableKernelArena.latestEventState time events).1)
      (_hmover :
        G.base.mover
            (MeasurableKernelArena.latestEventState time events).1 =
          some i),
      presentation.information.informationAt time events ∉
          terminalInformationSet time ∧
        presentation.information.informationAt time events ∈
          playerInformationSet time ∧
        playerTag time
            (presentation.information.informationAt time events) =
          some i
  /-- Every represented nonterminal chance prefix is classified as neither
  terminal nor player-controlled. -/
  chance_at :
    ∀ (time : ℕ)
      (events : model.toArena.EventPrefix time)
      (_hnonterminal :
        ¬ G.base.isTerminal
          (MeasurableKernelArena.latestEventState time events).1)
      (_hmover :
        G.base.mover
            (MeasurableKernelArena.latestEventState time events).1 =
          none),
      presentation.information.informationAt time events ∉
          terminalInformationSet time ∧
        presentation.information.informationAt time events ∉
          playerInformationSet time

/-- Measurable player/chance profile assembly data.

The chance law lives abstractly on the same carrier as player strategies and
is certified to realize to the presentation's fixed concrete chance kernel. -/
structure ProfileAssembly extends InformationRoles presentation where
  /-- Fixed abstract chance law on the common information carrier. -/
  chanceAbstractKernel :
    (time : ℕ) →
      Kernel
        (presentation.information.Information time)
        (presentation.realization.AbstractAction time)
  /-- The abstract chance kernel is globally s-finite. -/
  chanceAbstractKernel_isSFinite :
    ∀ time, IsSFiniteKernel (chanceAbstractKernel time)
  /-- The abstract chance law is normalized at represented chance prefixes. -/
  chance_isProbability :
    ∀ (time : ℕ)
      (events : model.toArena.EventPrefix time)
      (_hnonterminal :
        ¬ G.base.isTerminal
          (MeasurableKernelArena.latestEventState time events).1)
      (_hmover :
        G.base.mover
            (MeasurableKernelArena.latestEventState time events).1 =
          none),
      IsProbabilityMeasure
        (chanceAbstractKernel time
          (presentation.information.informationAt time events))
  /-- Almost every chance abstract action has a normalized realization. -/
  chance_realization_isProbability :
    ∀ (time : ℕ)
      (events : model.toArena.EventPrefix time)
      (_hnonterminal :
        ¬ G.base.isTerminal
          (MeasurableKernelArena.latestEventState time events).1)
      (_hmover :
        G.base.mover
            (MeasurableKernelArena.latestEventState time events).1 =
          none),
      ∀ᵐ abstractAction
          ∂chanceAbstractKernel time
            (presentation.information.informationAt time events),
        IsProbabilityMeasure
          (presentation.realization.kernel
            time (events, abstractAction))
  /-- The bound concrete chance-realization law lies in the current legal
  action fiber almost surely. -/
  chance_realization_legal :
    ∀ (time : ℕ)
      (events : model.toArena.EventPrefix time)
      (_hnonterminal :
        ¬ G.base.isTerminal
          (MeasurableKernelArena.latestEventState time events).1)
      (_hmover :
        G.base.mover
            (MeasurableKernelArena.latestEventState time events).1 =
          none),
      ∀ᵐ stateAction
          ∂(chanceAbstractKernel time
              (presentation.information.informationAt time events)).bind
            (fun abstractAction =>
              presentation.realization.kernel
                time (events, abstractAction)),
        stateAction ∈
          model.toArena.actionFiber
            (MeasurableKernelArena.latestEventState time events)
  /-- Realizing the abstract chance law gives exactly the fixed concrete
  chance-action kernel. -/
  chance_realizedKernel :
    ∀ (time : ℕ)
      (events : model.toArena.EventPrefix time)
      (_hnonterminal :
        ¬ G.base.isTerminal
          (MeasurableKernelArena.latestEventState time events).1)
      (_hmover :
        G.base.mover
            (MeasurableKernelArena.latestEventState time events).1 =
          none),
      (chanceAbstractKernel time
        (presentation.information.informationAt time events)).bind
          (fun abstractAction =>
            presentation.realization.kernel
              time (events, abstractAction)) =
        presentation.chanceKernel time events

namespace ProfileAssembly

variable
  {presentation : MeasurableKernelPresentation G model}
  (assembly : ProfileAssembly presentation)

instance instChanceAbstractKernelIsSFinite (time : ℕ) :
    IsSFiniteKernel (assembly.chanceAbstractKernel time) :=
  assembly.chanceAbstractKernel_isSFinite time

/-- Tagged input on which all player strategy kernels are stored.

The structure retains `assembly` in its type, so distinct assemblies may use
distinct measurable structures on `Option N` without a global instance
collision. -/
structure PlayerInput
    (assembly : ProfileAssembly presentation)
    (time : ℕ) where
  player : Option N
  information : presentation.information.Information time

/-- The tagged player-input carrier as an ordinary product. -/
def playerInputEquiv (time : ℕ) :
    assembly.PlayerInput time ≃
      Option N × presentation.information.Information time where
  toFun input := (input.player, input.information)
  invFun input := ⟨input.1, input.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Measurable structure transported from the explicit player-tag space and
the common information space. -/
instance instPlayerInputMeasurableSpace (time : ℕ) :
    MeasurableSpace (assembly.PlayerInput time) :=
  (assembly.playerTagMeasurable.prod inferInstance).comap
    (assembly.playerInputEquiv time)

/-- Forgetting the tag from a player input is measurable. -/
theorem playerInput_information_measurable (time : ℕ) :
    Measurable
      (fun input : assembly.PlayerInput time =>
        input.information) := by
  have hpair :
      @Measurable
        (assembly.PlayerInput time)
        (Option N × presentation.information.Information time)
        inferInstance
        (assembly.playerTagMeasurable.prod inferInstance)
        (assembly.playerInputEquiv time) :=
    comap_measurable (assembly.playerInputEquiv time)
  exact measurable_snd.comp hpair

/-- Reading the player tag is measurable for the assembly's explicit tag
sigma algebra. -/
theorem playerInput_player_measurable (time : ℕ) :
    @Measurable
      (assembly.PlayerInput time) (Option N)
      inferInstance assembly.playerTagMeasurable
      (fun input => input.player) := by
  have hpair :
      @Measurable
        (assembly.PlayerInput time)
        (Option N × presentation.information.Information time)
        inferInstance
        (assembly.playerTagMeasurable.prod inferInstance)
        (assembly.playerInputEquiv time) :=
    comap_measurable (assembly.playerInputEquiv time)
  exact measurable_fst.comp hpair

/-- Tag one common information value with its classified player owner. -/
def tagInformation (time : ℕ)
    (information : presentation.information.Information time) :
    assembly.PlayerInput time :=
  ⟨assembly.playerTag time information, information⟩

theorem tagInformation_measurable (time : ℕ) :
    Measurable (assembly.tagInformation time) := by
  rw [measurable_comap_iff]
  exact
    Measurable.prod
      (assembly.playerTag_measurable time)
      measurable_id

/-- A complete measurable collection of player strategy laws. -/
structure PlayerKernelProfile
    (assembly : ProfileAssembly presentation) where
  /-- Joint kernel indexed by a player tag and common information value. -/
  kernel :
    (time : ℕ) →
      Kernel
        (assembly.PlayerInput time)
        (presentation.realization.AbstractAction time)
  /-- The joint player kernel is globally s-finite. -/
  kernel_isSFinite :
    ∀ time, IsSFiniteKernel (kernel time)
  /-- At every represented player prefix, the acting player's law is
  normalized. -/
  isProbability :
    ∀ (time : ℕ)
      (events : model.toArena.EventPrefix time)
      (i : N)
      (_hnonterminal :
        ¬ G.base.isTerminal
          (MeasurableKernelArena.latestEventState time events).1)
      (_hmover :
        G.base.mover
            (MeasurableKernelArena.latestEventState time events).1 =
          some i),
      IsProbabilityMeasure
        (kernel time
          ⟨some i,
            presentation.information.informationAt time events⟩)
  /-- Almost every selected player action has a normalized realization. -/
  realization_isProbability :
    ∀ (time : ℕ)
      (events : model.toArena.EventPrefix time)
      (i : N)
      (_hnonterminal :
        ¬ G.base.isTerminal
          (MeasurableKernelArena.latestEventState time events).1)
      (_hmover :
        G.base.mover
            (MeasurableKernelArena.latestEventState time events).1 =
          some i),
      ∀ᵐ abstractAction
          ∂kernel time
            ⟨some i,
              presentation.information.informationAt time events⟩,
        IsProbabilityMeasure
          (presentation.realization.kernel
            time (events, abstractAction))
  /-- The bound concrete player-realization law lies in the current legal
  action fiber almost surely. -/
  realization_legal :
    ∀ (time : ℕ)
      (events : model.toArena.EventPrefix time)
      (i : N)
      (_hnonterminal :
        ¬ G.base.isTerminal
          (MeasurableKernelArena.latestEventState time events).1)
      (_hmover :
        G.base.mover
            (MeasurableKernelArena.latestEventState time events).1 =
          some i),
      ∀ᵐ stateAction
          ∂(kernel time
              ⟨some i,
                presentation.information.informationAt time events⟩).bind
            (fun abstractAction =>
              presentation.realization.kernel
                time (events, abstractAction)),
        stateAction ∈
          model.toArena.actionFiber
            (MeasurableKernelArena.latestEventState time events)

instance PlayerKernelProfile.instKernelIsSFinite
    (profile : assembly.PlayerKernelProfile)
    (time : ℕ) :
    IsSFiniteKernel (profile.kernel time) :=
  profile.kernel_isSFinite time

/-- One player's measurable replacement strategy. -/
structure PlayerStrategy
    (assembly : ProfileAssembly presentation)
    (who : N) where
  /-- Replacement law indexed by common information. -/
  kernel :
    (time : ℕ) →
      Kernel
        (presentation.information.Information time)
        (presentation.realization.AbstractAction time)
  /-- The replacement kernel is globally s-finite. -/
  kernel_isSFinite :
    ∀ time, IsSFiniteKernel (kernel time)
  /-- The replacement is normalized whenever `who` controls a represented
  nonterminal prefix. -/
  isProbability :
    ∀ (time : ℕ)
      (events : model.toArena.EventPrefix time)
      (_hnonterminal :
        ¬ G.base.isTerminal
          (MeasurableKernelArena.latestEventState time events).1)
      (_hmover :
        G.base.mover
            (MeasurableKernelArena.latestEventState time events).1 =
          some who),
      IsProbabilityMeasure
        (kernel time
          (presentation.information.informationAt time events))
  /-- Almost every replacement action has a normalized realization. -/
  realization_isProbability :
    ∀ (time : ℕ)
      (events : model.toArena.EventPrefix time)
      (_hnonterminal :
        ¬ G.base.isTerminal
          (MeasurableKernelArena.latestEventState time events).1)
      (_hmover :
        G.base.mover
            (MeasurableKernelArena.latestEventState time events).1 =
          some who),
      ∀ᵐ abstractAction
          ∂kernel time
            (presentation.information.informationAt time events),
        IsProbabilityMeasure
          (presentation.realization.kernel
            time (events, abstractAction))
  /-- The bound concrete replacement-realization law lies in the current
  legal fiber almost surely. -/
  realization_legal :
    ∀ (time : ℕ)
      (events : model.toArena.EventPrefix time)
      (_hnonterminal :
        ¬ G.base.isTerminal
          (MeasurableKernelArena.latestEventState time events).1)
      (_hmover :
        G.base.mover
            (MeasurableKernelArena.latestEventState time events).1 =
          some who),
      ∀ᵐ stateAction
          ∂(kernel time
              (presentation.information.informationAt time events)).bind
            (fun abstractAction =>
              presentation.realization.kernel
                time (events, abstractAction)),
        stateAction ∈
          model.toArena.actionFiber
            (MeasurableKernelArena.latestEventState time events)

instance PlayerStrategy.instKernelIsSFinite
    {who : N}
    (strategy : assembly.PlayerStrategy who)
    (time : ℕ) :
    IsSFiniteKernel (strategy.kernel time) :=
  strategy.kernel_isSFinite time

/-- Tagged inputs belonging to the deviating player. -/
def deviationSet (who : N) (time : ℕ) :
    Set (assembly.PlayerInput time) :=
  {input | input.player = some who}

theorem deviationSet_measurable (who : N) (time : ℕ) :
    MeasurableSet (assembly.deviationSet who time) :=
  (assembly.playerInput_player_measurable time)
    (assembly.playerTagSingleton_measurable who)

/-- Regard one player's replacement law as a kernel on all tagged inputs by
forgetting the tag. -/
def PlayerStrategy.onPlayerInput
    {who : N}
    (strategy : assembly.PlayerStrategy who)
    (time : ℕ) :
    Kernel
      (assembly.PlayerInput time)
      (presentation.realization.AbstractAction time) :=
  Kernel.comap
    (strategy.kernel time)
    (fun input => input.information)
    (assembly.playerInput_information_measurable time)

instance PlayerStrategy.onPlayerInput_isSFinite
    {who : N}
    (strategy : assembly.PlayerStrategy who)
    (time : ℕ) :
    IsSFiniteKernel
      (PlayerStrategy.onPlayerInput
        (assembly := assembly) strategy time) := by
  rw [PlayerStrategy.onPlayerInput]
  infer_instance

/-- Replace exactly one player's tagged kernel by measurable piecewise
branching. -/
def PlayerKernelProfile.deviate
    (profile : assembly.PlayerKernelProfile)
    (who : N)
    (strategy : assembly.PlayerStrategy who) :
    assembly.PlayerKernelProfile := by
  letI : DecidableEq (Option N) := assembly.playerTagDecidableEq
  letI (time : ℕ) : DecidablePred (· ∈ assembly.deviationSet who time) :=
    fun input => assembly.playerTagDecidableEq input.player (some who)
  exact
    {
      kernel := fun time =>
        Kernel.piecewise
          (assembly.deviationSet_measurable who time)
          (PlayerStrategy.onPlayerInput
            (assembly := assembly) strategy time)
          (profile.kernel time)
      kernel_isSFinite := by
        intro time
        infer_instance
      isProbability := by
        intro time events i hnonterminal hmover
        rw [Kernel.piecewise_apply]
        by_cases hwho : i = who
        · subst i
          rw [if_pos]
          · exact strategy.isProbability time events hnonterminal hmover
          · simp [deviationSet]
        · rw [if_neg]
          · exact
              profile.isProbability
                time events i hnonterminal hmover
          · simp [deviationSet, hwho]
      realization_isProbability := by
        intro time events i hnonterminal hmover
        rw [Kernel.piecewise_apply]
        by_cases hwho : i = who
        · subst i
          rw [if_pos]
          · exact
              strategy.realization_isProbability
                time events hnonterminal hmover
          · simp [deviationSet]
        · rw [if_neg]
          · exact
              profile.realization_isProbability
                time events i hnonterminal hmover
          · simp [deviationSet, hwho]
      realization_legal := by
        intro time events i hnonterminal hmover
        rw [Kernel.piecewise_apply]
        by_cases hwho : i = who
        · subst i
          rw [if_pos]
          · exact
              strategy.realization_legal
                time events hnonterminal hmover
          · simp [deviationSet]
        · rw [if_neg]
          · exact
              profile.realization_legal
                time events i hnonterminal hmover
          · simp [deviationSet, hwho]
    }

@[simp]
theorem PlayerKernelProfile.deviate_kernel_same
    (profile : assembly.PlayerKernelProfile)
    (who : N)
    (strategy : assembly.PlayerStrategy who)
    (time : ℕ)
    (information : presentation.information.Information time) :
    (PlayerKernelProfile.deviate
      (assembly := assembly) profile who strategy).kernel time
        ⟨some who, information⟩ =
      strategy.kernel time information := by
  classical
  letI : DecidableEq (Option N) := assembly.playerTagDecidableEq
  letI (time : ℕ) : DecidablePred (· ∈ assembly.deviationSet who time) :=
    fun input => assembly.playerTagDecidableEq input.player (some who)
  rw [PlayerKernelProfile.deviate, Kernel.piecewise_apply]
  simp [deviationSet, PlayerStrategy.onPlayerInput]

@[simp]
theorem PlayerKernelProfile.deviate_kernel_of_ne
    (profile : assembly.PlayerKernelProfile)
    (who : N)
    (strategy : assembly.PlayerStrategy who)
    (time : ℕ)
    (information : presentation.information.Information time)
    {other : N}
    (hne : other ≠ who) :
    (PlayerKernelProfile.deviate
      (assembly := assembly) profile who strategy).kernel time
        ⟨some other, information⟩ =
      profile.kernel time ⟨some other, information⟩ := by
  classical
  letI : DecidableEq (Option N) := assembly.playerTagDecidableEq
  letI (time : ℕ) : DecidablePred (· ∈ assembly.deviationSet who time) :=
    fun input => assembly.playerTagDecidableEq input.player (some who)
  rw [PlayerKernelProfile.deviate, Kernel.piecewise_apply]
  simp [deviationSet, hne]

/-- Player-law kernel on the common information carrier after measurable
owner tagging. -/
def playerAbstractKernel
    (profile : assembly.PlayerKernelProfile)
    (time : ℕ) :
    Kernel
      (presentation.information.Information time)
      (presentation.realization.AbstractAction time) :=
  Kernel.comap
    (profile.kernel time)
    (assembly.tagInformation time)
    (assembly.tagInformation_measurable time)

instance playerAbstractKernel_isSFinite
    (profile : assembly.PlayerKernelProfile)
    (time : ℕ) :
    IsSFiniteKernel (assembly.playerAbstractKernel profile time) := by
  rw [playerAbstractKernel]
  infer_instance

/-- Combine player and chance laws away from terminal information. -/
def nonterminalAbstractKernel
    (profile : assembly.PlayerKernelProfile)
    (time : ℕ) :
    Kernel
      (presentation.information.Information time)
      (presentation.realization.AbstractAction time) := by
  letI := assembly.playerInformationDecidable time
  exact
    Kernel.piecewise
      (assembly.playerInformationSet_measurable time)
      (assembly.playerAbstractKernel profile time)
      (assembly.chanceAbstractKernel time)

instance nonterminalAbstractKernel_isSFinite
    (profile : assembly.PlayerKernelProfile)
    (time : ℕ) :
    IsSFiniteKernel
      (assembly.nonterminalAbstractKernel profile time) := by
  rw [nonterminalAbstractKernel]
  infer_instance

/-- Full abstract policy kernel: terminal zero, otherwise player or chance. -/
def abstractKernel
    (profile : assembly.PlayerKernelProfile)
    (time : ℕ) :
    Kernel
      (presentation.information.Information time)
      (presentation.realization.AbstractAction time) := by
  letI := assembly.terminalInformationDecidable time
  exact
    Kernel.piecewise
      (assembly.terminalInformationSet_measurable time)
      0
      (assembly.nonterminalAbstractKernel profile time)

instance abstractKernel_isSFinite
    (profile : assembly.PlayerKernelProfile)
    (time : ℕ) :
    IsSFiniteKernel (assembly.abstractKernel profile time) := by
  rw [abstractKernel]
  infer_instance

theorem abstractKernel_apply_terminal
    (profile : assembly.PlayerKernelProfile)
    (time : ℕ)
    (events : model.toArena.EventPrefix time)
    (hterminal :
      G.base.isTerminal
        (MeasurableKernelArena.latestEventState time events).1) :
    assembly.abstractKernel profile time
        (presentation.information.informationAt time events) =
      0 := by
  classical
  letI := assembly.terminalInformationDecidable time
  letI := assembly.playerInformationDecidable time
  rw [abstractKernel, Kernel.piecewise_apply]
  rw [if_pos (assembly.terminal_at time events hterminal)]
  rfl

theorem abstractKernel_apply_player
    (profile : assembly.PlayerKernelProfile)
    (time : ℕ)
    (events : model.toArena.EventPrefix time)
    (i : N)
    (hnonterminal :
      ¬ G.base.isTerminal
        (MeasurableKernelArena.latestEventState time events).1)
    (hmover :
      G.base.mover
          (MeasurableKernelArena.latestEventState time events).1 =
        some i) :
    assembly.abstractKernel profile time
        (presentation.information.informationAt time events) =
      profile.kernel time
        ⟨some i,
          presentation.information.informationAt time events⟩ := by
  classical
  letI := assembly.terminalInformationDecidable time
  letI := assembly.playerInformationDecidable time
  rcases
      assembly.player_at time events i hnonterminal hmover with
    ⟨hnotTerminal, hplayer, htag⟩
  rw [abstractKernel, Kernel.piecewise_apply, if_neg hnotTerminal]
  rw [nonterminalAbstractKernel, Kernel.piecewise_apply, if_pos hplayer]
  change
    profile.kernel time
        (assembly.tagInformation time
          (presentation.information.informationAt time events)) =
      _
  rw [tagInformation, htag]

theorem abstractKernel_apply_chance
    (profile : assembly.PlayerKernelProfile)
    (time : ℕ)
    (events : model.toArena.EventPrefix time)
    (hnonterminal :
      ¬ G.base.isTerminal
        (MeasurableKernelArena.latestEventState time events).1)
    (hmover :
      G.base.mover
          (MeasurableKernelArena.latestEventState time events).1 =
        none) :
    assembly.abstractKernel profile time
        (presentation.information.informationAt time events) =
      assembly.chanceAbstractKernel time
        (presentation.information.informationAt time events) := by
  classical
  letI := assembly.terminalInformationDecidable time
  letI := assembly.playerInformationDecidable time
  rcases assembly.chance_at time events hnonterminal hmover with
    ⟨hnotTerminal, hnotPlayer⟩
  rw [abstractKernel, Kernel.piecewise_apply, if_neg hnotTerminal]
  rw [
    nonterminalAbstractKernel,
    Kernel.piecewise_apply,
    if_neg hnotPlayer]

/-- Assemble all player kernels and the fixed chance lift into one admissible
realized action policy. -/
def toRealizedActionPolicy
    (profile : assembly.PlayerKernelProfile) :
    MeasurableKernelArena.EventInformation.RealizedActionPolicy
      presentation.realization where
  abstractKernel := assembly.abstractKernel profile
  abstractKernel_isSFinite := by
    intro time
    infer_instance
  terminal_zero := by
    intro time events hterminal
    exact assembly.abstractKernel_apply_terminal
      profile time events hterminal
  nonterminal_isProbability := by
    intro time events hnonterminal
    cases hmover :
        G.base.mover
          (MeasurableKernelArena.latestEventState time events).1 with
    | some i =>
        rw [
          assembly.abstractKernel_apply_player
            profile time events i hnonterminal hmover]
        exact
          profile.isProbability
            time events i hnonterminal hmover
    | none =>
        rw [
          assembly.abstractKernel_apply_chance
            profile time events hnonterminal hmover]
        exact
          assembly.chance_isProbability
            time events hnonterminal hmover
  realization_isProbability := by
    intro time events hnonterminal
    cases hmover :
        G.base.mover
          (MeasurableKernelArena.latestEventState time events).1 with
    | some i =>
        rw [
          assembly.abstractKernel_apply_player
            profile time events i hnonterminal hmover]
        exact
          profile.realization_isProbability
            time events i hnonterminal hmover
    | none =>
        rw [
          assembly.abstractKernel_apply_chance
            profile time events hnonterminal hmover]
        exact
          assembly.chance_realization_isProbability
            time events hnonterminal hmover
  realization_legal := by
    intro time events hnonterminal
    cases hmover :
        G.base.mover
          (MeasurableKernelArena.latestEventState time events).1 with
    | some i =>
        rw [
          assembly.abstractKernel_apply_player
            profile time events i hnonterminal hmover]
        exact
          profile.realization_legal
            time events i hnonterminal hmover
    | none =>
        rw [
          assembly.abstractKernel_apply_chance
            profile time events hnonterminal hmover]
        exact
          assembly.chance_realization_legal
            time events hnonterminal hmover

/-- Assemble a player-kernel profile into the generic kernel-valued observed
profile. -/
def toKernelBehavioralProfile
    (profile : assembly.PlayerKernelProfile) :
    presentation.KernelBehavioralProfile where
  policy := assembly.toRealizedActionPolicy profile
  chance_eq := by
    intro time events hnonterminal hmover
    rw [
      MeasurableKernelArena.EventInformation.RealizedActionPolicy.realizedKernel_apply]
    change
      (assembly.abstractKernel profile time
        (presentation.information.informationAt time events)).bind
          (fun abstractAction =>
            presentation.realization.kernel
              time (events, abstractAction)) =
        presentation.chanceKernel time events
    rw [
      assembly.abstractKernel_apply_chance
        profile time events hnonterminal hmover]
    exact
      assembly.chance_realizedKernel
        time events hnonterminal hmover

/-- Construct assembly data from explicit roles and one reference admissible
profile. The reference supplies an abstract lift of the already fixed concrete
chance law. -/
def ofReference
    (roles : InformationRoles presentation)
    (reference : presentation.KernelBehavioralProfile) :
    ProfileAssembly presentation where
  toInformationRoles := roles
  chanceAbstractKernel := reference.policy.abstractKernel
  chanceAbstractKernel_isSFinite :=
    reference.policy.abstractKernel_isSFinite
  chance_isProbability := by
    intro time events hnonterminal _hmover
    exact
      reference.policy.nonterminal_isProbability
        time events hnonterminal
  chance_realization_isProbability := by
    intro time events hnonterminal _hmover
    exact
      reference.policy.realization_isProbability
        time events hnonterminal
  chance_realization_legal := by
    intro time events hnonterminal _hmover
    exact
      reference.policy.realization_legal
        time events hnonterminal
  chance_realizedKernel := by
    intro time events hnonterminal hmover
    rw [
      ← MeasurableKernelArena.EventInformation.RealizedActionPolicy.realizedKernel_apply]
    exact reference.chance_eq time events hnonterminal hmover

/-- Split the player branches of an existing generic profile into one tagged
player kernel. The tag is ignored because the original abstract law already
depends only on common information. -/
def PlayerKernelProfile.ofKernelBehavioralProfile
    (profile : presentation.KernelBehavioralProfile) :
    assembly.PlayerKernelProfile where
  kernel := fun time =>
    Kernel.comap
      (profile.policy.abstractKernel time)
      (fun input : assembly.PlayerInput time =>
        input.information)
      (assembly.playerInput_information_measurable time)
  kernel_isSFinite := by
    intro time
    infer_instance
  isProbability := by
    intro time events _i hnonterminal _hmover
    exact
      profile.policy.nonterminal_isProbability
        time events hnonterminal
  realization_isProbability := by
    intro time events _i hnonterminal _hmover
    exact
      profile.policy.realization_isProbability
        time events hnonterminal
  realization_legal := by
    intro time events _i hnonterminal _hmover
    exact
      profile.policy.realization_legal
        time events hnonterminal

/-- Reassembling the player branches of an existing profile preserves its raw
compiled event policy exactly. Chance abstract lifts may differ, but both
realize to the same fixed concrete chance law. -/
theorem toKernelBehavioralProfile_ofKernelBehavioralProfile_compiledPolicy
    (profile : presentation.KernelBehavioralProfile) :
    (assembly.toKernelBehavioralProfile
        (PlayerKernelProfile.ofKernelBehavioralProfile
          (assembly := assembly) profile)
      ).compiledPolicy =
      profile.compiledPolicy := by
  apply MeasurableKernelArena.EventHistoryActionPolicy.ext
  funext time
  apply Kernel.ext
  intro events
  by_cases hterminal :
      G.base.isTerminal
        (MeasurableKernelArena.latestEventState time events).1
  · rw [
      (assembly.toKernelBehavioralProfile
        (PlayerKernelProfile.ofKernelBehavioralProfile
          (assembly := assembly) profile)).compiledPolicy.terminal_zero
        time events hterminal,
      profile.compiledPolicy.terminal_zero
        time events hterminal]
  · cases hmover :
        G.base.mover
          (MeasurableKernelArena.latestEventState time events).1 with
    | some i =>
        rw [
          MeasurableKernelPresentation.KernelBehavioralProfile.compiledPolicy_kernel,
          MeasurableKernelPresentation.KernelBehavioralProfile.compiledPolicy_kernel,
          MeasurableKernelArena.EventInformation.RealizedActionPolicy.realizedKernel_apply,
          MeasurableKernelArena.EventInformation.RealizedActionPolicy.realizedKernel_apply]
        change
          (assembly.abstractKernel
            (PlayerKernelProfile.ofKernelBehavioralProfile
              (assembly := assembly) profile)
            time
            (presentation.information.informationAt time events)).bind
              (fun abstractAction =>
                presentation.realization.kernel
                  time (events, abstractAction)) =
            (profile.policy.abstractKernel time
              (presentation.information.informationAt time events)).bind
                (fun abstractAction =>
                  presentation.realization.kernel
                    time (events, abstractAction))
        rw [
          assembly.abstractKernel_apply_player
            (PlayerKernelProfile.ofKernelBehavioralProfile
              (assembly := assembly) profile)
            time events i hterminal hmover]
        rfl
    | none =>
        rw [
          (assembly.toKernelBehavioralProfile
            (PlayerKernelProfile.ofKernelBehavioralProfile
              (assembly := assembly) profile)).compiledPolicy_kernel_of_chance
            time events hterminal hmover,
          profile.compiledPolicy_kernel_of_chance
            time events hterminal hmover]

/-- Constructively deviating one tagged player produces a unilateral deviation
in the generic abstract-kernel sense. -/
theorem toKernelBehavioralProfile_deviate
    (profile : assembly.PlayerKernelProfile)
    (who : N)
    (strategy : assembly.PlayerStrategy who) :
    (assembly.toKernelBehavioralProfile profile).IsUnilateralDeviation
      who
      (assembly.toKernelBehavioralProfile
        (PlayerKernelProfile.deviate
          (assembly := assembly) profile who strategy)) := by
  intro time events i hmover hne
  change
    assembly.abstractKernel profile time
        (presentation.information.informationAt time events) =
      assembly.abstractKernel
        (PlayerKernelProfile.deviate
          (assembly := assembly) profile who strategy)
        time
        (presentation.information.informationAt time events)
  by_cases hterminal :
      G.base.isTerminal
        (MeasurableKernelArena.latestEventState time events).1
  · rw [
      assembly.abstractKernel_apply_terminal
        profile time events hterminal,
      assembly.abstractKernel_apply_terminal
        (PlayerKernelProfile.deviate
          (assembly := assembly) profile who strategy)
        time events hterminal]
  · rw [
      assembly.abstractKernel_apply_player
        profile time events i hterminal hmover,
      assembly.abstractKernel_apply_player
        (PlayerKernelProfile.deviate
          (assembly := assembly) profile who strategy)
        time events i hterminal hmover,
      PlayerKernelProfile.deviate_kernel_of_ne
        (assembly := assembly) profile who strategy time
        (presentation.information.informationAt time events)
        hne]

end ProfileAssembly

end MeasurableKernelPresentation

end ExtensiveGame.ObservedGame
