/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.Math.Probability.FiniteMarkovChain.Reachability
import Mathlib.Data.NNRat.Order

/-!
# Deterministic monitors for finite rational Markov chains

This module forms the exact finite product of a rational Markov chain and a
finite deterministic monitor.  Monitor states are `Fin q`.  Transient and
terminal chain states may use different label types and therefore have
separate deterministic update functions.

## Label-consumption convention

A product transient state `(i, s)` means that the label of the current chain
state `i` has already been consumed and the monitor is now in state `s`.
Consequently a transition from `(i, s)` to transient state `j` stores
`nextTransient s (transientLabel j)`, while a transition to terminal state
`a` stores `nextTerminal s (terminalLabel a)`.  `initialProductState` consumes
the initial transient label exactly once before the first Markov transition.
No path state or transition occurrence is replaced by an endpoint-only
summary: the monitor state is the deterministic fold of every consumed label.

The product uses the standard equivalence
`Fin n × Fin q ≃ Fin (n * q)` required by `Chain`, while exposing type-safe
encode/decode functions and their inverse laws.  Terminal acceptance is
checked only after an original terminal label has been consumed.  This is a
finite-word, terminal-time monitor; it is not an omega-word parity or Büchi
automaton.

`monitoredOutcomeLaw` reuses the general reachability solver.  Its `none`
outcome explicitly retains nontermination mass, including mass trapped in a
closed nonterminal class.  `acceptanceProbability` is the exact event mass of
accepted terminal product states in that checked finite law.  The raw
`acceptanceValue` is the corresponding sum of
`Chain.terminalProbability` values.  A local bridge under the executable
outcome-validity check lets the existing reachability correctness theorems
identify the two; no analytic object is imported here.

For a chain with `n` transient states, `m` terminal states, and `q` monitor
states, the product has `n*q` transient and `m*q` terminal states.  A dense
row contains those full dimensions, although exactly one monitor successor
per underlying destination can carry positive mass.  The reachability solver
therefore has the dense rational linear-algebra cost for dimension `n*q`.
-/

namespace FiniteLaw

/-- A Boolean event in a normalized finite law has mass at most one. -/
theorem eventMass_le_one (law : FiniteLaw α) (event : α → Bool) :
    law.eventMass event ≤ 1 := by
  unfold eventMass
  rw [← law.normalized]
  induction law.atoms with
  | nil => simp
  | cons atom atoms ih =>
      simp only [List.map_cons, List.sum_cons]
      by_cases h : event atom.1
      · simpa [h, add_comm] using add_le_add_left ih atom.2
      · simp only [h, Bool.false_eq_true, ↓reduceIte, zero_add]
        exact le_add_left ih

end FiniteLaw

namespace FiniteMarkovChain

open Matrix
open scoped BigOperators

universe uT uF

/-- A finite deterministic terminal-time monitor.

The two update functions permit different label types on transient and
terminal states.  `accepting` is inspected only after a terminal label has
been consumed. -/
structure DeterministicMonitor
    (q : ℕ) (TransientLabel : Type uT) (TerminalLabel : Type uF) where
  /-- Monitor state before the initial transient label is consumed. -/
  initial : Fin q
  /-- Consume the label of a transient state. -/
  nextTransient : Fin q → TransientLabel → Fin q
  /-- Consume the label of a terminal state. -/
  nextTerminal : Fin q → TerminalLabel → Fin q
  /-- Acceptance test after terminal-label consumption. -/
  accepting : Fin q → Bool

/-- Type-safe pair represented by the flat `Fin (n * q)` index required by
the finite-chain matrix interface. -/
abbrev ProductState (n q : ℕ) := Fin n × Fin q

namespace ProductState

/-- Encode an underlying state and monitor state as one flat finite index. -/
def encode {n q : ℕ} (state : ProductState n q) : Fin (n * q) :=
  finProdFinEquiv state

/-- Decode a flat product index into its underlying and monitor coordinates. -/
def decode {n q : ℕ} (state : Fin (n * q)) : ProductState n q :=
  finProdFinEquiv.symm state

@[simp]
theorem decode_encode {n q : ℕ} (state : ProductState n q) :
    decode (encode state) = state :=
  finProdFinEquiv.symm_apply_apply state

@[simp]
theorem encode_decode {n q : ℕ} (state : Fin (n * q)) :
    encode (decode state) = state :=
  finProdFinEquiv.apply_symm_apply state

end ProductState

namespace Chain

variable {n m q : ℕ}
variable {TransientLabel : Type uT} {TerminalLabel : Type uF}
variable (C : Chain n m)
variable (monitor : DeterministicMonitor q TransientLabel TerminalLabel)

/-- Transient coefficient of the monitored product before packaging it as a
normalized chain. -/
def monitoredTransient
    (transientLabel : Fin n → TransientLabel)
    (source target : Fin (n * q)) : ℚ≥0 :=
  let sourceState := ProductState.decode source
  let targetState := ProductState.decode target
  if targetState.2 =
      monitor.nextTransient sourceState.2 (transientLabel targetState.1) then
    C.transient sourceState.1 targetState.1
  else
    0

/-- Terminal coefficient of the monitored product. -/
def monitoredTerminal
    (terminalLabel : Fin m → TerminalLabel)
    (source : Fin (n * q)) (target : Fin (m * q)) : ℚ≥0 :=
  let sourceState := ProductState.decode source
  let targetState := ProductState.decode target
  if targetState.2 =
      monitor.nextTerminal sourceState.2 (terminalLabel targetState.1) then
    C.terminal sourceState.1 targetState.1
  else
    0

/-- Summing over the monitor coordinate preserves the original transient row
mass. -/
theorem sum_monitoredTransient
    (transientLabel : Fin n → TransientLabel)
    (source : Fin (n * q)) :
    (∑ target, C.monitoredTransient monitor transientLabel source target) =
      ∑ target, C.transient (ProductState.decode source).1 target := by
  rw [← (finProdFinEquiv : Fin n × Fin q ≃ Fin (n * q)).sum_comp]
  rw [Fintype.sum_prod_type]
  simp [monitoredTransient, ProductState.decode]

/-- Summing over the monitor coordinate preserves the original terminal row
mass. -/
theorem sum_monitoredTerminal
    (terminalLabel : Fin m → TerminalLabel)
    (source : Fin (n * q)) :
    (∑ target, C.monitoredTerminal monitor terminalLabel source target) =
      ∑ target, C.terminal (ProductState.decode source).1 target := by
  rw [← (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)).sum_comp]
  rw [Fintype.sum_prod_type]
  simp [monitoredTerminal, ProductState.decode]

/-- Exact chain-monitor product.

The terminal reward is the zero/one acceptance indicator.  Nontermination is
not assigned that reward: it remains the separate `none` outcome of the
reachability solver. -/
def monitorProduct
    (transientLabel : Fin n → TransientLabel)
    (terminalLabel : Fin m → TerminalLabel) :
    Chain (n * q) (m * q) where
  transient := C.monitoredTransient monitor transientLabel
  terminal := C.monitoredTerminal monitor terminalLabel
  normalized source := by
    rw [C.sum_monitoredTransient monitor transientLabel source]
    rw [C.sum_monitoredTerminal monitor terminalLabel source]
    exact C.normalized (ProductState.decode source).1
  reward terminal :=
    if monitor.accepting (ProductState.decode terminal).2 then 1 else 0

/-- The product row is normalized, including when closed nonterminal classes
are present in the original chain. -/
theorem monitorProduct_normalized
    (transientLabel : Fin n → TransientLabel)
    (terminalLabel : Fin m → TerminalLabel)
    (source : Fin (n * q)) :
    (∑ target, (C.monitorProduct monitor transientLabel terminalLabel).transient
      source target) +
      (∑ target, (C.monitorProduct monitor transientLabel terminalLabel).terminal
        source target) = 1 :=
  (C.monitorProduct monitor transientLabel terminalLabel).normalized source

/-- Exact transient coefficient at type-safe encoded coordinates. -/
@[simp]
theorem monitorProduct_transient_encode
    (transientLabel : Fin n → TransientLabel)
    (terminalLabel : Fin m → TerminalLabel)
    (source target : Fin n) (monitorSource monitorTarget : Fin q) :
    (C.monitorProduct monitor transientLabel terminalLabel).transient
        (ProductState.encode (source, monitorSource))
        (ProductState.encode (target, monitorTarget)) =
      if monitorTarget =
          monitor.nextTransient monitorSource (transientLabel target) then
        C.transient source target
      else
        0 := by
  simp [monitorProduct, monitoredTransient]

/-- Exact terminal coefficient at type-safe encoded coordinates. -/
@[simp]
theorem monitorProduct_terminal_encode
    (transientLabel : Fin n → TransientLabel)
    (terminalLabel : Fin m → TerminalLabel)
    (source : Fin n) (terminal : Fin m)
    (monitorSource monitorTarget : Fin q) :
    (C.monitorProduct monitor transientLabel terminalLabel).terminal
        (ProductState.encode (source, monitorSource))
        (ProductState.encode (terminal, monitorTarget)) =
      if monitorTarget =
          monitor.nextTerminal monitorSource (terminalLabel terminal) then
        C.terminal source terminal
      else
        0 := by
  simp [monitorProduct, monitoredTerminal]

/-- Positive product transient mass forces the unique deterministic monitor
update and a positive underlying transition. -/
theorem monitorProduct_transient_pos_iff
    (transientLabel : Fin n → TransientLabel)
    (terminalLabel : Fin m → TerminalLabel)
    (source target : Fin n) (monitorSource monitorTarget : Fin q) :
    0 < (C.monitorProduct monitor transientLabel terminalLabel).transient
        (ProductState.encode (source, monitorSource))
        (ProductState.encode (target, monitorTarget)) ↔
      monitorTarget =
          monitor.nextTransient monitorSource (transientLabel target) ∧
        0 < C.transient source target := by
  rw [C.monitorProduct_transient_encode monitor transientLabel terminalLabel]
  split <;> simp_all

/-- Positive product terminal mass forces terminal-label consumption and a
positive underlying terminal transition. -/
theorem monitorProduct_terminal_pos_iff
    (transientLabel : Fin n → TransientLabel)
    (terminalLabel : Fin m → TerminalLabel)
    (source : Fin n) (terminal : Fin m)
    (monitorSource monitorTarget : Fin q) :
    0 < (C.monitorProduct monitor transientLabel terminalLabel).terminal
        (ProductState.encode (source, monitorSource))
        (ProductState.encode (terminal, monitorTarget)) ↔
      monitorTarget =
          monitor.nextTerminal monitorSource (terminalLabel terminal) ∧
        0 < C.terminal source terminal := by
  rw [C.monitorProduct_terminal_encode monitor transientLabel terminalLabel]
  split <;> simp_all

end Chain

namespace DeterministicMonitor

variable {n q : ℕ}
variable {TransientLabel : Type uT} {TerminalLabel : Type uF}
variable (monitor : DeterministicMonitor q TransientLabel TerminalLabel)

/-- Initial product state.  This is the unique place where the initial
transient label is consumed. -/
def initialProductState
    (transientLabel : Fin n → TransientLabel) (initial : Fin n) :
    Fin (n * q) :=
  ProductState.encode
    (initial, monitor.nextTransient monitor.initial (transientLabel initial))

/-- Decoding the initialized product state exposes the one mandatory initial
label consumption. -/
@[simp]
theorem decode_initialProductState
    (transientLabel : Fin n → TransientLabel) (initial : Fin n) :
    ProductState.decode (monitor.initialProductState transientLabel initial) =
      (initial,
        monitor.nextTransient monitor.initial (transientLabel initial)) := by
  simp [initialProductState]

/-- Acceptance test for an encoded product terminal.  Its monitor coordinate
already includes the terminal label by construction of `monitorProduct`. -/
def acceptsProductTerminal
    {m : ℕ} (terminal : Fin (m * q)) : Bool :=
  monitor.accepting (ProductState.decode terminal).2

@[simp]
theorem acceptsProductTerminal_encode
    {m : ℕ} (terminal : Fin m) (state : Fin q) :
    monitor.acceptsProductTerminal (ProductState.encode (terminal, state)) =
      monitor.accepting state := by
  simp [acceptsProductTerminal]

end DeterministicMonitor

namespace Chain

variable {n m q : ℕ}
variable {TransientLabel : Type uT} {TerminalLabel : Type uF}
variable (C : Chain n m)
variable (monitor : DeterministicMonitor q TransientLabel TerminalLabel)

/-- Product terminal reward is exactly the monitor acceptance indicator after
the terminal label has been consumed. -/
@[simp]
theorem monitorProduct_reward_encode
    (transientLabel : Fin n → TransientLabel)
    (terminalLabel : Fin m → TerminalLabel)
    (terminal : Fin m) (state : Fin q) :
    (C.monitorProduct monitor transientLabel terminalLabel).reward
        (ProductState.encode (terminal, state)) =
      if monitor.accepting state then 1 else 0 := by
  simp [monitorProduct]

/-- Terminal/nontermination law of the monitored product from an original
transient start.  The `none` outcome is actual nontermination, not rejection
by the monitor. -/
def monitoredOutcomeLaw
    (transientLabel : Fin n → TransientLabel)
    (terminalLabel : Fin m → TerminalLabel)
    (initial : Fin n) : FiniteLaw (Option (Fin (m * q))) :=
  (C.monitorProduct monitor transientLabel terminalLabel).outcomeLaw
    (monitor.initialProductState transientLabel initial)

/-- Exact accepted-terminal mass in the checked outcome law of the product.
Nontermination is excluded from acceptance and remains an explicit `none`
atom. -/
def acceptanceProbability
    (transientLabel : Fin n → TransientLabel)
    (terminalLabel : Fin m → TerminalLabel)
    (initial : Fin n) : ℚ≥0 :=
  (C.monitoredOutcomeLaw monitor transientLabel terminalLabel initial).eventMass
    fun outcome => match outcome with
      | some terminal => monitor.acceptsProductTerminal terminal
      | none => false

/-- Exact nontermination mass retained by the monitored outcome law.  Closed
nonterminal classes are therefore valid input and are not silently assigned
to either acceptance or rejection. -/
def monitoredNonterminationProbability
    (transientLabel : Fin n → TransientLabel)
    (terminalLabel : Fin m → TerminalLabel)
    (initial : Fin n) : ℚ≥0 :=
  (C.monitoredOutcomeLaw monitor transientLabel terminalLabel initial).mass none

/-- Raw rational acceptance vector obtained by summing the existing exact
`terminalProbability` solver over accepted product terminals. -/
def acceptanceValue
    (transientLabel : Fin n → TransientLabel)
    (terminalLabel : Fin m → TerminalLabel) : Fin (n * q) → ℚ :=
  let product := C.monitorProduct monitor transientLabel terminalLabel
  fun source =>
    ∑ terminal,
      if monitor.acceptsProductTerminal terminal then
        product.terminalProbability terminal source
      else
        0

/-- Raw acceptance value at the initialized product state. -/
def initialAcceptanceValue
    (transientLabel : Fin n → TransientLabel)
    (terminalLabel : Fin m → TerminalLabel)
    (initial : Fin n) : ℚ :=
  C.acceptanceValue monitor transientLabel terminalLabel
    (monitor.initialProductState transientLabel initial)

/-- Accepted-terminal mass is nonnegative by construction. -/
theorem acceptanceProbability_nonneg
    (transientLabel : Fin n → TransientLabel)
    (terminalLabel : Fin m → TerminalLabel)
    (initial : Fin n) :
    0 ≤ C.acceptanceProbability
      monitor transientLabel terminalLabel initial :=
  bot_le

/-- Accepted-terminal mass is at most one. -/
theorem acceptanceProbability_le_one
    (transientLabel : Fin n → TransientLabel)
    (terminalLabel : Fin m → TerminalLabel)
    (initial : Fin n) :
    C.acceptanceProbability monitor transientLabel terminalLabel initial ≤ 1 :=
  FiniteLaw.eventMass_le_one _ _

/-- Explicit nontermination mass is nonnegative. -/
theorem monitoredNonterminationProbability_nonneg
    (transientLabel : Fin n → TransientLabel)
    (terminalLabel : Fin m → TerminalLabel)
    (initial : Fin n) :
    0 ≤ C.monitoredNonterminationProbability
      monitor transientLabel terminalLabel initial :=
  bot_le

/-- Explicit nontermination mass is at most one. -/
theorem monitoredNonterminationProbability_le_one
    (transientLabel : Fin n → TransientLabel)
    (terminalLabel : Fin m → TerminalLabel)
    (initial : Fin n) :
    C.monitoredNonterminationProbability
        monitor transientLabel terminalLabel initial ≤ 1 := by
  unfold monitoredNonterminationProbability
  exact FiniteLaw.eventMass_le_one _ _

/-- When the executable reachability outcome check succeeds, the checked
accepted mass is exactly the sum of the product chain's raw
`terminalProbability` values.  The general reachability correctness theorem
proves this check succeeds for every normalized chain; it may be applied in a
downstream semantics module without entering this runtime API. -/
theorem coe_acceptanceProbability_eq_initialAcceptanceValue_of_valid
    (transientLabel : Fin n → TransientLabel)
    (terminalLabel : Fin m → TerminalLabel)
    (initial : Fin n)
    (hvalid :
      (C.monitorProduct monitor transientLabel terminalLabel).outcomeWeightsValid
        (monitor.initialProductState transientLabel initial) = true) :
    (C.acceptanceProbability monitor transientLabel terminalLabel initial : ℚ) =
      C.initialAcceptanceValue monitor transientLabel terminalLabel initial := by
  let product := C.monitorProduct monitor transientLabel terminalLabel
  let source := monitor.initialProductState transientLabel initial
  have hv : (∀ terminal, 0 ≤ product.terminalProbability terminal source) ∧
      0 ≤ product.nonterminationProbability source ∧
      (∑ terminal, product.terminalProbability terminal source) +
        product.nonterminationProbability source = 1 := by
    simpa [product, source, outcomeWeightsValid] using hvalid
  simp [acceptanceProbability, monitoredOutcomeLaw,
    initialAcceptanceValue, acceptanceValue,
    outcomeLaw, outcomeLaw?, product, source, hv, FiniteLaw.eventMass]
  rw [List.sum_ofFn]
  change (NNRat.castHom ℚ)
      (∑ terminal, if monitor.acceptsProductTerminal terminal then
        (product.terminalProbability terminal source).toNNRat else 0) =
    ∑ terminal, if monitor.acceptsProductTerminal terminal then
      product.terminalProbability terminal source else 0
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro terminal _
  by_cases haccepts : monitor.acceptsProductTerminal terminal
  · simp [haccepts, Rat.coe_toNNRat _ (hv.1 terminal)]
  · simp [haccepts]

/-- One-step accepted exit value of every product transient state. -/
def acceptanceExitValue
    (transientLabel : Fin n → TransientLabel)
    (terminalLabel : Fin m → TerminalLabel) : Fin (n * q) → ℚ :=
  let product := C.monitorProduct monitor transientLabel terminalLabel
  fun source => ∑ terminal,
    if monitor.acceptsProductTerminal terminal then
      product.R source terminal else 0

private lemma sum_accepting_add {k : ℕ} (accepts : Fin k → Bool)
    (left right : Fin k → ℚ) :
    (∑ terminal, if accepts terminal then left terminal + right terminal else 0) =
      (∑ terminal, if accepts terminal then left terminal else 0) +
        ∑ terminal, if accepts terminal then right terminal else 0 := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro terminal _
  cases accepts terminal <;> simp

private lemma sum_accepting_sum {ι : Type*} {k : ℕ}
    (accepts : Fin k → Bool) (indices : Finset ι) (value : ι → Fin k → ℚ) :
    (∑ terminal, if accepts terminal then ∑ i ∈ indices, value i terminal else 0) =
      ∑ i ∈ indices, ∑ terminal, if accepts terminal then value i terminal else 0 := by
  calc
    _ = ∑ terminal, ∑ i ∈ indices,
        if accepts terminal then value i terminal else 0 := by
      apply Finset.sum_congr rfl
      intro terminal _
      cases accepts terminal <;> simp
    _ = _ := Finset.sum_comm

private lemma sum_accepting_mulVec {k l : ℕ} (accepts : Fin l → Bool)
    (matrix : Matrix (Fin k) (Fin k) ℚ) (value : Fin l → Fin k → ℚ)
    (source : Fin k) :
    (∑ terminal, if accepts terminal then (matrix *ᵥ value terminal) source else 0) =
      ∑ target, matrix source target *
        ∑ terminal, if accepts terminal then value terminal target else 0 := by
  simp only [Matrix.mulVec, dotProduct]
  rw [sum_accepting_sum]
  apply Finset.sum_congr rfl
  intro target _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro terminal _
  cases accepts terminal <;> simp

/-- Linearity turns the existing per-terminal Bellman correctness equations
into the Bellman equation for the monitor acceptance vector.  The downstream
`ReachabilitySemantics` theorem supplies `hbellman` using
`terminalProbability_bellman`; the hypothesis is proof-only and is not part
of execution. -/
theorem acceptanceValue_bellman_of_terminalProbability_bellman
    (transientLabel : Fin n → TransientLabel)
    (terminalLabel : Fin m → TerminalLabel)
    (hbellman : ∀ terminal,
      (C.monitorProduct monitor transientLabel terminalLabel).terminalProbability
          terminal =
        (fun source =>
          (C.monitorProduct monitor transientLabel terminalLabel).R
            source terminal) +
          ((C.monitorProduct monitor transientLabel terminalLabel).Q *ᵥ
            (C.monitorProduct monitor transientLabel terminalLabel).terminalProbability
              terminal)) :
    C.acceptanceValue monitor transientLabel terminalLabel =
      C.acceptanceExitValue monitor transientLabel terminalLabel +
        ((C.monitorProduct monitor transientLabel terminalLabel).Q *ᵥ
          C.acceptanceValue monitor transientLabel terminalLabel) := by
  let product := C.monitorProduct monitor transientLabel terminalLabel
  funext source
  change (∑ terminal,
      if monitor.acceptsProductTerminal terminal then
        product.terminalProbability terminal source else 0) =
    (∑ terminal,
      if monitor.acceptsProductTerminal terminal then
        product.R source terminal else 0) +
      ∑ target, product.Q source target *
        (∑ terminal,
          if monitor.acceptsProductTerminal terminal then
            product.terminalProbability terminal target else 0)
  calc
    (∑ terminal,
        if monitor.acceptsProductTerminal terminal then
          product.terminalProbability terminal source else 0) =
      ∑ terminal,
        if monitor.acceptsProductTerminal terminal then
          (product.R source terminal +
            (product.Q *ᵥ product.terminalProbability terminal) source)
        else 0 := by
          apply Finset.sum_congr rfl
          intro terminal _
          by_cases haccepts : monitor.acceptsProductTerminal terminal
          · simp only [haccepts, if_true]
            exact congrFun (hbellman terminal) source
          · simp [haccepts]
    _ = _ := by
      rw [sum_accepting_add, sum_accepting_mulVec]

/-- Accepted first-hit mass at one exact horizon in the product chain. -/
def acceptanceHit
    (transientLabel : Fin n → TransientLabel)
    (terminalLabel : Fin m → TerminalLabel)
    (horizon : ℕ) (source : Fin (n * q)) : ℚ :=
  let product := C.monitorProduct monitor transientLabel terminalLabel
  ∑ terminal, if monitor.acceptsProductTerminal terminal then
    product.hit horizon source terminal else 0

/-- Eventual accepted mass still transient after a finite horizon.  Closed
nonterminating classes contribute zero here, while remaining explicit in
`monitoredNonterminationProbability`. -/
def acceptanceLate
    (transientLabel : Fin n → TransientLabel)
    (terminalLabel : Fin m → TerminalLabel)
    (horizon : ℕ) (source : Fin (n * q)) : ℚ :=
  let product := C.monitorProduct monitor transientLabel terminalLabel
  ∑ terminal, if monitor.acceptsProductTerminal terminal then
    (product.Q ^ horizon *ᵥ product.terminalProbability terminal) source else 0

/-- Summing the existing specified-terminal finite first-hit correctness
equations gives the monitor's accepted-hits-plus-late decomposition.  The
general theorem `terminalProbability_eq_hits_add_late` supplies `hcorrect` in
the semantics layer. -/
theorem acceptanceValue_eq_hits_add_late_of_terminalProbability_correctness
    (transientLabel : Fin n → TransientLabel)
    (terminalLabel : Fin m → TerminalLabel)
    (horizon : ℕ) (source : Fin (n * q))
    (hcorrect : ∀ terminal,
      let product := C.monitorProduct monitor transientLabel terminalLabel
      product.terminalProbability terminal source =
        (∑ r ∈ Finset.range horizon, product.hit r source terminal) +
          (product.Q ^ horizon *ᵥ product.terminalProbability terminal) source) :
    C.acceptanceValue monitor transientLabel terminalLabel source =
      (∑ r ∈ Finset.range horizon,
        C.acceptanceHit monitor transientLabel terminalLabel r source) +
      C.acceptanceLate monitor transientLabel terminalLabel horizon source := by
  let product := C.monitorProduct monitor transientLabel terminalLabel
  change (∑ terminal, if monitor.acceptsProductTerminal terminal then
      product.terminalProbability terminal source else 0) = _
  change _ = (∑ r ∈ Finset.range horizon,
      ∑ terminal, if monitor.acceptsProductTerminal terminal then
        product.hit r source terminal else 0) +
    ∑ terminal, if monitor.acceptsProductTerminal terminal then
      (product.Q ^ horizon *ᵥ product.terminalProbability terminal) source else 0
  calc
    (∑ terminal, if monitor.acceptsProductTerminal terminal then
        product.terminalProbability terminal source else 0) =
      ∑ terminal, if monitor.acceptsProductTerminal terminal then
        ((∑ r ∈ Finset.range horizon, product.hit r source terminal) +
          (product.Q ^ horizon *ᵥ product.terminalProbability terminal) source)
        else 0 := by
          apply Finset.sum_congr rfl
          intro terminal _
          by_cases haccepts : monitor.acceptsProductTerminal terminal
          · simp only [haccepts, if_true]
            exact hcorrect terminal
          · simp [haccepts]
    _ = _ := by
      rw [sum_accepting_add, sum_accepting_sum]


end Chain

end FiniteMarkovChain
