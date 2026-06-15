/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Data.List.Basic

/-!
# EconCSLib.Algorithm.Online

Online algorithms as deterministic state machines.

## Design

An online algorithm processes a stream of requests one at a time. The
characteristic constraint — *no visibility of the future* — is encoded
structurally: each step depends only on the current state and the current
request. The state summarises whatever the algorithm needs to know about
the past; future requests are inaccessible because there is no syntactic
hook to refer to them.

This is orthogonal to cost accounting (`Foundation.CostM`): online is
about the **information** available to each decision, `CostM` is about
the **resource** consumed. The two can be composed but neither requires
the other.

## Main definitions

* `OnlineAlgorithm Input State Output` — a state machine: an initial
  state and a per-step transition `State → Input → State × Option Output`.
  A step *may or may not* emit an output: emitting an output signals that
  the algorithm has reached its decision and **halts**.
* `OnlineAlgorithm.run` — drive the machine for a *stopping problem*:
  halt at the first step that emits an output, returning the state
  reached and that output (`none` if the inputs were exhausted without
  any output).
* `OnlineAlgorithm.runAll` — drive the machine for a *streaming problem*:
  never halt, instead collect **every** emitted output in arrival order.
* `IsCompetitiveMax`, `IsCompetitiveMin` — `c`-competitiveness against an
  offline optimum, in the maximisation and minimisation directions.

## Design: two ways to drive the same machine

The single transition `step : State → Input → State × Option Output`
supports both shapes of online problem; only the *driver* differs.

* **Stopping problems** — secretary hiring, prophet inequalities, the
  single-item auction — watch the stream and, at one moment, commit to an
  irrevocable decision and stop. Drive these with `run`: the first
  `some o` halts the machine and is the result; a `none` records
  information into the state and waits for the next input.
* **Streaming problems** — online scheduling, bipartite matching,
  paging, ad allocation — emit a decision for (almost) every request and
  run to the end of the stream. Drive these with `runAll`: it never
  halts and gathers every emitted output. A step may still return `none`
  to take no action on a particular request.

## References

* [Borodin, El-Yaniv, *Online Computation and Competitive Analysis*]
-/

namespace Online

/-- A deterministic online algorithm as a state machine.

The state `State` summarises the relevant past; `step` consumes the
current state and the current input to produce the next state together
with an *optional* output — without ever seeing any future input. A step
that emits `some o` halts the run with result `o`; a step that emits
`none` defers, recording what it learned into the next state. -/
structure OnlineAlgorithm (Input State Output : Type*) where
  /-- Initial state, before any input is processed. -/
  init : State
  /-- One-step transition. Depends only on the current state and the
  current input — by construction, the future is invisible. Emitting
  `some o` halts the run; `none` defers to the next input. -/
  step : State → Input → State × Option Output

namespace OnlineAlgorithm

variable {α σ β : Type*}

/-- Drive the machine from an explicit starting state across a list of
inputs, halting at the **first** step that emits an output. Returns the
state reached at that point together with the emitted output, or the
final state and `none` if the inputs are exhausted without any output. -/
def run (alg : OnlineAlgorithm α σ β) : σ → List α → σ × Option β
  | s, []      => (s, none)
  | s, r :: rs =>
      match alg.step s r with
      | (s', some o) => (s', some o)
      | (s', none)   => alg.run s' rs

@[simp] theorem run_nil (alg : OnlineAlgorithm α σ β) (s : σ) :
    alg.run s [] = (s, none) := rfl

theorem run_cons (alg : OnlineAlgorithm α σ β)
    (s : σ) (r : α) (rs : List α) :
    alg.run s (r :: rs) =
      match alg.step s r with
      | (s', some o) => (s', some o)
      | (s', none)   => alg.run s' rs := rfl

/-- If the step on `r` halts with output `o`, the run halts there. -/
@[simp] theorem run_cons_some (alg : OnlineAlgorithm α σ β)
    (s s' : σ) (o : β) (r : α) (rs : List α)
    (h : alg.step s r = (s', some o)) :
    alg.run s (r :: rs) = (s', some o) := by
  rw [run_cons, h]

/-- If the step on `r` defers (`none`), the run continues on `rs`. -/
@[simp] theorem run_cons_none (alg : OnlineAlgorithm α σ β)
    (s s' : σ) (r : α) (rs : List α)
    (h : alg.step s r = (s', none)) :
    alg.run s (r :: rs) = alg.run s' rs := by
  rw [run_cons, h]

/-- Running on `xs ++ ys` where every step on `xs` defers (`none`)
factors through the state reached after `xs`: the prefix produces no
output, so the run continues into `ys` from that state. -/
theorem run_append_of_forall_none (alg : OnlineAlgorithm α σ β)
    (s : σ) (xs ys : List α)
    (h : (alg.run s xs).2 = none) :
    alg.run s (xs ++ ys) = alg.run (alg.run s xs).1 ys := by
  induction xs generalizing s with
  | nil => simp
  | cons r rs ih =>
      cases hstep : alg.step s r with
      | mk s' o =>
          cases o with
          | some o =>
              rw [run_cons_some _ _ _ _ _ _ hstep] at h
              simp at h
          | none =>
              rw [run_cons_none _ _ _ _ _ hstep] at h
              simp only [List.cons_append]
              rw [run_cons_none _ _ _ _ _ hstep,
                  run_cons_none _ _ _ _ _ hstep]
              exact ih s' h

/-- Drive the machine to the **end** of the request list without halting,
collecting every emitted output in arrival order. This is the driver for
*streaming* online problems — scheduling, matching, paging — where the
algorithm acts on each request and never stops early. A step that emits
`none` simply contributes no output for that request. -/
def runAll (alg : OnlineAlgorithm α σ β) : σ → List α → σ × List β
  | s, []      => (s, [])
  | s, r :: rs =>
      match alg.step s r with
      | (s', some o) =>
          let rest := alg.runAll s' rs
          (rest.1, o :: rest.2)
      | (s', none)   => alg.runAll s' rs

@[simp] theorem runAll_nil (alg : OnlineAlgorithm α σ β) (s : σ) :
    alg.runAll s [] = (s, []) := rfl

theorem runAll_cons (alg : OnlineAlgorithm α σ β)
    (s : σ) (r : α) (rs : List α) :
    alg.runAll s (r :: rs) =
      match alg.step s r with
      | (s', some o) =>
          let rest := alg.runAll s' rs
          (rest.1, o :: rest.2)
      | (s', none)   => alg.runAll s' rs := rfl

/-- If the step on `r` emits `o`, `runAll` records it and recurses. -/
@[simp] theorem runAll_cons_some (alg : OnlineAlgorithm α σ β)
    (s s' : σ) (o : β) (r : α) (rs : List α)
    (h : alg.step s r = (s', some o)) :
    alg.runAll s (r :: rs) =
      ((alg.runAll s' rs).1, o :: (alg.runAll s' rs).2) := by
  rw [runAll_cons, h]

/-- If the step on `r` emits nothing, `runAll` recurses unchanged. -/
@[simp] theorem runAll_cons_none (alg : OnlineAlgorithm α σ β)
    (s s' : σ) (r : α) (rs : List α)
    (h : alg.step s r = (s', none)) :
    alg.runAll s (r :: rs) = alg.runAll s' rs := by
  rw [runAll_cons, h]

end OnlineAlgorithm

/-! ### Competitive ratio

For each request sequence the algorithm produces a numerical value of
interest (welfare, throughput, cost, …). The offline optimum `opt` is the
best value achievable with full hindsight. The algorithm is `c`-competitive
if it stays within a factor `c` of `opt`, in either the maximisation or
minimisation direction.

The definitions are deliberately abstract: the caller supplies both
`value` (typically `obj ∘ alg.run alg.init`) and `opt` (the offline
benchmark for the problem at hand). The competitive ratio itself lives in
any ordered multiplicative structure `F`. -/

variable {α F : Type*}

/-- `c`-competitive for a **maximisation** objective: the algorithm's
value on every request sequence is at least `c · opt`. -/
def IsCompetitiveMax [Mul F] [LE F]
    (value opt : List α → F) (c : F) : Prop :=
  ∀ reqs, c * opt reqs ≤ value reqs

/-- `c`-competitive for a **minimisation** objective: the algorithm's
value on every request sequence is at most `c · opt`. -/
def IsCompetitiveMin [Mul F] [LE F]
    (value opt : List α → F) (c : F) : Prop :=
  ∀ reqs, value reqs ≤ c * opt reqs

end Online
