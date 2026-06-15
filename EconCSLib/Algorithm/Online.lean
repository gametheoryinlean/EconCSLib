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

## Design: the no-input step

The transition `step : State → Option Input → State × Option Output`
receives `some r` for a genuine request and `none` for *end of input*.
The `none` case lets the algorithm act when the stream is exhausted — a
secretary forced to hire the last candidate, an auction posting a final
clearance — rather than silently doing nothing. Both shapes of online
problem are supported; only the *driver* differs.

* **Stopping problems** — secretary hiring, prophet inequalities, the
  single-item auction — watch the stream and, at one moment, commit to an
  irrevocable decision and stop. Drive these with `run`: the first
  `some o` halts the machine and is the result; a `none` records
  information into the state and waits for the next input. When the inputs
  run out without a decision, one last `step _ none` is taken.
* **Streaming problems** — online scheduling, bipartite matching,
  paging, ad allocation — emit a decision for (almost) every request and
  run to the end of the stream. Drive these with `runAll`: it never
  halts and gathers every emitted output, including a possible final
  output from the end-of-input step.

`scan` / `scanState` are the clean halt-first **core** that processes only
the genuine requests (no end-of-input step); `run` / `runState` are `scan`
followed by the terminal `step _ none`. Keeping the two layers apart lets
the core retain its clean concatenation algebra (`scan_append_*`).

## References

* [Borodin, El-Yaniv, *Online Computation and Competitive Analysis*]
-/

namespace Online

/-- A deterministic online algorithm as a state machine.

The state `State` summarises the relevant past; `step` consumes the
current state and the current input to produce the next state together
with an *optional* output — without ever seeing any future input. The
input is `Option Input`: `some r` is a genuine request, `none` signals
*end of input*, the algorithm's chance to act when the stream is
exhausted. A step that emits `some o` halts the run with result `o`; a
step that emits `none` defers, recording what it learned into the next
state. -/
structure OnlineAlgorithm (Input State Output : Type*) where
  /-- Initial state, before any input is processed. -/
  init : State
  /-- One-step transition. Depends only on the current state and the
  current input — by construction, the future is invisible. The input is
  `some r` for a request and `none` for end of input. Emitting `some o`
  halts the run; `none` defers. -/
  step : State → Option Input → State × Option Output

namespace OnlineAlgorithm

variable {α σ β : Type*}

/-! ### Core: `scan` over the genuine requests

`scan` processes only the real inputs (each fed as `some r`), halting at
the first emitted output. It performs **no** end-of-input step, which is
exactly what gives it a clean concatenation algebra. `run` / `runState`
below add the terminal `step _ none`. -/

/-- Scan the genuine requests, halting at the **first** emitted output.
No end-of-input step is taken. -/
def scan (alg : OnlineAlgorithm α σ β) : σ → List α → Option β
  | _, []      => none
  | s, r :: rs =>
      match alg.step s (some r) with
      | (_,  some o) => some o
      | (s', none)   => alg.scan s' rs

@[simp] theorem scan_nil (alg : OnlineAlgorithm α σ β) (s : σ) :
    alg.scan s [] = none := rfl

theorem scan_cons (alg : OnlineAlgorithm α σ β)
    (s : σ) (r : α) (rs : List α) :
    alg.scan s (r :: rs) =
      match alg.step s (some r) with
      | (_,  some o) => some o
      | (s', none)   => alg.scan s' rs := rfl

/-- If the step on `r` halts with output `o`, the scan yields `o`. -/
@[simp] theorem scan_cons_some (alg : OnlineAlgorithm α σ β)
    (s s' : σ) (o : β) (r : α) (rs : List α)
    (h : alg.step s (some r) = (s', some o)) :
    alg.scan s (r :: rs) = some o := by
  rw [scan_cons, h]

/-- If the step on `r` defers (`none`), the scan continues on `rs`. -/
@[simp] theorem scan_cons_none (alg : OnlineAlgorithm α σ β)
    (s s' : σ) (r : α) (rs : List α)
    (h : alg.step s (some r) = (s', none)) :
    alg.scan s (r :: rs) = alg.scan s' rs := by
  rw [scan_cons, h]

/-- The state reached when the scan halts: the post-step state at the
first emitting request, or the state after the last request if none
emitted. The bookkeeping companion to `scan`. -/
def scanState (alg : OnlineAlgorithm α σ β) : σ → List α → σ
  | s, []      => s
  | s, r :: rs =>
      match alg.step s (some r) with
      | (s', some _) => s'
      | (s', none)   => alg.scanState s' rs

@[simp] theorem scanState_nil (alg : OnlineAlgorithm α σ β) (s : σ) :
    alg.scanState s [] = s := rfl

theorem scanState_cons (alg : OnlineAlgorithm α σ β)
    (s : σ) (r : α) (rs : List α) :
    alg.scanState s (r :: rs) =
      match alg.step s (some r) with
      | (s', some _) => s'
      | (s', none)   => alg.scanState s' rs := rfl

/-- If the step on `r` halts (emits an output), the halting state is the
post-step state `s'`; the rest is not processed. -/
@[simp] theorem scanState_cons_some (alg : OnlineAlgorithm α σ β)
    (s s' : σ) (o : β) (r : α) (rs : List α)
    (h : alg.step s (some r) = (s', some o)) :
    alg.scanState s (r :: rs) = s' := by
  rw [scanState_cons, h]

/-- If the step on `r` defers (`none`), the scan continues on `rs`. -/
@[simp] theorem scanState_cons_none (alg : OnlineAlgorithm α σ β)
    (s s' : σ) (r : α) (rs : List α)
    (h : alg.step s (some r) = (s', none)) :
    alg.scanState s (r :: rs) = alg.scanState s' rs := by
  rw [scanState_cons, h]

/-- Scanning `xs ++ ys` where every request in `xs` defers (`none`)
factors through the state reached after `xs`. -/
theorem scan_append_of_forall_none (alg : OnlineAlgorithm α σ β)
    (s : σ) (xs ys : List α)
    (h : alg.scan s xs = none) :
    alg.scan s (xs ++ ys) = alg.scan (alg.scanState s xs) ys := by
  induction xs generalizing s with
  | nil => simp
  | cons r rs ih =>
      cases hstep : alg.step s (some r) with
      | mk s' o =>
          cases o with
          | some o =>
              rw [scan_cons_some _ _ _ _ _ _ hstep] at h
              simp at h
          | none =>
              rw [scan_cons_none _ _ _ _ _ hstep] at h
              simp only [List.cons_append]
              rw [scan_cons_none _ _ _ _ _ hstep,
                  scanState_cons_none _ _ _ _ _ hstep]
              exact ih s' h

/-- State version of `scan_append_of_forall_none`. -/
theorem scanState_append_of_forall_none (alg : OnlineAlgorithm α σ β)
    (s : σ) (xs ys : List α)
    (h : alg.scan s xs = none) :
    alg.scanState s (xs ++ ys) = alg.scanState (alg.scanState s xs) ys := by
  induction xs generalizing s with
  | nil => simp
  | cons r rs ih =>
      cases hstep : alg.step s (some r) with
      | mk s' o =>
          cases o with
          | some o =>
              rw [scan_cons_some _ _ _ _ _ _ hstep] at h
              simp at h
          | none =>
              rw [scan_cons_none _ _ _ _ _ hstep] at h
              simp only [List.cons_append]
              rw [scanState_cons_none _ _ _ _ _ hstep,
                  scanState_cons_none _ _ _ _ _ hstep]
              exact ih s' h

/-- If the prefix `xs` already emits an output, the halting state over
`xs ++ ys` is reached within `xs`: the suffix is never processed. -/
theorem scanState_append_of_scan_isSome (alg : OnlineAlgorithm α σ β)
    (s : σ) (xs ys : List α)
    (h : (alg.scan s xs).isSome) :
    alg.scanState s (xs ++ ys) = alg.scanState s xs := by
  induction xs generalizing s with
  | nil => simp at h
  | cons r rs ih =>
      cases hstep : alg.step s (some r) with
      | mk s' o =>
          cases o with
          | some o =>
              rw [scanState_cons _ _ _ _, hstep]
              simp only [List.cons_append]
              rw [scanState_cons _ _ _ _, hstep]
          | none =>
              rw [scan_cons_none _ _ _ _ _ hstep] at h
              simp only [List.cons_append]
              rw [scanState_cons_none _ _ _ _ _ hstep,
                  scanState_cons_none _ _ _ _ _ hstep]
              exact ih s' h

/-! ### Drivers: `run` / `runState` / `runAll`

These wrap the core with the terminal end-of-input step `step _ none`. -/

/-- The observable result of a **stopping** run: the first output emitted
while scanning the requests, or — if the requests are exhausted without a
decision — the output of the end-of-input step `step _ none`. -/
def run (alg : OnlineAlgorithm α σ β) (s : σ) (rs : List α) : Option β :=
  match alg.scan s rs with
  | some o => some o
  | none   => (alg.step (alg.scanState s rs) none).2

/-- The halting state of `run`: the scan's halting state if it emitted,
otherwise the state after the end-of-input step. -/
def runState (alg : OnlineAlgorithm α σ β) (s : σ) (rs : List α) : σ :=
  match alg.scan s rs with
  | some _ => alg.scanState s rs
  | none   => (alg.step (alg.scanState s rs) none).1

/-- On no requests, `run` is exactly the end-of-input step's output. -/
@[simp] theorem run_nil (alg : OnlineAlgorithm α σ β) (s : σ) :
    alg.run s [] = (alg.step s none).2 := rfl

/-- On no requests, `runState` is the end-of-input step's state. -/
@[simp] theorem runState_nil (alg : OnlineAlgorithm α σ β) (s : σ) :
    alg.runState s [] = (alg.step s none).1 := rfl

/-- Drive the machine to the **end** of the request list without halting,
collecting every emitted output in arrival order, including a possible
final output from the end-of-input step. The driver for *streaming*
problems — scheduling, matching, paging. -/
def runAll (alg : OnlineAlgorithm α σ β) : σ → List α → List β
  | s, []      =>
      match (alg.step s none).2 with
      | some o => [o]
      | none   => []
  | s, r :: rs =>
      match alg.step s (some r) with
      | (s', some o) => o :: alg.runAll s' rs
      | (s', none)   => alg.runAll s' rs

theorem runAll_cons (alg : OnlineAlgorithm α σ β)
    (s : σ) (r : α) (rs : List α) :
    alg.runAll s (r :: rs) =
      match alg.step s (some r) with
      | (s', some o) => o :: alg.runAll s' rs
      | (s', none)   => alg.runAll s' rs := rfl

/-- If the step on `r` emits `o`, `runAll` records it and recurses. -/
@[simp] theorem runAll_cons_some (alg : OnlineAlgorithm α σ β)
    (s s' : σ) (o : β) (r : α) (rs : List α)
    (h : alg.step s (some r) = (s', some o)) :
    alg.runAll s (r :: rs) = o :: alg.runAll s' rs := by
  rw [runAll_cons, h]

/-- If the step on `r` emits nothing, `runAll` recurses unchanged. -/
@[simp] theorem runAll_cons_none (alg : OnlineAlgorithm α σ β)
    (s s' : σ) (r : α) (rs : List α)
    (h : alg.step s (some r) = (s', none)) :
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
