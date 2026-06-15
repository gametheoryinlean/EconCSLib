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

/-! ### Driving the machine over the genuine requests

`run` processes only the genuine requests (each fed as `some r`), halting
at the **first** emitted output. It performs **no** end-of-input step:
`step _ none` is exposed separately as `finalize`, to be invoked
explicitly by algorithms that must commit a decision once the stream is
exhausted (secretary hiring, prophet inequalities). Keeping the
end-of-input action out of `run` is what gives `run` a clean concatenation
law (`run_append_of_forall_none`) and makes `runState` the true
"mid-stream" state — the state *before* the next genuine request, with no
spurious terminal step. -/

/-- Drive the machine across the genuine requests, halting at the **first**
step that emits an output. The observable result is that output: `some o`
if some request triggered the decision `o`, or `none` if the requests were
exhausted without a commitment. Use `runState` for the halting state and
`finalize` to take the end-of-input step. -/
def run (alg : OnlineAlgorithm α σ β) : σ → List α → Option β
  | _, []      => none
  | s, r :: rs =>
      match alg.step s (some r) with
      | (_,  some o) => some o
      | (s', none)   => alg.run s' rs

@[simp] theorem run_nil (alg : OnlineAlgorithm α σ β) (s : σ) :
    alg.run s [] = none := rfl

theorem run_cons (alg : OnlineAlgorithm α σ β)
    (s : σ) (r : α) (rs : List α) :
    alg.run s (r :: rs) =
      match alg.step s (some r) with
      | (_,  some o) => some o
      | (s', none)   => alg.run s' rs := rfl

/-- If the step on `r` halts with output `o`, the run yields `o`. -/
@[simp] theorem run_cons_some (alg : OnlineAlgorithm α σ β)
    (s s' : σ) (o : β) (r : α) (rs : List α)
    (h : alg.step s (some r) = (s', some o)) :
    alg.run s (r :: rs) = some o := by
  rw [run_cons, h]

/-- If the step on `r` defers (`none`), the run continues on `rs`. -/
@[simp] theorem run_cons_none (alg : OnlineAlgorithm α σ β)
    (s s' : σ) (r : α) (rs : List α)
    (h : alg.step s (some r) = (s', none)) :
    alg.run s (r :: rs) = alg.run s' rs := by
  rw [run_cons, h]

/-- The state reached when `run` halts: the post-step state at the first
emitting request, or the state after the last request if none emitted. The
bookkeeping companion to `run`. -/
def runState (alg : OnlineAlgorithm α σ β) : σ → List α → σ
  | s, []      => s
  | s, r :: rs =>
      match alg.step s (some r) with
      | (s', some _) => s'
      | (s', none)   => alg.runState s' rs

@[simp] theorem runState_nil (alg : OnlineAlgorithm α σ β) (s : σ) :
    alg.runState s [] = s := rfl

theorem runState_cons (alg : OnlineAlgorithm α σ β)
    (s : σ) (r : α) (rs : List α) :
    alg.runState s (r :: rs) =
      match alg.step s (some r) with
      | (s', some _) => s'
      | (s', none)   => alg.runState s' rs := rfl

/-- If the step on `r` halts (emits an output), the halting state is the
post-step state `s'`; the rest is not processed. -/
@[simp] theorem runState_cons_some (alg : OnlineAlgorithm α σ β)
    (s s' : σ) (o : β) (r : α) (rs : List α)
    (h : alg.step s (some r) = (s', some o)) :
    alg.runState s (r :: rs) = s' := by
  rw [runState_cons, h]

/-- If the step on `r` defers (`none`), the run continues on `rs`. -/
@[simp] theorem runState_cons_none (alg : OnlineAlgorithm α σ β)
    (s s' : σ) (r : α) (rs : List α)
    (h : alg.step s (some r) = (s', none)) :
    alg.runState s (r :: rs) = alg.runState s' rs := by
  rw [runState_cons, h]

/-- Running on `xs ++ ys` where every request in `xs` defers (`none`)
factors through the state reached after `xs`: the prefix produces no
output, so the run continues into `ys` from that state. -/
theorem run_append_of_forall_none (alg : OnlineAlgorithm α σ β)
    (s : σ) (xs ys : List α)
    (h : alg.run s xs = none) :
    alg.run s (xs ++ ys) = alg.run (alg.runState s xs) ys := by
  induction xs generalizing s with
  | nil => simp
  | cons r rs ih =>
      cases hstep : alg.step s (some r) with
      | mk s' o =>
          cases o with
          | some o =>
              rw [run_cons_some _ _ _ _ _ _ hstep] at h
              simp at h
          | none =>
              rw [run_cons_none _ _ _ _ _ hstep] at h
              simp only [List.cons_append]
              rw [run_cons_none _ _ _ _ _ hstep,
                  runState_cons_none _ _ _ _ _ hstep]
              exact ih s' h

/-- State version of `run_append_of_forall_none`. -/
theorem runState_append_of_forall_none (alg : OnlineAlgorithm α σ β)
    (s : σ) (xs ys : List α)
    (h : alg.run s xs = none) :
    alg.runState s (xs ++ ys) = alg.runState (alg.runState s xs) ys := by
  induction xs generalizing s with
  | nil => simp
  | cons r rs ih =>
      cases hstep : alg.step s (some r) with
      | mk s' o =>
          cases o with
          | some o =>
              rw [run_cons_some _ _ _ _ _ _ hstep] at h
              simp at h
          | none =>
              rw [run_cons_none _ _ _ _ _ hstep] at h
              simp only [List.cons_append]
              rw [runState_cons_none _ _ _ _ _ hstep,
                  runState_cons_none _ _ _ _ _ hstep]
              exact ih s' h

/-- If the prefix `xs` already emits an output, the halting state over
`xs ++ ys` is reached within `xs`: the suffix is never processed. -/
theorem runState_append_of_run_isSome (alg : OnlineAlgorithm α σ β)
    (s : σ) (xs ys : List α)
    (h : (alg.run s xs).isSome) :
    alg.runState s (xs ++ ys) = alg.runState s xs := by
  induction xs generalizing s with
  | nil => simp at h
  | cons r rs ih =>
      cases hstep : alg.step s (some r) with
      | mk s' o =>
          cases o with
          | some o =>
              rw [runState_cons _ _ _ _, hstep]
              simp only [List.cons_append]
              rw [runState_cons _ _ _ _, hstep]
          | none =>
              rw [run_cons_none _ _ _ _ _ hstep] at h
              simp only [List.cons_append]
              rw [runState_cons_none _ _ _ _ _ hstep,
                  runState_cons_none _ _ _ _ _ hstep]
              exact ih s' h

/-! ### End of input

`finalize` is the one-shot end-of-input step: when the stream is
exhausted, the algorithm is given a final `step _ none` to commit a
decision it could not make earlier (it never knew which request was last).
This is opt-in — `run` itself never takes it — so stopping problems that
have no forced final decision (e.g. the single-item auction: no clearing
bid simply means no sale) ignore it entirely. -/

/-- The end-of-input output: the algorithm's final decision when the stream
is exhausted. -/
def finalize (alg : OnlineAlgorithm α σ β) (s : σ) : Option β :=
  (alg.step s none).2

/-- The state after the end-of-input step. -/
def finalizeState (alg : OnlineAlgorithm α σ β) (s : σ) : σ :=
  (alg.step s none).1

/-- Run to the end, then force a decision via the end-of-input step if no
output was emitted while scanning the requests. The driver for stopping
problems that must commit by the end of the stream (secretary hiring). -/
def runOrFinalize (alg : OnlineAlgorithm α σ β) (s : σ) (rs : List α) : Option β :=
  (alg.run s rs).orElse (fun _ => alg.finalize (alg.runState s rs))

/-! ### Streaming

`runAll` never halts: it gathers every emitted output in arrival order.
The driver for streaming problems — scheduling, matching, paging. Like
`run`, it processes only genuine requests; an algorithm that also wants a
final output at end of stream appends `finalize`. -/

/-- Collect every emitted output across the genuine requests, in order. -/
def runAll (alg : OnlineAlgorithm α σ β) : σ → List α → List β
  | _, []      => []
  | s, r :: rs =>
      match alg.step s (some r) with
      | (s', some o) => o :: alg.runAll s' rs
      | (s', none)   => alg.runAll s' rs

@[simp] theorem runAll_nil (alg : OnlineAlgorithm α σ β) (s : σ) :
    alg.runAll s [] = [] := rfl

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
