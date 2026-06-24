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
  halt at the first step that emits an output, returning the pair
  `(terminal state, result)`; the result is `none` if the inputs were
  exhausted and the end-of-input step also declined. The terminal state is
  read as `(run …).1`, the decision as `(run …).2`.
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

`run` returns a pair: `(run …).1` is the **terminal** state (after the
end-of-input step) and `(run …).2` is the decision. Compositional facts
about splitting a request stream — needed e.g. to isolate one bidder —
are proved per instance from `run_cons_some` / `run_cons_none`; for the
single-item auction the end-of-input step preserves the state, which keeps
those splitting lemmas clean.

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

/-- Drive the machine across the requests, halting at the **first** step
that emits an output. When the genuine requests are exhausted without a
commitment, the machine is given the **end-of-input** step `step _ none` —
its last chance to decide, since it never knew which request was last — and
its `(state, output)` pair *is* the result. So `(run s rs).1` is the
terminal state and `(run s rs).2` is the decision. -/
def run (alg : OnlineAlgorithm α σ β) : σ → List α → σ × Option β
  | s, []      => alg.step s none
  | s, r :: rs =>
      match alg.step s (some r) with
      | (s', some o) => (s', some o)
      | (s', none)   => alg.run s' rs

/-- On no requests, `run` is exactly the end-of-input step. -/
@[simp] theorem run_nil (alg : OnlineAlgorithm α σ β) (s : σ) :
    alg.run s [] = alg.step s none := rfl

theorem run_cons (alg : OnlineAlgorithm α σ β)
    (s : σ) (r : α) (rs : List α) :
    alg.run s (r :: rs) =
      match alg.step s (some r) with
      | (s', some o) => (s', some o)
      | (s', none)   => alg.run s' rs := rfl

/-- If the step on `r` halts with output `o`, the run halts there. -/
@[simp] theorem run_cons_some (alg : OnlineAlgorithm α σ β)
    (s s' : σ) (o : β) (r : α) (rs : List α)
    (h : alg.step s (some r) = (s', some o)) :
    alg.run s (r :: rs) = (s', some o) := by
  rw [run_cons, h]

/-- If the step on `r` defers (`none`), the run continues on `rs`. -/
@[simp] theorem run_cons_none (alg : OnlineAlgorithm α σ β)
    (s s' : σ) (r : α) (rs : List α)
    (h : alg.step s (some r) = (s', none)) :
    alg.run s (r :: rs) = alg.run s' rs := by
  rw [run_cons, h]

/-- The **decision** `run` commits to — the second component of `run`. -/
abbrev runResult (alg : OnlineAlgorithm α σ β) (s : σ) (rs : List α) : Option β :=
  (alg.run s rs).2

/-- The **terminal status** (state) `run` halts in — the first component of
`run`, after the end-of-input step. -/
abbrev runStatus (alg : OnlineAlgorithm α σ β) (s : σ) (rs : List α) : σ :=
  (alg.run s rs).1

/-! ### Streaming

`runAll` never halts: it gathers every emitted output in arrival order,
including a possible final output from the end-of-input step. The driver
for streaming problems — scheduling, matching, paging. -/

/-- Collect every emitted output across the requests in order, plus a final
output from the end-of-input step if it emits one. -/
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
