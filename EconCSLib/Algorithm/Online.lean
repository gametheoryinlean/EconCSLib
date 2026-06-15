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
  exhausted and the end-of-input step also declined.
* `OnlineAlgorithm.runState` — the *resume* state: the state reached by
  the genuine requests, with no end-of-input step. The right notion for
  compositional reasoning (splitting a stream at an interior point).
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
end-of-input step) and `(run …).2` is the decision.
`runState` is the **resume** state — the genuine requests only, *no*
end-of-input step. The two differ exactly by that final `step _ none` and
coincide when it preserves the state. The resume state is what carries a
clean concatenation law (`runState_append_of_forall_none`), needed when a
request stream is split at an interior point (e.g. isolating one bidder).

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

/-! ### Resume state

`runState` is the **resume** state: the state reached by feeding the
genuine requests, halting at the first emitted output, with **no**
end-of-input step. It is the state *before the next genuine request*, the
right notion for compositional reasoning — splitting a request stream at an
interior point, where the stream is *not* ending. It differs from
`(run …).state` only by the final `step _ none`; the two coincide whenever
that end-of-input step preserves the state. -/

/-- The resume state: scan the genuine requests, halting at the first
emitting one, taking **no** end-of-input step. -/
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

/-- If the step on `r` halts (emits an output), the resume state is the
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

/-- Running on `xs ++ ys` where the scan of `xs` emits nothing factors
through the resume state after `xs`: the prefix produces no output, so the
run resumes into `ys` from that state. -/
theorem runState_append_of_forall_none (alg : OnlineAlgorithm α σ β)
    (s : σ) (xs ys : List α)
    (h : (alg.run s xs).2 = none) :
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
