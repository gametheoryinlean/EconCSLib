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
  state and a per-step transition `State → Input → State × Output`.
* `OnlineAlgorithm.run` — drive the machine from an explicit starting
  state over a finite request list, returning the final state and the
  list of outputs in arrival order.
* `IsCompetitiveMax`, `IsCompetitiveMin` — `c`-competitiveness against an
  offline optimum, in the maximisation and minimisation directions.

## References

* [Borodin, El-Yaniv, *Online Computation and Competitive Analysis*]
-/

namespace Online

/-- A deterministic online algorithm as a state machine.

The state `State` summarises the relevant past; `step` consumes the
current state and the current input to produce the next state together
with the output for this input — without ever seeing any future input. -/
structure OnlineAlgorithm (Input State Output : Type*) where
  /-- Initial state, before any input is processed. -/
  init : State
  /-- One-step transition. Depends only on the current state and the
  current input — by construction, the future is invisible. -/
  step : State → Input → State × Output

namespace OnlineAlgorithm

variable {α σ β : Type*}

/-- Drive the machine from an explicit starting state across a list of
inputs, returning the final state and the outputs in arrival order. -/
def run (alg : OnlineAlgorithm α σ β) : σ → List α → σ × List β
  | s, []      => (s, [])
  | s, r :: rs =>
      let sa   := alg.step s r
      let rest := alg.run sa.1 rs
      (rest.1, sa.2 :: rest.2)

@[simp] theorem run_nil (alg : OnlineAlgorithm α σ β) (s : σ) :
    alg.run s [] = (s, []) := rfl

@[simp] theorem run_cons (alg : OnlineAlgorithm α σ β)
    (s : σ) (r : α) (rs : List α) :
    alg.run s (r :: rs) =
      let sa   := alg.step s r
      let rest := alg.run sa.1 rs
      (rest.1, sa.2 :: rest.2) := rfl

/-- Running on `xs ++ ys` factors through the state reached after `xs`. -/
theorem run_append (alg : OnlineAlgorithm α σ β) (s : σ) (xs ys : List α) :
    alg.run s (xs ++ ys) =
      let mid  := alg.run s xs
      let tail := alg.run mid.1 ys
      (tail.1, mid.2 ++ tail.2) := by
  induction xs generalizing s with
  | nil => simp
  | cons r rs ih =>
      simp only [List.cons_append, run_cons]
      simp [ih]

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
