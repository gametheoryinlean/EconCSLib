/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.GameForm.IndexedContinuation
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Uniform approximation and limit Nash on declared roots

This module isolates the analytic hypothesis needed to pass exact finite
Nash inequalities on declared continuation roots to an infinite payoff. The
approximation error is uniform over every root, player, and unilateral
deviation from the candidate profile and must tend to zero.

`IndexedContinuationGameForm` is representation-neutral and cannot certify
whether its root predicate is a lawful subgame system. Consequently no
standard-SPE claim is made here and no unconditional finite-to-infinite
implication is asserted.
-/

open Filter

namespace IndexedContinuationGameForm

universe uN uS uH uR uO

variable {N : Type uN}

/-- Nash optimality on every declared root, stated directly for a real-valued
continuation payoff functional.

This is useful when finite and infinite evaluators have different outcome
representations but share roots and strategies. It becomes an SPE predicate
only after a representation-aware caller supplies a lawful subgame system as
the root predicate. -/
def IsNashOnRootsForPayoff [DecidableEq N]
    (G : IndexedContinuationGameForm N)
    (payoff : G.Root → G.Profile → N → ℝ)
    (profile : G.Profile) : Prop :=
  ∀ root, G.IsDeclaredRoot root →
    ∀ i deviation,
      payoff root (Function.update profile i deviation) i ≤
        payoff root profile i

/-- A uniform error certificate over every admissible root, player, and
unilateral deviation from one candidate profile. -/
def UniformDeviationConvergenceAt [DecidableEq N]
    (G : IndexedContinuationGameForm N)
    (finitePayoff : ℕ → G.Root → G.Profile → N → ℝ)
    (infinitePayoff : G.Root → G.Profile → N → ℝ)
    (profile : G.Profile)
    (error : ℕ → ℝ) : Prop :=
  (∀ n, 0 ≤ error n) ∧
  Tendsto error atTop (nhds 0) ∧
  ∀ n root i deviation,
    abs (finitePayoff n root profile i -
        infinitePayoff root profile i) ≤ error n ∧
      abs (finitePayoff n root
          (Function.update profile i deviation) i -
        infinitePayoff root
          (Function.update profile i deviation) i) ≤ error n

private lemma tendsto_of_abs_sub_le_error {payoff error : ℕ → ℝ} {value : ℝ}
    (herror : Tendsto error atTop (nhds 0))
    (hbound : ∀ n, |payoff n - value| ≤ error n) :
    Tendsto payoff atTop (nhds value) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  exact squeeze_zero (fun _ => dist_nonneg)
    (fun n => by simpa [Real.dist_eq] using hbound n) herror

/-- Exact finite-index Nash on declared roots passes to the infinite payoff
when approximation errors vanish uniformly over all roots, players, and
unilateral deviations. -/
theorem isNashOnRootsForInfinitePayoff_of_uniformDeviationConvergence
    [DecidableEq N]
    (G : IndexedContinuationGameForm N)
    (finitePayoff : ℕ → G.Root → G.Profile → N → ℝ)
    (infinitePayoff : G.Root → G.Profile → N → ℝ)
    (profile : G.Profile)
    (error : ℕ → ℝ)
    (huniform :
      G.UniformDeviationConvergenceAt
        finitePayoff infinitePayoff profile error)
    (hfinite :
      ∀ n, G.IsNashOnRootsForPayoff (finitePayoff n) profile) :
    G.IsNashOnRootsForPayoff infinitePayoff profile := by
  intro root hroot i deviation
  have hbase := tendsto_of_abs_sub_le_error huniform.2.1
    (fun n => (huniform.2.2 n root i deviation).1)
  have hdeviation := tendsto_of_abs_sub_le_error huniform.2.1
    (fun n => (huniform.2.2 n root i deviation).2)
  exact
    le_of_tendsto_of_tendsto'
      hdeviation hbase
      (fun n => hfinite n root hroot i deviation)

end IndexedContinuationGameForm
