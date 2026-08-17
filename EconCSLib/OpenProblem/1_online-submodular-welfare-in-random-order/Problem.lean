/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.OpenProblem.EconCSBench.Common

namespace EconCSLib.OpenProblem.EconCSBench.OnlineSubmodularWelfare

/-- Items revealed through time `t` in an arrival order. -/
def revealedPrefix {items : ℕ}
    (order : Equiv.Perm (Fin items)) (t : Fin items) : Finset (Fin items) :=
  (Finset.univ.filter fun s => s ≤ t).image order

/-- Two valuation/order inputs give exactly the same oracle information on
bundles contained in the revealed prefix. -/
def SameSubmodularHistory
    {agents items : ℕ}
    (v v' : Fin agents →
      SubmodularBundleValuation (Finset.univ : Finset (Fin items)))
  (order order' : Equiv.Perm (Fin items)) (t : Fin items) : Prop :=
  (∀ s, s ≤ t → order s = order' s) ∧
  ∀ i : Fin agents,
    ∀ S : BundleAllocation (Finset.univ : Finset (Fin items)),
      S.1 ⊆ revealedPrefix order t → (v i).val S = (v' i).val S

noncomputable instance onlineAllocationFintype
    (agents items : ℕ) :
    Fintype
      (BundlePartitionAllocation (Fin agents)
        (Finset.univ : Finset (Fin items))) := by
  classical
  unfold BundlePartitionAllocation
  infer_instance

/-- Probability of a complete prefix-assignment profile under a randomized
allocation law. -/
noncomputable def prefixAssignmentProbability
    {agents items : ℕ}
    (L : Lottery ℝ
      (BundlePartitionAllocation (Fin agents)
        (Finset.univ : Finset (Fin items))))
    (seen : Finset (Fin items))
    (assignmentProfile : Fin agents → Finset (Fin items)) : ℝ :=
  ∑ A, L.val A *
    if (∀ i, (A.1 i).1 ∩ seen = assignmentProfile i) then 1 else 0

/-- A randomized online allocation algorithm in the random-order model.
Randomness is represented directly by the output law, avoiding an additional
finite global seed-space assumption not present in the Markdown. -/
structure RandomOrderSubmodularAlgorithm
    (agents items : ℕ) where
  /-- Allocation distribution for a valuation profile and arrival order. -/
  outcome :
    (Fin agents → SubmodularBundleValuation (Finset.univ : Finset (Fin items))) →
      Equiv.Perm (Fin items) →
        Lottery ℝ
          (BundlePartitionAllocation (Fin agents)
            (Finset.univ : Finset (Fin items)))
  /-- Every allocation in the support assigns every item exactly once. -/
  complete :
    ∀ v order A, 0 < (outcome v order).val A →
      IsCompleteBundleAllocation A
  /-- Immediate irrevocable assignment: the joint law of all assignments in a
  revealed prefix depends only on the information revealed in that prefix. -/
  online :
    ∀ v v' order order' t,
      SameSubmodularHistory v v' order order' t →
        ∀ assignmentProfile,
          prefixAssignmentProbability (outcome v order)
              (revealedPrefix order t) assignmentProfile =
            prefixAssignmentProbability (outcome v' order')
              (revealedPrefix order' t) assignmentProfile

/-- Expected welfare over the uniformly random arrival order and internal
randomness. -/
noncomputable def expectedOnlineWelfare
    {agents items : ℕ}
    (algorithm : RandomOrderSubmodularAlgorithm agents items)
    (v : Fin agents →
      SubmodularBundleValuation (Finset.univ : Finset (Fin items))) : ℝ :=
  Lottery.expectedValue (uniformLottery (Equiv.Perm (Fin items))) fun order =>
    Lottery.expectedValue (algorithm.outcome v order) fun A =>
      bundleSocialWelfare (fun i => (v i).val) A

/-- Open-problem statement: a random-order online algorithm guarantees
`0.51` of offline optimal submodular welfare. -/
def RandomOrderSubmodularPointFiveOneStatement : Prop :=
  ∀ agents items : ℕ, 0 < agents → 0 < items →
    ∃ algorithm : RandomOrderSubmodularAlgorithm agents items,
      ∀ v : Fin agents →
          SubmodularBundleValuation (Finset.univ : Finset (Fin items)),
        (51 / 100 : ℝ) * bundleOPT (fun i => (v i).val) ≤
          expectedOnlineWelfare algorithm v

/-- English version: "Is there a random-order online submodular-welfare
algorithm with competitive ratio at least 0.51?" -/
theorem randomOrderSubmodularPointFiveOne :
    answer(sorry) ↔ RandomOrderSubmodularPointFiveOneStatement := by
  sorry

end EconCSLib.OpenProblem.EconCSBench.OnlineSubmodularWelfare
