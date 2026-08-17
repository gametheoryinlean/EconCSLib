/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.OpenProblem.EconCSBench.Common
import Mathlib.Analysis.SpecialFunctions.Exp

namespace EconCSLib.OpenProblem.EconCSBench.SubmodularWelfareDemandOracle

/-- One demand query specifies an agent and a nonnegative-unrestricted item
price vector. -/
structure SWMDemandQuery
    (Agent : Type*) {Good : Type*} (M : Finset Good) where
  agent : Agent
  price : BundlePriceVector M
  price_nonnegative : ∀ g, 0 ≤ price g

/-- A demand oracle returns one bundle for every demand query. -/
abbrev SWMDemandOracle
    (Agent : Type*) {Good : Type*} (M : Finset Good) :=
  SWMDemandQuery Agent M → BundleAllocation M

/-- Oracle answers really maximize the queried agent's quasi-linear utility.
All maximizing tie-breaks are admitted. -/
def IsValidSWMDemandOracle
    {Agent Good : Type*} [DecidableEq Good] {M : Finset Good}
    (valuation : Agent → SubmodularBundleValuation M)
    (oracle : SWMDemandOracle Agent M) : Prop :=
  ∀ query,
    IsDemandBundle (valuation query.agent).val query.price M (oracle query)

/-- Canonical exact-real RAM representation of a demand query.  Agents and
goods are represented by their fixed finite enumerations, followed by one
exact real word for each item price. -/
noncomputable def encodeSWMDemandQuery
    {Agent Good : Type*} [Fintype Agent] [DecidableEq Good]
    {M : Finset Good} (query : SWMDemandQuery Agent M) :
    List EconCSLib.OpenProblem.UnitCostRAM.Word :=
  .integer (Int.ofNat ((Fintype.equivFin Agent) query.agent).val) ::
    List.ofFn fun index : Fin M.card =>
      .real (query.price (M.equivFin.symm index))

/-- Canonical membership-vector representation of a bundle. -/
noncomputable def encodeSWMBundle
    {Good : Type*} [DecidableEq Good] (M : Finset Good)
    (bundle : BundleAllocation M) :
    List EconCSLib.OpenProblem.UnitCostRAM.Word :=
  List.ofFn fun index : Fin M.card =>
    .bit (decide ((M.equivFin.symm index).1 ∈ bundle.1))

/-- Canonical item-membership matrix representing an allocation.  Rows follow
the fixed enumeration of agents and columns the fixed enumeration of `M`. -/
noncomputable def encodeSWMAllocation
    {Agent Good : Type*} [Fintype Agent] [DecidableEq Good]
    (M : Finset Good) (allocation : BundlePartitionAllocation Agent M) :
    List EconCSLib.OpenProblem.UnitCostRAM.Word :=
  (List.ofFn fun index : Fin (Fintype.card Agent) =>
    encodeSWMBundle M
      (allocation.1 ((Fintype.equivFin Agent).symm index))).flatten

/-- A length-`randomBits` Boolean tape.  The final statement equips this finite
type with its canonical uniform lottery, so no arbitrary real-valued seed
weights can carry nonuniform advice. -/
abbrev SWMRandomTape (randomBits : ℕ) := Fin randomBits → Bool

/-- The structural machine input consists only of the two instance
dimensions.  Valuations and random bits enter solely through the fixed machine
environment. -/
def encodeSWMProgramInput
    (Agent : Type*) [Fintype Agent]
    {Good : Type*} (M : Finset Good) :
    List EconCSLib.OpenProblem.UnitCostRAM.Word :=
  [.integer (Int.ofNat (Fintype.card Agent)),
    .integer (Int.ofNat M.card)]

/-- The fixed external semantics of the only machine operation.  A word list
is accepted precisely when it is the canonical encoding of a legal
nonnegative-price demand query; the result is the canonical bundle returned by
the supplied oracle.  Malformed calls return the empty word list and reveal no
valuation information. -/
noncomputable def swmDemandEnvironment
    {Agent Good : Type*} [Fintype Agent] [DecidableEq Good]
    {M : Finset Good} (randomBits : ℕ) (tape : SWMRandomTape randomBits)
    (oracle : SWMDemandOracle Agent M) :
    EconCSLib.OpenProblem.UnitCostRAM.MachineEnvironment Unit := by
  classical
  exact
    { external := fun _ words =>
        if h : ∃ query : SWMDemandQuery Agent M,
            encodeSWMDemandQuery query = words then
          encodeSWMBundle M (oracle (Classical.choose h))
        else
          []
      randomTape := fun cursor =>
        if h : cursor < randomBits then tape ⟨cursor, h⟩ else false }

/-- A demand-only program may use ordinary RAM instructions and external
`call`s, but not the separate distribution-sampling instruction.  Since the
external-operation type is `Unit`, every `call` has exactly the demand-oracle
semantics fixed by `swmDemandEnvironment`. -/
def IsDemandOnlySWMInstruction :
    EconCSLib.OpenProblem.UnitCostRAM.Instruction Unit → Prop
  | .sample _ _ _ _ _ => False
  | _ => True

/-- Every instruction of a finite program belongs to the demand-only syntax. -/
def IsDemandOnlySWMProgram
    (program : EconCSLib.OpenProblem.UnitCostRAM.Program Unit) : Prop :=
  ∀ (pc : ℕ) instruction, program.code[pc]? = some instruction →
    IsDemandOnlySWMInstruction instruction

/-- Run the finite instruction-level algorithm on one uniform random tape and
one demand oracle.  Time, demand calls, and consumed random bits below are all
generated by this execution. -/
noncomputable def runSWMProgram
    {Agent Good : Type*} [Fintype Agent] [DecidableEq Good]
    {M : Finset Good}
    (program : EconCSLib.OpenProblem.UnitCostRAM.Program Unit)
    {randomBits : ℕ} (fuel : ℕ) (tape : SWMRandomTape randomBits)
    (oracle : SWMDemandOracle Agent M) :=
  EconCSLib.OpenProblem.UnitCostRAM.run
    (swmDemandEnvironment randomBits tape oracle) program fuel
    (encodeSWMProgramInput Agent M)

/-- A randomized demand-only SWM algorithm is realized by one finite RAM
program reading a bounded Boolean random tape through interpreter
`randomBit` instructions.  Its mathematical allocation is tied to the exact
canonical output of the same execution for every tape and every oracle
tie-breaking rule. -/
structure RandomizedDemandOnlySWMAlgorithm
    (Agent : Type*) {Good : Type*}
    [Fintype Agent] [DecidableEq Good] (M : Finset Good) (randomBits : ℕ)
    (program : EconCSLib.OpenProblem.UnitCostRAM.Program Unit) where
  allocation : SWMRandomTape randomBits → SWMDemandOracle Agent M →
    BundlePartitionAllocation Agent M
  fuel : SWMRandomTape randomBits → SWMDemandOracle Agent M → ℕ
  correct : ∀ tape oracle,
    ∃ finalState,
      (runSWMProgram program (fuel tape oracle) tape oracle).ret =
        .halted (encodeSWMAllocation M (allocation tape oracle)) finalState

/-- The declared uniform-tape length, actual instruction count, actual number
of external `call` instructions, actual number of `randomBit` instructions,
and peak RAM space obey one fixed polynomial in the number of agents and
goods.  Space includes the program's static registers, encoded input words,
and interpreter-generated peak allocated cells.  All execution bounds are
uniform over tapes and oracle answers. -/
def RandomizedDemandOnlySWMAlgorithm.HasResourceBound
    {Agent Good : Type*} [Fintype Agent] [DecidableEq Good]
    {M : Finset Good}
    {randomBits : ℕ}
    {program : EconCSLib.OpenProblem.UnitCostRAM.Program Unit}
    (algorithm :
      RandomizedDemandOnlySWMAlgorithm Agent M randomBits program)
    (coefficient exponent : ℕ) : Prop :=
  let size := Fintype.card Agent + M.card
  let sizeOf : SWMRandomTape randomBits → ℕ :=
    fun _ => Fintype.card Agent + M.card
  randomBits ≤ coefficient * (size + 1) ^ exponent ∧
    UniformResourceBound coefficient exponent sizeOf
      (fun tape oracle =>
        EconCSLib.OpenProblem.UnitCostRAM.ProfiledCost.steps
          (runSWMProgram program (algorithm.fuel tape oracle) tape oracle)) ∧
    UniformResourceBound coefficient exponent sizeOf
      (fun tape oracle =>
        EconCSLib.OpenProblem.UnitCostRAM.ProfiledCost.oracleQueries
          (runSWMProgram program (algorithm.fuel tape oracle) tape oracle)) ∧
    UniformResourceBound coefficient exponent sizeOf
      (fun tape oracle =>
        EconCSLib.OpenProblem.UnitCostRAM.ProfiledCost.randomBits
          (runSWMProgram program (algorithm.fuel tape oracle) tape oracle)) ∧
    UniformResourceBound coefficient exponent sizeOf
      (fun tape oracle =>
        program.registerCount + (encodeSWMProgramInput Agent M).length +
          EconCSLib.OpenProblem.UnitCostRAM.ProfiledCost.peakCells
            (runSWMProgram program (algorithm.fuel tape oracle) tape oracle))

/-- Expected welfare for a fixed valid demand oracle. -/
noncomputable def RandomizedDemandOnlySWMAlgorithm.expectedWelfare
    {Agent Good : Type*} [Fintype Agent] [DecidableEq Good]
    {M : Finset Good}
    {randomBits : ℕ}
    {program : EconCSLib.OpenProblem.UnitCostRAM.Program Unit}
    (algorithm :
      RandomizedDemandOnlySWMAlgorithm Agent M randomBits program)
    (valuation : Agent → SubmodularBundleValuation M)
    (oracle : SWMDemandOracle Agent M) : ℝ :=
  Lottery.expectedValue (uniformLottery (SWMRandomTape randomBits)) fun tape =>
    bundleSocialWelfare (fun i => (valuation i).val)
      (algorithm.allocation tape oracle)

/-- Open-problem statement with the requested explicit `+0.01` improvement.
The guarantee holds for every valid demand-oracle tie-breaking rule. -/
noncomputable def DemandOracleSWMPointZeroOneStatement : Prop :=
  ∃ coefficient exponent : ℕ,
    ∃ program : EconCSLib.OpenProblem.UnitCostRAM.Program Unit,
      IsDemandOnlySWMProgram program ∧
      ∀ (Agent Good : Type) [Fintype Agent] [DecidableEq Agent]
          [Nonempty Agent] [DecidableEq Good] (M : Finset Good),
        ∃ algorithm :
          RandomizedDemandOnlySWMAlgorithm Agent M
            (coefficient *
              (Fintype.card Agent + M.card + 1) ^ exponent)
            program,
          algorithm.HasResourceBound coefficient exponent ∧
          ∀ valuation : Agent → SubmodularBundleValuation M,
            (∃ oracle : SWMDemandOracle Agent M,
              IsValidSWMDemandOracle valuation oracle) ∧
            ∀ oracle : SWMDemandOracle Agent M,
                IsValidSWMDemandOracle valuation oracle →
                  (∀ tape,
                    IsCompleteBundleAllocation
                      (algorithm.allocation tape oracle)) ∧
                  (1 - 1 / Real.exp 1 + 1 / 100 : ℝ) *
                        bundleOPT (fun i => (valuation i).val) ≤
                      algorithm.expectedWelfare valuation oracle

/-- English version: "Is there a polynomial-time, polynomial-demand-query SWM
algorithm with approximation at least `1 - 1/e + 0.01`?" -/
theorem demandOracleSWMPointZeroOne :
    answer(sorry) ↔ DemandOracleSWMPointZeroOneStatement := by
  sorry

end EconCSLib.OpenProblem.EconCSBench.SubmodularWelfareDemandOracle
