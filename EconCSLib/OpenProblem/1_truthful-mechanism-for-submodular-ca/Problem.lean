/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.OpenProblem.EconCSBench.Common

namespace EconCSLib.OpenProblem.EconCSBench.TruthfulSubmodularCA

/-- Value extractor for reported submodular valuations. -/
def submodularReportedValue
    {G : Type*} [DecidableEq G] {M : Finset G}
    (v : SubmodularBundleValuation M) : BundleAllocation M → ℝ :=
  v.val

/-- A demand query names a bidder and a nonnegative item-price vector. -/
structure MechanismDemandQuery
    (Bidder : Type*) {Good : Type*} (M : Finset Good) where
  bidder : Bidder
  price : BundlePriceVector M
  price_nonnegative : ∀ g, 0 ≤ price g

/-- The bidder-independent part of a demand query.  A demand oracle for one
reported valuation sees only this price vector, not the other bidders'
reports. -/
structure ValuationDemandQuery
    {Good : Type*} (M : Finset Good) where
  price : BundlePriceVector M
  price_nonnegative : ∀ g, 0 ≤ price g

/-- A demand oracle supplies one utility-maximizing bundle per query. -/
abbrev MechanismDemandOracle
    (Bidder : Type*) {Good : Type*} (M : Finset Good) :=
  MechanismDemandQuery Bidder M → BundleAllocation M

/-- A fixed demand-oracle implementation for each reported valuation.  Its
tie-breaking may depend on the valuation and price, but not on the rest of a
report profile. -/
abbrev ValuationDemandOracle
    {Good : Type*} (M : Finset Good) :=
  ValuationDemandQuery M → BundleAllocation M

/-- Semantic validity of a family containing one fixed oracle for every
bidder and reported valuation.  Different bidders may use different legal
tie-breaking rules even when their reported value functions coincide. -/
def IsValidBidderValuationDemandOracleFamily
    {Bidder Good : Type*} [DecidableEq Good] {M : Finset Good}
    (oracleFor :
      Bidder → SubmodularBundleValuation M →
        ValuationDemandOracle M) : Prop :=
  ∀ bidder valuation query,
    IsDemandBundle valuation.val query.price M
      (oracleFor bidder valuation query)

/-- Turn valuation-indexed fixed demand oracles into the bidder-indexed oracle
seen by a query program at one report profile. -/
def profileDemandOracle
    {Bidder Good : Type*} [DecidableEq Good] {M : Finset Good}
    (reports : Bidder → SubmodularBundleValuation M)
    (oracleFor :
      Bidder → SubmodularBundleValuation M →
        ValuationDemandOracle M) :
    MechanismDemandOracle Bidder M :=
  fun query =>
    oracleFor query.bidder (reports query.bidder)
      { price := query.price, price_nonnegative := query.price_nonnegative }

/-- A finite adaptive demand-query program whose leaf contains both the
allocation and the payments of one deterministic mechanism component. -/
inductive DemandMechanismQueryTree
    (Bidder : Type*) {Good : Type*} [DecidableEq Good] (M : Finset Good)
  | output
      (allocation : BundlePartitionAllocation Bidder M)
      (payment : Bidder → ℝ)
  | query (question : MechanismDemandQuery Bidder M)
      (next : BundleAllocation M → DemandMechanismQueryTree Bidder M)
      (localCost : BundleAllocation M → ℕ)

/-- Run a demand-query mechanism against an oracle. -/
def DemandMechanismQueryTree.run
    {Bidder Good : Type*} [DecidableEq Good] {M : Finset Good}
    (tree : DemandMechanismQueryTree Bidder M)
    (oracle : MechanismDemandOracle Bidder M) :
    BundlePartitionAllocation Bidder M × (Bidder → ℝ) :=
  match tree with
  | .output allocation payment => (allocation, payment)
  | .query question next _ => (next (oracle question)).run oracle

/-- Actual number of demand queries along one oracle-answer path. -/
def DemandMechanismQueryTree.queryCount
    {Bidder Good : Type*} [DecidableEq Good] {M : Finset Good}
    (tree : DemandMechanismQueryTree Bidder M)
    (oracle : MechanismDemandOracle Bidder M) : ℕ :=
  match tree with
  | .output _ _ => 0
  | .query question next _ =>
      1 + (next (oracle question)).queryCount oracle

/-- Unit-cost path length including the annotated local work used to choose
each continuation. -/
def DemandMechanismQueryTree.timeCost
    {Bidder Good : Type*} [DecidableEq Good] {M : Finset Good}
    (tree : DemandMechanismQueryTree Bidder M)
    (oracle : MechanismDemandOracle Bidder M) : ℕ :=
  match tree with
  | .output _ _ => 1
  | .query question next localCost =>
      let answer := oracle question
      1 + localCost answer + (next answer).timeCost oracle

/-- The deterministic direct mechanism induced by one query program and one
fixed legal demand-oracle tie-breaking rule. -/
def demandProgramMechanism
    {Bidder Good : Type*} [DecidableEq Good] {M : Finset Good}
    (program : DemandMechanismQueryTree Bidder M)
    (oracleFor :
      Bidder → SubmodularBundleValuation M →
        ValuationDemandOracle M) :
    DeterministicBundleMechanism
      Bidder (SubmodularBundleValuation M) M where
  allocation := fun reports =>
    (program.run (profileDemandOracle reports oracleFor)).1
  payment := fun reports =>
    (program.run (profileDemandOracle reports oracleFor)).2

/-- A universally truthful demand-query program that is robust to the demand
oracle's legal tie-breaking.  The public randomization and adaptive programs
are fixed before an oracle implementation is chosen. -/
structure DemandImplementableTruthfulMechanism
    (Bidder Seed : Type*) {Good : Type*}
    [Fintype Bidder] [DecidableEq Bidder] [Fintype Seed]
    [DecidableEq Good] (M : Finset Good) where
  /-- Public random seed distribution. -/
  seedDist : Lottery ℝ Seed
  /-- One adaptive oracle program for every realization of the public coins. -/
  program : Seed → DemandMechanismQueryTree Bidder M
  /-- Each deterministic component is DSIC under every fixed legal family of
  demand-oracle tie-breaking rules. -/
  truthful :
    ∀ oracleFor,
      IsValidBidderValuationDemandOracleFamily oracleFor →
        ∀ seed,
          (demandProgramMechanism (program seed) oracleFor).IsDSIC
            submodularReportedValue
  /-- The advertised allocation is a partition of all items. -/
  complete :
    ∀ oracleFor,
      IsValidBidderValuationDemandOracleFamily oracleFor →
        ∀ seed reports,
          IsCompleteBundleAllocation
            ((program seed).run
              (profileDemandOracle reports oracleFor)).1

/-- Expected welfare under one fixed legal demand-oracle implementation. -/
noncomputable def DemandImplementableTruthfulMechanism.expectedWelfare
    {Bidder Seed Good : Type*}
    [Fintype Bidder] [DecidableEq Bidder] [Fintype Seed]
    [DecidableEq Good] {M : Finset Good}
    (mechanism : DemandImplementableTruthfulMechanism Bidder Seed M)
    (oracleFor :
      Bidder → SubmodularBundleValuation M →
        ValuationDemandOracle M)
    (reports : Bidder → SubmodularBundleValuation M) : ℝ :=
  Lottery.expectedValue mechanism.seedDist fun seed =>
    bundleSocialWelfare (fun i => (reports i).val)
      ((mechanism.program seed).run
        (profileDemandOracle reports oracleFor)).1

/-- One fixed polynomial demand-query bound attached to the actual adaptive
programs, uniformly over seeds, reports, and legal oracle tie-breaking. -/
def DemandImplementableTruthfulMechanism.UsesDemandQueryBound
    {Bidder Seed Good : Type*}
    [Fintype Bidder] [DecidableEq Bidder] [Fintype Seed]
    [DecidableEq Good] {M : Finset Good}
    (mechanism :
      DemandImplementableTruthfulMechanism Bidder Seed M)
    (coefficient exponent : ℕ) : Prop :=
  let Input := Seed × (Bidder → SubmodularBundleValuation M)
  let OracleFamily :=
    Bidder → SubmodularBundleValuation M → ValuationDemandOracle M
  UniformResourceBoundOn coefficient exponent
    (fun (_ : Input) (oracleFor : OracleFamily) =>
      IsValidBidderValuationDemandOracleFamily oracleFor)
    (fun _ : Input => Fintype.card Bidder + M.card)
    (fun input oracleFor =>
      (mechanism.program input.1).queryCount
        (profileDemandOracle input.2 oracleFor))

/-- Open-problem statement: a universally truthful mechanism achieves an
`O(log log m)` approximation using polynomially many demand queries. -/
noncomputable def TruthfulSubmodularLogLogStatement : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ cutoff : ℕ,
    ∃ coefficient exponent : ℕ,
      ∀ (Bidder Good : Type) [Fintype Bidder] [DecidableEq Bidder]
        [Nonempty Bidder] [DecidableEq Good] (M : Finset Good),
        cutoff ≤ M.card →
          ∃ seeds : ℕ,
            ∃ mechanism :
              DemandImplementableTruthfulMechanism
                Bidder (Fin (seeds + 1)) M,
              mechanism.UsesDemandQueryBound coefficient exponent ∧
              ∀ oracleFor,
                IsValidBidderValuationDemandOracleFamily oracleFor →
                  ∀ reports : Bidder → SubmodularBundleValuation M,
                    bundleOPT (fun i => (reports i).val) ≤
                      (C * Real.log (Real.log M.card)) *
                        mechanism.expectedWelfare oracleFor reports

/-- English version: "Is there a universally truthful, polynomial-demand-query
`O(log log m)` approximation for submodular combinatorial auctions?" -/
theorem truthfulSubmodularLogLog :
    answer(sorry) ↔ TruthfulSubmodularLogLogStatement := by
  sorry

end EconCSLib.OpenProblem.EconCSBench.TruthfulSubmodularCA
