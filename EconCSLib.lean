/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

-- EconCSLib: stable aggregate import

-- Foundation: abstract vocabulary
import EconCSLib.Foundation.Player
import EconCSLib.Foundation.Preference
import EconCSLib.Foundation.Profile
import EconCSLib.Foundation.Argmax
import EconCSLib.Foundation.OrderedGroup
import EconCSLib.Foundation.CostM
import EconCSLib.Foundation.CostM.Cells
import EconCSLib.Foundation.CostM.Visited

-- Foundation/Utility: utility theory (vNM, lotteries, affine transforms)
import EconCSLib.Foundation.Utility.Basic
import EconCSLib.Foundation.Utility.AffineTransform
import EconCSLib.Foundation.Utility.Lottery
import EconCSLib.Foundation.Utility.VNMAxioms

-- Math: infrastructure with no game vocabulary
import EconCSLib.Math.Simplex

-- Math/LinearAlgebra
import EconCSLib.Math.LinearAlgebra.FourierMotzkin
import EconCSLib.Math.LinearAlgebra.Farkas
import EconCSLib.Math.LinearAlgebra.PerronFrobenius

-- Math/LinearProgramming
import EconCSLib.Math.LinearProgramming.StrongDuality
import EconCSLib.Math.LinearProgramming.StrongComplementarity

-- Math/FixedPoint
import EconCSLib.Math.FixedPoint.Scarf
import EconCSLib.Math.FixedPoint.Brouwer
import EconCSLib.Math.FixedPoint.Brouwer_product
import EconCSLib.Math.FixedPoint.KKM

-- Math/Minimax
import EconCSLib.Math.Minimax.MinimaxLoomis
import EconCSLib.Math.Minimax.Loomis
import EconCSLib.Math.Minimax.SkewSymmetric
import EconCSLib.Math.Minimax.Minimax

-- GameTheory/StrategicGame
import EconCSLib.GameTheory.StrategicGame.Basic
import EconCSLib.GameTheory.StrategicGame.BestResponse
import EconCSLib.GameTheory.StrategicGame.Dominance
import EconCSLib.GameTheory.StrategicGame.NashEquilibrium
import EconCSLib.GameTheory.StrategicGame.Checker
import EconCSLib.GameTheory.StrategicGame.PotentialGame
import EconCSLib.GameTheory.StrategicGame.ESS
import EconCSLib.GameTheory.StrategicGame.IESDS
import EconCSLib.GameTheory.StrategicGame.CorrelatedEq
import EconCSLib.GameTheory.StrategicGame.MixedStrategy
import EconCSLib.GameTheory.StrategicGame.Nash

-- GameTheory/StrategicGame/ZeroSum
import EconCSLib.GameTheory.StrategicGame.ZeroSum.Basic
import EconCSLib.GameTheory.StrategicGame.ZeroSum.MatrixGame
import EconCSLib.GameTheory.StrategicGame.ZeroSum.MatrixGameNash
import EconCSLib.GameTheory.StrategicGame.ZeroSum.OptimalStrategySetPolytope
import EconCSLib.GameTheory.StrategicGame.ZeroSum.StrongComplementarity
import EconCSLib.GameTheory.StrategicGame.ZeroSum.StochasticMatrix
import EconCSLib.GameTheory.StrategicGame.ZeroSum.Antisymmetric

-- GameTheory/StrategicGame/ZeroSum/Learning
import EconCSLib.GameTheory.StrategicGame.ZeroSum.Learning.FictitiousPlay
import EconCSLib.GameTheory.StrategicGame.ZeroSum.Learning.Robinson
import EconCSLib.GameTheory.StrategicGame.ZeroSum.Learning.Cesaro

-- GameTheory/ExtensiveGame (Arena-based, supports infinite games)
import EconCSLib.GameTheory.ExtensiveGame.Basic
import EconCSLib.GameTheory.ExtensiveGame.Strategy
import EconCSLib.GameTheory.ExtensiveGame.Play
import EconCSLib.GameTheory.ExtensiveGame.Subgame
import EconCSLib.GameTheory.ExtensiveGame.BehaviorStrategy
-- Finite perfect-information games (inductive GameTree, Kuhn + Zermelo)
import EconCSLib.GameTheory.ExtensiveGame.GameTree
import EconCSLib.GameTheory.ExtensiveGame.BackwardInduction
import EconCSLib.GameTheory.ExtensiveGame.GameTreeSPE
import EconCSLib.GameTheory.ExtensiveGame.GameTreeNE
import EconCSLib.GameTheory.ExtensiveGame.GameTreeStrategicForm
import EconCSLib.GameTheory.ExtensiveGame.FiniteArenaExtraction
import EconCSLib.GameTheory.ExtensiveGame.StochasticGameTree
import EconCSLib.GameTheory.ExtensiveGame.ImperfectInformation
import EconCSLib.GameTheory.ExtensiveGame.Zermelo
import EconCSLib.GameTheory.ExtensiveGame.ZeroSumGameTreeWithChance

-- GameTheory/CoalitionalGame
import EconCSLib.GameTheory.CoalitionalGame.Basic
import EconCSLib.GameTheory.CoalitionalGame.Core
import EconCSLib.GameTheory.CoalitionalGame.ShapleyValue

-- Social choice
import EconCSLib.SocialChoice.Basic
import EconCSLib.SocialChoice.Voting.Basic
import EconCSLib.SocialChoice.Voting.Arrow
import EconCSLib.SocialChoice.Voting.Decisive
import EconCSLib.SocialChoice.Voting.VotingRules
import EconCSLib.SocialChoice.Voting.ProfileSurgery
import EconCSLib.SocialChoice.Voting.GibbardSatterthwaite

-- MarketDesign/Matching
import EconCSLib.MarketDesign.Matching.Basic
import EconCSLib.MarketDesign.Matching.GaleShapley
import EconCSLib.MarketDesign.Matching.Optimal
import EconCSLib.MarketDesign.Matching.RuralHospitals
import EconCSLib.MarketDesign.Matching.Lattice

-- MechanismDesign/Auction
import EconCSLib.MechanismDesign.Auction.MechBasic
import EconCSLib.MechanismDesign.Auction.Transfer
import EconCSLib.MechanismDesign.Auction.MechBayesian
import EconCSLib.MechanismDesign.Auction.VCG
import EconCSLib.MechanismDesign.Auction.Myerson
import EconCSLib.MechanismDesign.Auction.AuctionBasic
import EconCSLib.MechanismDesign.Auction.BayesianSingleItem
import EconCSLib.MechanismDesign.Auction.Knapsack
import EconCSLib.MechanismDesign.Auction.Vickrey
import EconCSLib.MechanismDesign.Auction.ReserveVickrey
import EconCSLib.MechanismDesign.Auction.FirstPrice
import EconCSLib.MechanismDesign.Auction.OptimalSingleItem

-- Fair division
import EconCSLib.SocialChoice.FairDivision.Basic
import EconCSLib.SocialChoice.FairDivision.Cardinal
import EconCSLib.SocialChoice.FairDivision.Fairness
import EconCSLib.SocialChoice.FairDivision.Welfare
import EconCSLib.SocialChoice.FairDivision.Indivisible.Basic
import EconCSLib.SocialChoice.FairDivision.Indivisible.Instance
import EconCSLib.SocialChoice.FairDivision.Indivisible.Valuation
import EconCSLib.SocialChoice.FairDivision.Indivisible.Fairness
import EconCSLib.SocialChoice.FairDivision.Indivisible.Efficiency
import EconCSLib.SocialChoice.FairDivision.Indivisible.SocialWelfare
import EconCSLib.SocialChoice.FairDivision.Indivisible.Checker
import EconCSLib.SocialChoice.FairDivision.Indivisible.ImpossibilityEF
import EconCSLib.SocialChoice.FairDivision.Indivisible.Implications
import EconCSLib.SocialChoice.FairDivision.Indivisible.EFX
import EconCSLib.SocialChoice.FairDivision.Indivisible.RoundRobin
import EconCSLib.SocialChoice.FairDivision.Indivisible.EnvyCycle
import EconCSLib.SocialChoice.FairDivision.Indivisible.MMS
import EconCSLib.SocialChoice.FairDivision.Divisible.Allocation
import EconCSLib.SocialChoice.FairDivision.Divisible.Valuation
import EconCSLib.SocialChoice.FairDivision.Divisible.Basic
import EconCSLib.SocialChoice.FairDivision.Divisible.Instance
import EconCSLib.SocialChoice.FairDivision.Divisible.UnitInterval
import EconCSLib.SocialChoice.FairDivision.Divisible.EnvyFree
import EconCSLib.SocialChoice.FairDivision.Divisible.CutAndChoose
import EconCSLib.SocialChoice.FairDivision.Divisible.DubinsSpanier
import EconCSLib.SocialChoice.FairDivision.Divisible.Existence

/-!
# EconCSLib

Stable aggregate import for the EconCSLib Lean library. Worked examples and
experimental open-problem interfaces remain available as opt-in imports.
-/
