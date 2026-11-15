/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.Foundation.Utility.Lottery
import EconCSLib.MechanismDesign.Auction.VCG
import EconCSLib.OpenProblem.New.SharedConcepts.Adapters
import EconCSLib.OpenProblem.SubmodularWelfareDemandOracle
import EconCSLib.SocialChoice.FairDivision.Divisible.Instance
import EconCSLib.SocialChoice.FairDivision.Indivisible.Instance
import EconCSLib.SocialChoice.FairDivision.Indivisible.MMS
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Combinatorics.Matroid.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Shared mathematical concepts

Imports valuation, welfare, demand, fairness, lottery, and mechanism definitions.
-/
