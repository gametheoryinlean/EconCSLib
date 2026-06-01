/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.MechanismDesign.Auction.Transfer
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Order.Interval.Set.Defs

/-!
# EconCSLib.MechanismDesign.Auction.AuctionBasic

Basic auction and mechanism definitions used across the library.

This is the base layer for `EconCSLib/MechanismDesign/Auction`. It provides:

- abstract auction formats: `SingleItemAuction`, `CombinatorialAuction`,
  and the transfer-layer `SingleParameterMechanism`
- generic predicates such as feasibility, monotonicity, DSIC, and
  implementability
- ordered-bid helper constructions such as `Auction.maxBid` and
  `Auction.argmaxBid`

Myerson-specific payment formulas and proofs are in
`EconCSLib/MechanismDesign/Auction/Myerson.lean`.

## Auction format hierarchy

Different auction formats arise by specializing the report/type space,
allocation space, and payment space:

```
MechanismWithTransfers I T A P                     -- general transfer mechanism
  ├─ SingleItemAuction I V P                        -- T i = V, A = Option I
  └─ SingleParameterMechanism I R                   -- T i = R, A = I → R, P = R

MultipleParameterMechanism I A V P                  -- T i = A → V
  └─ CombinatorialAuction I k V P                   -- A = CombinatorialAllocation I k
```

## Main definitions

### Auction formats
* `SingleItemAuction` — one indivisible item; allocation is `Option I` (winner or no sale)
* `CombinatorialAuction` — `k` distinct items; allocation assigns item bundles per agent
* `SingleParameterMechanism` — Myerson's single-parameter setting, defined in
  `MechanismDesign.Auction.Transfer`

### Predicates on auction formats
* `CombinatorialAuction.IsFeasible` — no item allocated to two agents
* `SingleParameterMechanism.IsAllocFeasible` — allocations lie in `[0, 1]`
* `SingleParameterMechanism.IsMonotone` — allocation is non-decreasing in each agent's
  reported type (Myerson's necessary condition for DSIC)

### Bid-profile support predicates (`Auction.BidProfile`)
* `Auction.BidProfile.Nonnegative` — every bid is nonnegative
* `Auction.BidProfile.InSet` — each bid lies in a per-agent admissible set
* `Auction.BidProfile.InBox` — each bid lies in a per-agent closed interval
* `Auction.BidProfile.StrategyMapsBoxToBox` — a strategy maps one bid box into another
* `Auction.BidProfile.inBox_iff_inSet_Icc` — `InBox` ↔ `InSet` with `Set.Icc`

### Ordered-bid utilities
The following are mathematical tools for auction rules that rank bids.
**They do not define any specific auction's winner** — each concrete auction specifies
its own allocation rule, which may or may not select the highest bidder.

* `Auction.maxBid` — the highest bid in a profile
* `Auction.argmaxBid` — the bidder with the highest bid
* `Auction.maxBidExcluding` — the highest bid excluding a given bidder

## References

* [Nisan et al., *Algorithmic Game Theory*, Ch. 9, 11]
* [Maschler, Solan, Zamir, *Game Theory*, Ch. 11–12]
-/

/-! ## Abstract auction formats -/

/-- A single-item auction.

  One indivisible item is for sale. Each agent reports a scalar bid of type `V`.
  The allocation is `Option I`:
  - `some i` — bidder `i` receives the item
  - `none` — the item is withheld (reserve price not met, etc.)

  Which bidder wins, or whether anyone wins, is determined by the allocation rule
  of the specific mechanism. This structure imposes no winner-selection policy. -/
structure SingleItemAuction (I : Type*) (V : Type*) (P : Type*)
    extends MechanismWithTransfers I (fun _ => V) (Option I) P

/-- A multi-item auction with `k` distinct items.

  An agent bundle is a finite subset of the `k` items, represented as
  `Finset (Fin k)`. A full allocation assigns one bundle to each agent. Agents
  report valuation functions over full allocation profiles, so this is the
  specialization of `MultipleParameterMechanism` to bundle allocations.

  Feasibility (no item sold twice) is a separate predicate; see `IsFeasible`. -/
def MultiItemBundle (k : ℕ) := Finset (Fin k)

namespace MultiItemBundle

/-- View a named multi-item bundle as the underlying finite set of item indices. -/
def toFinset {k : ℕ} (bundle : MultiItemBundle k) : Finset (Fin k) :=
  bundle

end MultiItemBundle

/-- A multi-item allocation assigns each agent a bundle of items. -/
def CombinatorialAllocation (I : Type*) (k : ℕ) := I → MultiItemBundle k

/-- A combinatorial auction with `k` distinct items.

  This is a multiple-parameter mechanism whose allocation space is the type of
  bundle-allocation profiles `I → Finset (Fin k)`. Each agent reports a valuation
  over those allocation profiles. -/
structure CombinatorialAuction (I : Type*) (k : ℕ) (V : Type*) (P : Type*)
    extends MultipleParameterMechanism I (CombinatorialAllocation I k) V P

namespace CombinatorialAuction

/-- Feasibility: each item is allocated to at most one agent. -/
def IsFeasible {I : Type*} {k : ℕ} {V P : Type*}
    (M : CombinatorialAuction I k V P) : Prop :=
  ∀ (b : ∀ _ : I, MultipleParameterMechanism.Valuation (CombinatorialAllocation I k) V)
    (i j : I), i ≠ j →
    ∀ item : Fin k,
      item ∈ MultiItemBundle.toFinset (M.allocationRule b i) →
      item ∉ MultiItemBundle.toFinset (M.allocationRule b j)

end CombinatorialAuction

/-! ## Bid-profile support predicates

Side conditions on bid profiles that constrain the admissible bid space without
modifying the underlying auction format.  Useful for bounded-support equilibrium
arguments and strategy-set restrictions in Bayesian auction theory.

[Krishna, Ch. 2-3]; [AGT, Ch. 9, §9.3-9.5] -/

namespace Auction.BidProfile

variable {I V : Type*}

/-- Every bid is nonnegative.

  $\forall i.\; b_i \ge 0$.  Captures the standard private-value convention that
  bids represent willingness-to-pay. -/
def Nonnegative [Zero V] [LE V] (b : I → V) : Prop :=
  ∀ i, 0 ≤ b i

/-- Each bid lies in the per-agent admissible set.

  For a family of strategy sets $S_i \subseteq V$, asserts $\forall i.\; b_i \in S_i$.
  Captures heterogeneous strategy spaces. -/
def InSet (b : I → V) (S : I → Set V) : Prop :=
  ∀ i, b i ∈ S i

/-- Each bid lies in the per-agent box $[\ell_i, u_i]$.

  $\forall i.\; \ell_i \le b_i \le u_i$. -/
def InBox [LE V] (b : I → V) (ℓ u : I → V) : Prop :=
  ∀ i, ℓ i ≤ b i ∧ b i ≤ u i

/-- A scalar strategy maps the input bid interval $[\ell, u]$ into $[\ell', u']$.

  Captures Lipschitz/contraction conditions for best-response dynamics in bounded
  auctions. -/
def StrategyMapsBoxToBox [LE V] (σ : V → V) (ℓ u ℓ' u' : V) : Prop :=
  ∀ v, ℓ ≤ v ∧ v ≤ u → ℓ' ≤ σ v ∧ σ v ≤ u'

/-- `InBox b ℓ u` is equivalent to `InSet b (fun i => Set.Icc (ℓ i) (u i))`.

  Makes box-constrained bid spaces interoperable with the Mathlib `Set.Icc` API
  (continuity, compactness, integration). -/
lemma inBox_iff_inSet_Icc [Preorder V] (b : I → V) (ℓ u : I → V) :
    InBox b ℓ u ↔ InSet b (fun i => Set.Icc (ℓ i) (u i)) := by
  unfold InBox InSet
  simp [Set.mem_Icc]

end Auction.BidProfile

/-! ## Ordered-bid utilities

The following definitions apply when bids are linearly ordered (e.g., scalar bids in `ℝ`).
They are **mathematical tools** for computing bid maxima and argmaxes — they do not define
any particular auction's winner or allocation rule.

Each concrete auction explicitly states whether it uses these utilities and how. -/

section OrderedBids

variable {I : Type*} [Fintype I] [Nontrivial I] {V : Type*} [LinearOrder V]

namespace Auction

variable (b : I → V)

/-- The highest bid in a profile. -/
@[simp]
def maxBid : V := Finset.sup' Finset.univ Finset.univ_nonempty b

/-- There exists a bidder whose bid equals the highest bid. -/
lemma exists_maxBid : ∃ i : I, b i = maxBid b := by
  obtain ⟨i, _, h2⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty b
  exact ⟨i, symm h2⟩

/-- The bidder whose bid achieves the maximum.

  This is a mathematical argmax, not a declaration that any auction's winner is the
  highest bidder. Concrete auctions define their own allocation/winner rules. -/
noncomputable def argmaxBid : I := Classical.choose (exists_maxBid b)

/-- The argmax bidder's bid equals the highest bid. -/
lemma argmaxBid_eq_maxBid : b (argmaxBid b) = maxBid b :=
  Classical.choose_spec (exists_maxBid b)

/-- Every bid is at most the argmax bidder's bid. -/
lemma bid_le_maxBid (j : I) : b j ≤ b (argmaxBid b) := by
  rw [argmaxBid_eq_maxBid b]
  exact Finset.le_sup' b (Finset.mem_univ j)

/-- If `i` strictly outbids all others, then `i` is the argmax bidder. -/
lemma eq_argmaxBid_of_strict_max (i : I) (h : ∀ j, j ≠ i → b j < b i) :
    i = argmaxBid b := by
  contrapose! h
  exact ⟨argmaxBid b, h.symm, bid_le_maxBid b i⟩

variable [DecidableEq I]

/-- The highest bid excluding bidder `i`. -/
noncomputable def maxBidExcluding (i : I) : V :=
  (Finset.univ.erase i).sup' Finset.univ_nontrivial.erase_nonempty b

/-- Excluding any bidder can only decrease the highest bid. -/
lemma maxBidExcluding_le_maxBid (i : I) : maxBidExcluding b i ≤ maxBid b := by
  apply Finset.sup'_mono
  exact Finset.subset_univ _

/-- If `i` is not the argmax bidder, excluding `i` does not change the highest bid. -/
lemma maxBidExcluding_eq_maxBid_of_not_argmax {i : I} (h : i ≠ argmaxBid b) :
    maxBidExcluding b i = maxBid b := by
  apply le_antisymm
  · exact maxBidExcluding_le_maxBid b i
  · rw [← argmaxBid_eq_maxBid b]
    exact Finset.le_sup' b (Finset.mem_erase_of_ne_of_mem h.symm (Finset.mem_univ _))

/-- The argmax bidder's bid is at least the highest bid among all others. -/
lemma maxBidExcluding_le_argmaxBid_bid :
    maxBidExcluding b (argmaxBid b) ≤ b (argmaxBid b) := by
  calc maxBidExcluding b (argmaxBid b)
      ≤ maxBid b := maxBidExcluding_le_maxBid b (argmaxBid b)
    _ = b (argmaxBid b) := (argmaxBid_eq_maxBid b).symm

/-- Changing `i`'s bid does not affect the highest bid among the others. -/
lemma maxBidExcluding_update_self (i : I) (bi : V) :
    maxBidExcluding (Function.update b i bi) i = maxBidExcluding b i := by
  apply Finset.sup'_congr _ rfl
  intro j hj
  simp [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

end Auction

end OrderedBids
