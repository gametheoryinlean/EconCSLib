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

- abstract auction formats: `SingleItemAuction`, `SingleParameterAuction`,
  `CombinatorialAuction`, and the transfer-layer `SingleParameterMechanism`
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
       └─ SingleParameterAuction I R                -- auction-facing scalar-bid layer

MultipleParameterMechanism I A V P                  -- T i = A → V
  └─ CombinatorialAuction I k V P                   -- A = CombinatorialAllocation I k
```

## Main definitions

### Auction formats
* `SingleItemAuction` — one indivisible item; allocation is `Option I` (winner or no sale)
* `SingleParameterAuction` — auction-facing wrapper around scalar reports and allocations
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

### Ordered-bid utilities (`Auction.BidProfile`, `SingleParameterAuction`)
The following are mathematical tools for auction rules that rank bids.
**They do not define any specific auction's winner** — each concrete auction specifies
its own allocation rule, which may or may not select the highest bidder.

* `Auction.BidProfile.maxBid` - the highest bid in a profile
* `Auction.BidProfile.argmaxBid` - the bidder with the highest bid
* `Auction.BidProfile.without` - the profile of bids with one bidder marked as excluded
* `Auction.BidProfileWithout.maxBid` - the highest bid after excluding that bidder
* `SingleParameterAuction.maxBid`, `.argmaxBid`, `.maxBidExcluding` -
  method-style access to the same tools from an auction object
* compatibility aliases `Auction.maxBid`, `Auction.argmaxBid`, `Auction.maxBidExcluding`
* update lemmas for `argmaxBid` and `maxBidExcluding`

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

/-- Auction-facing single-parameter layer.

This wraps the transfer-layer `SingleParameterMechanism` with auction
terminology: reports are scalar bid profiles, allocations are scalar allocation
profiles, and payments are scalar. Ordered-bid utilities such as max bid,
argmax bid, and max bid excluding a bidder are exposed below as methods on this
layer, while the DSIC/monotonicity/payment theory remains inherited from
`SingleParameterMechanism`. -/
structure SingleParameterAuction (I : Type*) (R : Type*)
    extends SingleParameterMechanism I R

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

namespace Auction

/-- A scalar bid profile: one bid for each bidder.

This is the auction-facing wrapper around the raw function type `I → V`.  The
wrapper lets ordered-bid operations be expressed as methods of a bid profile
while retaining a coercion to the underlying function for existing mechanisms
and proofs. -/
structure BidProfile (I : Type*) (V : Type*) where
  /-- The reported bid of each bidder. -/
  bid : I → V

namespace BidProfile

variable {I V : Type*}

instance : CoeFun (BidProfile I V) (fun _ => I → V) where
  coe b := b.bid

/-- Promote a raw bid function to a named bid profile. -/
@[simps]
def ofFunction (b : I → V) : BidProfile I V where
  bid := b

end BidProfile

/-- A bid profile viewed with one bidder excluded.

The original profile is retained, but all operations in this namespace interpret
`excluded` as removed from the active bidder set.  This is the reusable
`bidProfileWithout_i` abstraction used by max-bid-excluding and DSIC arguments
where bidder `i`'s report is varied while opponents' reports are fixed. -/
structure BidProfileWithout (I : Type*) (V : Type*) where
  /-- The full bid profile from which one bidder is excluded. -/
  profile : BidProfile I V
  /-- The bidder excluded from the active profile. -/
  excluded : I

namespace BidProfileWithout

variable {I V : Type*}

/-- The active bid of a non-excluded bidder. -/
def activeBid (b : BidProfileWithout I V) : {j : I // j ≠ b.excluded} → V :=
  fun j => b.profile j.1

end BidProfileWithout

end Auction

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

namespace Auction.BidProfile

variable (b : Auction.BidProfile I V)

/-- The highest bid in a profile. -/
@[simp]
def maxBid : V := Finset.sup' Finset.univ Finset.univ_nonempty fun i => b i

/-- There exists a bidder whose bid equals the highest bid. -/
lemma exists_maxBid : ∃ i : I, b i = b.maxBid := by
  obtain ⟨i, _, h2⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty fun i => b i
  exact ⟨i, h2.symm⟩

/-- The bidder whose bid achieves the maximum.

This is a mathematical argmax, not a declaration that any auction's winner is the
highest bidder. Concrete auctions define their own allocation/winner rules. -/
noncomputable def argmaxBid : I := Classical.choose (exists_maxBid b)

/-- The argmax bidder's bid equals the highest bid. -/
lemma argmaxBid_eq_maxBid : b (b.argmaxBid) = b.maxBid :=
  Classical.choose_spec (exists_maxBid b)

/-- Every bid is at most the argmax bidder's bid. -/
lemma bid_le_maxBid (j : I) : b j ≤ b (b.argmaxBid) := by
  rw [argmaxBid_eq_maxBid b]
  exact Finset.le_sup' (fun i => b i) (Finset.mem_univ j)

/-- If `i` strictly outbids all others, then `i` is the argmax bidder. -/
lemma eq_argmaxBid_of_strict_max (i : I) (h : ∀ j, j ≠ i → b j < b i) :
    i = b.argmaxBid := by
  contrapose! h
  exact ⟨b.argmaxBid, h.symm, bid_le_maxBid b i⟩

/-- The same bid profile, viewed with bidder `i` excluded. -/
def without (i : I) : Auction.BidProfileWithout I V where
  profile := b
  excluded := i

omit [Fintype I] [Nontrivial I] [LinearOrder V] in
@[simp] lemma without_profile (i : I) : (b.without i).profile = b := rfl

omit [Fintype I] [Nontrivial I] [LinearOrder V] in
@[simp] lemma without_excluded (i : I) : (b.without i).excluded = i := rfl

end Auction.BidProfile

namespace Auction.BidProfileWithout

variable [DecidableEq I] (b : Auction.BidProfileWithout I V)

/-- The highest bid among the active bidders after excluding one bidder. -/
noncomputable def maxBid : V :=
  (Finset.univ.erase b.excluded).sup' Finset.univ_nontrivial.erase_nonempty
    fun j => b.profile j

/-- Any active bidder has bid at most the maximum among the active bidders. -/
lemma bid_le_maxBid_of_ne {j : I} (hji : j ≠ b.excluded) :
    b.profile j ≤ b.maxBid := by
  unfold maxBid
  exact
    Finset.le_sup' (fun j => b.profile j)
      (Finset.mem_erase_of_ne_of_mem hji (Finset.mem_univ j))

/-- Some active bidder attains the maximum among the active bidders. -/
lemma exists_maxBid :
    ∃ j, j ≠ b.excluded ∧ b.profile j = b.maxBid := by
  unfold maxBid
  obtain ⟨j, hjmem, hj⟩ :=
    Finset.exists_mem_eq_sup' (s := Finset.univ.erase b.excluded)
      (H := Finset.univ_nontrivial.erase_nonempty) (f := fun j => b.profile j)
  exact ⟨j, Finset.ne_of_mem_erase hjmem, hj.symm⟩

end Auction.BidProfileWithout

namespace Auction.BidProfile

variable (b : Auction.BidProfile I V) [DecidableEq I]

/-- The highest bid excluding bidder `i`. -/
noncomputable def maxBidExcluding (i : I) : V := (b.without i).maxBid

/-- Any bidder other than `i` has bid at most the highest bid excluding `i`. -/
lemma bid_le_maxBidExcluding_of_ne {i j : I} (hji : j ≠ i) :
    b j ≤ b.maxBidExcluding i :=
  Auction.BidProfileWithout.bid_le_maxBid_of_ne (b.without i) hji

/-- Some bidder other than `i` attains the highest bid excluding `i`. -/
lemma exists_maxBidExcluding (i : I) :
    ∃ j, j ≠ i ∧ b j = b.maxBidExcluding i := by
  simpa [maxBidExcluding, without] using
    Auction.BidProfileWithout.exists_maxBid (b.without i)

/-- Excluding any bidder can only decrease the highest bid. -/
lemma maxBidExcluding_le_maxBid (i : I) : b.maxBidExcluding i ≤ b.maxBid := by
  unfold maxBidExcluding Auction.BidProfileWithout.maxBid without maxBid
  apply Finset.sup'_mono
  exact Finset.subset_univ _

/-- If `i` is not the argmax bidder, excluding `i` does not change the highest bid. -/
lemma maxBidExcluding_eq_maxBid_of_not_argmax {i : I} (h : i ≠ b.argmaxBid) :
    b.maxBidExcluding i = b.maxBid := by
  apply le_antisymm
  · exact maxBidExcluding_le_maxBid b i
  · rw [← argmaxBid_eq_maxBid b]
    exact Finset.le_sup' (fun j => b j) (Finset.mem_erase_of_ne_of_mem h.symm (Finset.mem_univ _))

/-- The argmax bidder's bid is at least the highest bid among all others. -/
lemma maxBidExcluding_le_argmaxBid_bid :
    b.maxBidExcluding b.argmaxBid ≤ b b.argmaxBid := by
  calc b.maxBidExcluding b.argmaxBid
      ≤ b.maxBid := maxBidExcluding_le_maxBid b b.argmaxBid
    _ = b b.argmaxBid := (argmaxBid_eq_maxBid b).symm

/-- Changing `i`'s bid does not affect the highest bid among the others. -/
lemma maxBidExcluding_update_self (i : I) (bi : V) :
    (Auction.BidProfile.ofFunction (Function.update b i bi)).maxBidExcluding i =
      b.maxBidExcluding i := by
  unfold maxBidExcluding Auction.BidProfileWithout.maxBid without
  apply Finset.sup'_congr _ rfl
  intro j hj
  simp [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

/-- If the updated bid strictly exceeds every old bid excluding `i`, then `i`
strictly outbids every other bidder after the update. -/
lemma update_self_strict_max_of_maxBidExcluding_lt {i : I} {bi : V}
    (hbi : b.maxBidExcluding i < bi) :
    ∀ j, j ≠ i → (Function.update b i bi) j < (Function.update b i bi) i := by
  intro j hji
  have hjle : b j ≤ b.maxBidExcluding i :=
    bid_le_maxBidExcluding_of_ne b hji
  have hjlt : b j < bi := lt_of_le_of_lt hjle hbi
  simpa [Function.update_of_ne hji, Function.update_self] using hjlt

/-- If the updated bid strictly exceeds the old maximum excluding `i`, then
`i` becomes the selected argmax bidder after the update. -/
lemma argmaxBid_update_self_eq_of_maxBidExcluding_lt {i : I} {bi : V}
    (hbi : b.maxBidExcluding i < bi) :
    (Auction.BidProfile.ofFunction (Function.update b i bi)).argmaxBid = i := by
  exact
    (eq_argmaxBid_of_strict_max
      (Auction.BidProfile.ofFunction (Function.update b i bi)) i
      (update_self_strict_max_of_maxBidExcluding_lt (b := b) hbi)).symm

end Auction.BidProfile

namespace SingleParameterAuction

/-- Promote a report profile to the bid-profile abstraction associated with this auction. -/
def bidProfile (_A : SingleParameterAuction I V) (b : I → V) : Auction.BidProfile I V :=
  Auction.BidProfile.ofFunction b

/-- Method-style access to the highest bid in a report profile. -/
@[simp]
abbrev maxBid (A : SingleParameterAuction I V) (b : I → V) : V :=
  (bidProfile A b).maxBid

/-- Method-style access to an argmax bidder in a report profile. -/
noncomputable def argmaxBid (A : SingleParameterAuction I V) (b : I → V) : I :=
  (bidProfile A b).argmaxBid

/-- Method-style access to the report profile with bidder `i` excluded. -/
def bidProfileWithout [DecidableEq I] (A : SingleParameterAuction I V) (b : I → V) (i : I) :
    Auction.BidProfileWithout I V :=
  (bidProfile A b).without i

/-- Method-style access to the highest bid excluding bidder `i`. -/
noncomputable abbrev maxBidExcluding [DecidableEq I]
    (A : SingleParameterAuction I V) (b : I → V) (i : I) : V :=
  (bidProfile A b).maxBidExcluding i

end SingleParameterAuction

namespace Auction

variable (b : I → V)

/-- The highest bid in a profile. -/
@[simp]
abbrev maxBid : V := (BidProfile.ofFunction b).maxBid

/-- There exists a bidder whose bid equals the highest bid. -/
lemma exists_maxBid : ∃ i : I, b i = maxBid b := by
  simpa [maxBid] using BidProfile.exists_maxBid (BidProfile.ofFunction b)

/-- The bidder whose bid achieves the maximum.

  This is a mathematical argmax, not a declaration that any auction's winner is the
  highest bidder. Concrete auctions define their own allocation/winner rules. -/
noncomputable def argmaxBid : I := (BidProfile.ofFunction b).argmaxBid

/-- The argmax bidder's bid equals the highest bid. -/
lemma argmaxBid_eq_maxBid : b (argmaxBid b) = maxBid b :=
  BidProfile.argmaxBid_eq_maxBid (BidProfile.ofFunction b)

/-- Every bid is at most the argmax bidder's bid. -/
lemma bid_le_maxBid (j : I) : b j ≤ b (argmaxBid b) := by
  exact BidProfile.bid_le_maxBid (BidProfile.ofFunction b) j

/-- If `i` strictly outbids all others, then `i` is the argmax bidder. -/
lemma eq_argmaxBid_of_strict_max (i : I) (h : ∀ j, j ≠ i → b j < b i) :
    i = argmaxBid b := by
  exact BidProfile.eq_argmaxBid_of_strict_max (BidProfile.ofFunction b) i h

variable [DecidableEq I]

/-- The bid profile with bidder `i` excluded. -/
def bidProfileWithout (i : I) : BidProfileWithout I V :=
  (BidProfile.ofFunction b).without i

/-- The highest bid excluding bidder `i`. -/
noncomputable abbrev maxBidExcluding (i : I) : V :=
  (BidProfile.ofFunction b).maxBidExcluding i

/-- Any bidder other than `i` has bid at most the highest bid excluding `i`. -/
lemma bid_le_maxBidExcluding_of_ne {i j : I} (hji : j ≠ i) :
    b j ≤ maxBidExcluding b i :=
  BidProfile.bid_le_maxBidExcluding_of_ne (BidProfile.ofFunction b) hji

/-- Some bidder other than `i` attains the highest bid excluding `i`. -/
lemma exists_maxBidExcluding (i : I) :
    ∃ j, j ≠ i ∧ b j = maxBidExcluding b i := by
  simpa [maxBidExcluding] using
    BidProfile.exists_maxBidExcluding (BidProfile.ofFunction b) i

/-- Excluding any bidder can only decrease the highest bid. -/
lemma maxBidExcluding_le_maxBid (i : I) : maxBidExcluding b i ≤ maxBid b := by
  exact BidProfile.maxBidExcluding_le_maxBid (BidProfile.ofFunction b) i

/-- If `i` is not the argmax bidder, excluding `i` does not change the highest bid. -/
lemma maxBidExcluding_eq_maxBid_of_not_argmax {i : I} (h : i ≠ argmaxBid b) :
    maxBidExcluding b i = maxBid b := by
  exact BidProfile.maxBidExcluding_eq_maxBid_of_not_argmax (BidProfile.ofFunction b) h

/-- The argmax bidder's bid is at least the highest bid among all others. -/
lemma maxBidExcluding_le_argmaxBid_bid :
    maxBidExcluding b (argmaxBid b) ≤ b (argmaxBid b) := by
  exact BidProfile.maxBidExcluding_le_argmaxBid_bid (BidProfile.ofFunction b)

/-- Changing `i`'s bid does not affect the highest bid among the others. -/
lemma maxBidExcluding_update_self (i : I) (bi : V) :
    maxBidExcluding (Function.update b i bi) i = maxBidExcluding b i := by
  exact BidProfile.maxBidExcluding_update_self (BidProfile.ofFunction b) i bi

/-- If the updated bid strictly exceeds every old bid excluding `i`, then `i`
strictly outbids every other bidder after the update. -/
lemma update_self_strict_max_of_maxBidExcluding_lt {i : I} {bi : V}
    (hbi : maxBidExcluding b i < bi) :
    ∀ j, j ≠ i → (Function.update b i bi) j < (Function.update b i bi) i := by
  exact BidProfile.update_self_strict_max_of_maxBidExcluding_lt
    (BidProfile.ofFunction b) hbi

/-- If the updated bid strictly exceeds the old maximum excluding `i`, then
`i` becomes the selected argmax bidder after the update. -/
lemma argmaxBid_update_self_eq_of_maxBidExcluding_lt {i : I} {bi : V}
    (hbi : maxBidExcluding b i < bi) :
    argmaxBid (Function.update b i bi) = i := by
  exact BidProfile.argmaxBid_update_self_eq_of_maxBidExcluding_lt
    (BidProfile.ofFunction b) hbi

end Auction

end OrderedBids
