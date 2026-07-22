/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.GameTreeStrategicForm
import EconCSLib.GameTheory.ExtensiveGame.Strategy

/-!
# Examples.UltimatumGame

Ultimatum-game examples for MSZ Chapter 7.

The first section follows Exercise 7.5 directly: Allen asks for an integer
amount between 0 and 100, Rick accepts or rejects, and the file records the
extensive-form structure, pure strategy sets, and Nash payoff construction.

The later section is a compact two-offer worked example in the `GameTree`
framework.  It uses the existing finite-tree API for subtrees, Kuhn's theorem,
root-scoped Nash equilibrium, subgame-perfect equilibrium, and strategic-form
extraction.

## References

* [MSZ] Chapter 7, Exercise 7.5
-/

/-! ## MSZ Exercise 7.5: full 0..100 extensive-form specification

This section follows the textbook exercise directly. Allen first asks for an
integer amount between 0 and 100. Rick observes Allen's request and accepts or
rejects. If Rick accepts, Allen receives the requested amount and Rick receives
the remainder. If Rick rejects, both receive zero.

The later `GameTree` section is a smaller two-offer worked example used to
exercise the current finite-tree equilibrium API.
-/

namespace Examples.UltimatumGame.Full

/-! ### Players, offers, responses, and states -/

/-- The two textbook players. -/
inductive Player
  | Allen
  | Rick
  deriving DecidableEq, Repr

/-- Allen's requested amount, represented as `Fin 101`, i.e. `{0, ..., 100}`. -/
abbrev Offer := Fin 101

/-- Rick's response after observing Allen's offer. -/
inductive Response
  | Accept
  | Reject
  deriving DecidableEq, Repr

open Player Response

/-- States of the full 0..100 ultimatum game. -/
inductive State
  | root
  | rickDecision (x : Offer)
  | accepted (x : Offer)
  | rejected (x : Offer)
  deriving DecidableEq, Repr

open State

/-- Available actions at each state.

At the root, Allen chooses one of the 101 offers.  At a Rick decision node,
Rick chooses accept or reject.  Terminal states have no actions. -/
def action : State → Type
  | root => Offer
  | rickDecision _ => Response
  | accepted _ => Empty
  | rejected _ => Empty

/-- Transition function for the full Exercise 7.5 game. -/
def next : (s : State) → action s → State
  | root, x => rickDecision x
  | rickDecision x, Accept => accepted x
  | rickDecision x, Reject => rejected x

/-- Player assignment for the full Exercise 7.5 game. -/
def mover : State → Option Player
  | root => some Allen
  | rickDecision _ => some Rick
  | accepted _ => none
  | rejected _ => none

/-- Payoffs for the full Exercise 7.5 game.

If Rick accepts offer `x`, Allen receives `x` and Rick receives `100 - x`.
If Rick rejects, both receive zero.  Nonterminal payoffs are set to zero because
only terminal payoffs matter. -/
def payoff : State → Player → ℤ
  | accepted x, Allen => x.val
  | accepted x, Rick => 100 - x.val
  | rejected _, _ => 0
  | _, _ => 0

/-- The full 0..100 extensive-form ultimatum game from MSZ Exercise 7.5. -/
def game : ExtensiveGame Player ℤ where
  State := State
  Action := action
  next := next
  init := root
  mover := mover
  payoff := payoff

/-! ### Basic verification -/

example : game.mover root = some Allen := rfl

example (x : Offer) : game.mover (rickDecision x) = some Rick := rfl

example (x : Offer) : game.next root x = rickDecision x := rfl

example (x : Offer) : game.next (rickDecision x) Accept = accepted x := rfl

example (x : Offer) : game.next (rickDecision x) Reject = rejected x := rfl

example (x : Offer) : game.payoff (accepted x) Allen = x.val := rfl

example (x : Offer) : game.payoff (accepted x) Rick = 100 - x.val := rfl

example (x : Offer) : game.payoff (rejected x) Allen = 0 := rfl

example (x : Offer) : game.payoff (rejected x) Rick = 0 := rfl

example (x : Offer) : IsEmpty (game.Action (accepted x)) := by
  constructor
  intro a
  cases a

example (x : Offer) : IsEmpty (game.Action (rejected x)) := by
  constructor
  intro a
  cases a

/-! ### Pure strategy sets -/

/-- Allen's pure strategies are exactly the 101 offers. -/
abbrev AllenStrategy := Offer

/-- Rick's pure strategies specify accept/reject after each possible offer. -/
abbrev RickStrategy := Offer → Response

/-- Extract Allen's chosen offer from an extensive-game pure strategy. -/
def allenStrategy (σ : game.Strategy Allen) : AllenStrategy :=
  σ root rfl

/-- Extract Rick's complete contingent response plan from an extensive-game
    pure strategy. -/
def rickStrategy (τ : game.Strategy Rick) : RickStrategy :=
  fun x => τ (rickDecision x) rfl

theorem allenStrategy_surjective (x : AllenStrategy) :
    ∃ σ : game.Strategy Allen, allenStrategy σ = x := by
  refine ⟨fun s hs => ?_, ?_⟩
  · cases s with
    | root => exact x
    | rickDecision y => cases hs
    | accepted y => cases hs
    | rejected y => cases hs
  · rfl

theorem rickStrategy_surjective (r : RickStrategy) :
    ∃ τ : game.Strategy Rick, rickStrategy τ = r := by
  refine ⟨fun s hs => ?_, ?_⟩
  · cases s with
    | root => cases hs
    | rickDecision x => exact r x
    | accepted x => cases hs
    | rejected x => cases hs
  · rfl

/-! ### Nash payoff construction -/

/-- The terminal state induced by a fixed offer and Rick response. -/
def responseState (x : Offer) : Response → State
  | Accept => accepted x
  | Reject => rejected x

/-- A pure strategy profile for the full 0..100 ultimatum game. -/
structure Profile where
  allen : AllenStrategy
  rick : RickStrategy

namespace Profile

/-- Extensionality for pure strategy profiles. -/
theorem ext {σ τ : Profile} (hallen : σ.allen = τ.allen)
    (hrick : σ.rick = τ.rick) : σ = τ := by
  cases σ with
  | mk a r =>
      cases τ with
      | mk a' r' =>
          dsimp at hallen hrick
          subst a'
          subst r'
          rfl

/-- The terminal state induced by a pure strategy profile. -/
def outcomeState (σ : Profile) : State :=
  responseState σ.allen (σ.rick σ.allen)

/-- The payoff induced by a pure strategy profile. -/
def payoff (σ : Profile) (i : Player) : ℤ :=
  Full.payoff σ.outcomeState i

/-- Change Allen's offer, holding Rick's contingent plan fixed. -/
def deviateAllen (σ : Profile) (x : AllenStrategy) : Profile :=
  { σ with allen := x }

/-- Change Rick's contingent response plan, holding Allen's offer fixed. -/
def deviateRick (σ : Profile) (r : RickStrategy) : Profile :=
  { σ with rick := r }

end Profile

/-- Pure Nash equilibrium for the full Exercise 7.5 strategic representation. -/
def IsNashProfile (σ : Profile) : Prop :=
  (∀ x : AllenStrategy, (σ.deviateAllen x).payoff Allen ≤ σ.payoff Allen) ∧
    ∀ r : RickStrategy, (σ.deviateRick r).payoff Rick ≤ σ.payoff Rick

theorem offer_val_nonneg (x : Offer) : (0 : ℤ) ≤ x.val := by
  omega

theorem offer_val_le_hundred (x : Offer) : (x.val : ℤ) ≤ 100 := by
  have hx : x.val < 101 := x.isLt
  omega

/-- Rick accepts exactly offer `a` and rejects every other offer. -/
def acceptsOnly (a : Offer) : RickStrategy :=
  fun x => if x = a then Accept else Reject

/-- The Nash profile supporting accepted split `(a, 100-a)`. -/
def nashProfile (a : Offer) : Profile where
  allen := a
  rick := acceptsOnly a

theorem nashProfile_payoff (a : Offer) :
    (nashProfile a).payoff Allen = a.val ∧
      (nashProfile a).payoff Rick = 100 - a.val := by
  simp [nashProfile, acceptsOnly, Profile.payoff, Profile.outcomeState,
    responseState, payoff]

/-- Every split `(a, 100-a)` is a Nash-equilibrium payoff.

The supporting profile has Allen ask for `a`, while Rick accepts exactly `a`
and rejects all other offers. -/
theorem nashProfile_isNash (a : Offer) :
    IsNashProfile (nashProfile a) := by
  constructor
  · intro x
    by_cases hx : x = a
    · subst hx
      simp [nashProfile, acceptsOnly, Profile.deviateAllen, Profile.payoff,
        Profile.outcomeState, responseState, payoff]
    · have ha_nonneg : (0 : ℤ) ≤ a.val := offer_val_nonneg a
      simp [nashProfile, acceptsOnly, Profile.deviateAllen, Profile.payoff,
        Profile.outcomeState, responseState, payoff, hx, ha_nonneg]
  · intro r
    by_cases hr : r a = Accept
    · simp [nashProfile, acceptsOnly, Profile.deviateRick, Profile.payoff,
        Profile.outcomeState, responseState, payoff, hr]
    · have hrReject : r a = Reject := by
        cases h : r a with
        | Accept => exact False.elim (hr h)
        | Reject => rfl
      have ha_le : (a.val : ℤ) ≤ 100 := offer_val_le_hundred a
      simp [nashProfile, acceptsOnly, Profile.deviateRick, Profile.payoff,
        Profile.outcomeState, responseState, payoff, hrReject, ha_le]

theorem nashProfile_payoff_set (a : Offer) :
    IsNashProfile (nashProfile a) ∧
      (nashProfile a).payoff Allen = a.val ∧
        (nashProfile a).payoff Rick = 100 - a.val :=
  ⟨nashProfile_isNash a, (nashProfile_payoff a).1, (nashProfile_payoff a).2⟩

/-! ### Subgame response optimality -/

/-- The offer in which Allen asks for all 100 dollars. -/
def hundred : Offer := ⟨100, by omega⟩

/-- The offer in which Allen asks for 99 dollars. -/
def ninetyNine : Offer := ⟨99, by omega⟩

theorem hundred_val : hundred.val = 100 := rfl

theorem ninetyNine_val : ninetyNine.val = 99 := rfl

theorem eq_hundred_of_val_eq (x : Offer) (h : (x.val : ℤ) = 100) :
    x = hundred := by
  apply Fin.ext
  have hnat : x.val = 100 := by omega
  simpa [hundred] using hnat

theorem eq_ninetyNine_of_val_eq (x : Offer) (h : (x.val : ℤ) = 99) :
    x = ninetyNine := by
  apply Fin.ext
  have hnat : x.val = 99 := by omega
  simpa [ninetyNine] using hnat

theorem ninetyNine_ne_hundred : ninetyNine ≠ hundred := by
  intro h
  have hval : ninetyNine.val = hundred.val := congrArg Fin.val h
  have h99 : ninetyNine.val = 99 := rfl
  have h100 : hundred.val = 100 := rfl
  omega

theorem offer_val_le_ninetyNine_of_ne_hundred (x : Offer)
    (hx : x ≠ hundred) : (x.val : ℤ) ≤ 99 := by
  have hxle : (x.val : ℤ) ≤ 100 := offer_val_le_hundred x
  have hxne : (x.val : ℤ) ≠ 100 := by
    intro hval
    exact hx (eq_hundred_of_val_eq x hval)
  omega

/-- Rick's response is optimal in the one-decision subgame following offer `x`. -/
def ResponseBestAt (x : Offer) (r : Response) : Prop :=
  ∀ y : Response, Full.payoff (responseState x y) Rick ≤
    Full.payoff (responseState x r) Rick

/-- Rick is sequentially rational at every one-offer subgame. -/
def RickSequentiallyRational (r : RickStrategy) : Prop :=
  ∀ x : Offer, ResponseBestAt x (r x)

/-- Accepting is always a weakly optimal response for Rick, because
`100 - x ≥ 0` for every admissible offer. -/
theorem responseBest_accept (x : Offer) : ResponseBestAt x Accept := by
  intro y
  cases y
  · simp [responseState, payoff]
  · have hx : (x.val : ℤ) ≤ 100 := offer_val_le_hundred x
    simp [responseState, payoff]
    omega

/-- Rejecting is also weakly optimal after the offer `100`, where Rick receives
zero whether he accepts or rejects. -/
theorem responseBest_reject_hundred : ResponseBestAt hundred Reject := by
  intro y
  cases y
  · change (100 : ℤ) - (hundred.val : ℤ) ≤ 0
    have hval : hundred.val = 100 := rfl
    omega
  · rfl

theorem responseBest_reject_iff (x : Offer) :
    ResponseBestAt x Reject ↔ x = hundred := by
  constructor
  · intro h
    have hAccept := h Accept
    have hxle : (x.val : ℤ) ≤ 100 := offer_val_le_hundred x
    have hval : (x.val : ℤ) = 100 := by
      simp [responseState, payoff] at hAccept
      omega
    exact eq_hundred_of_val_eq x hval
  · intro hx
    subst x
    exact responseBest_reject_hundred

theorem rickSequentiallyRational_iff (r : RickStrategy) :
    RickSequentiallyRational r ↔ ∀ x : Offer, r x = Accept ∨ x = hundred := by
  constructor
  · intro h x
    cases hr : r x with
    | Accept => exact Or.inl rfl
    | Reject =>
        have hbest : ResponseBestAt x Reject := by
          simpa [hr] using h x
        exact Or.inr ((responseBest_reject_iff x).mp hbest)
  · intro h x
    cases hr : r x with
    | Accept =>
        simpa [hr] using responseBest_accept x
    | Reject =>
        rcases h x with hacc | hx
        · rw [hacc] at hr
          cases hr
        · subst x
          simpa [hr] using responseBest_reject_hundred

/-- Rick accepts every offer. -/
def acceptsAll : RickStrategy :=
  fun _ => Accept

/-- Rick accepts every offer below 100 and rejects the offer 100. -/
def acceptsBelowHundred : RickStrategy :=
  fun x => if x = hundred then Reject else Accept

theorem acceptsAll_sequentiallyRational :
    RickSequentiallyRational acceptsAll := by
  intro x
  exact responseBest_accept x

theorem acceptsBelowHundred_sequentiallyRational :
    RickSequentiallyRational acceptsBelowHundred := by
  intro x
  by_cases hx : x = hundred
  · subst x
    simp [acceptsBelowHundred, responseBest_reject_hundred]
  · simp [acceptsBelowHundred, hx, responseBest_accept]

theorem rickSequentiallyRational_eq_acceptsAll_of_hundred_accept
    {r : RickStrategy} (hR : RickSequentiallyRational r)
    (h100 : r hundred = Accept) :
    r = acceptsAll := by
  funext x
  by_cases hx : x = hundred
  · subst x
    simpa [acceptsAll] using h100
  · have hx_or := (rickSequentiallyRational_iff r).mp hR x
    rcases hx_or with hacc | hhundred
    · simpa [acceptsAll] using hacc
    · exact False.elim (hx hhundred)

theorem rickSequentiallyRational_eq_acceptsBelowHundred_of_hundred_reject
    {r : RickStrategy} (hR : RickSequentiallyRational r)
    (h100 : r hundred = Reject) :
    r = acceptsBelowHundred := by
  funext x
  by_cases hx : x = hundred
  · subst x
    simp [acceptsBelowHundred, h100]
  · have hx_or := (rickSequentiallyRational_iff r).mp hR x
    rcases hx_or with hacc | hhundred
    · simp [acceptsBelowHundred, hx, hacc]
    · exact False.elim (hx hhundred)

/-! ### Subgame-perfect profiles -/

/-- Allen's offer is optimal at the root against Rick's contingent plan. -/
def AllenBestAgainst (x : AllenStrategy) (r : RickStrategy) : Prop :=
  ∀ y : AllenStrategy, Full.payoff (responseState y (r y)) Allen ≤
    Full.payoff (responseState x (r x)) Allen

/-- Pure subgame perfection for this two-stage game: Allen is optimal at the
root and Rick is optimal in every one-offer subgame. -/
def IsSubgamePerfectProfile (σ : Profile) : Prop :=
  AllenBestAgainst σ.allen σ.rick ∧ RickSequentiallyRational σ.rick

theorem IsSubgamePerfectProfile.toNashProfile {σ : Profile}
    (hσ : IsSubgamePerfectProfile σ) :
    IsNashProfile σ := by
  rcases hσ with ⟨hAllen, hRick⟩
  constructor
  · intro x
    simpa [AllenBestAgainst, Profile.deviateAllen, Profile.payoff,
      Profile.outcomeState] using hAllen x
  · intro r
    have hBest : ResponseBestAt σ.allen (σ.rick σ.allen) := hRick σ.allen
    simpa [ResponseBestAt, Profile.deviateRick, Profile.payoff,
      Profile.outcomeState] using hBest (r σ.allen)

theorem allenBest_acceptsAll_hundred :
    AllenBestAgainst hundred acceptsAll := by
  intro y
  have hy : y.val < 101 := y.isLt
  simp [acceptsAll, responseState, payoff, hundred]
  omega

theorem allenBest_acceptsAll_iff (x : AllenStrategy) :
    AllenBestAgainst x acceptsAll ↔ x = hundred := by
  constructor
  · intro h
    have hHundred := h hundred
    have hxle : (x.val : ℤ) ≤ 100 := offer_val_le_hundred x
    have hge : (100 : ℤ) ≤ x.val := by
      simp [acceptsAll, responseState, payoff, hundred] at hHundred
      omega
    have hval : (x.val : ℤ) = 100 := by omega
    exact eq_hundred_of_val_eq x hval
  · intro hx
    subst x
    exact allenBest_acceptsAll_hundred

theorem allenBest_acceptsBelowHundred_ninetyNine :
    AllenBestAgainst ninetyNine acceptsBelowHundred := by
  intro y
  by_cases hy : y = hundred
  · subst y
    have hle : (0 : ℤ) ≤ 99 := by omega
    simp [acceptsBelowHundred, responseState, payoff, ninetyNine, hundred]
  · have hle : (y.val : ℤ) ≤ 99 :=
      offer_val_le_ninetyNine_of_ne_hundred y hy
    simpa [acceptsBelowHundred, hy, ninetyNine_ne_hundred, responseState,
      payoff, ninetyNine] using hle

theorem allenBest_acceptsBelowHundred_iff (x : AllenStrategy) :
    AllenBestAgainst x acceptsBelowHundred ↔ x = ninetyNine := by
  constructor
  · intro h
    by_cases hx : x = hundred
    · subst x
      have hNinetyNine := h ninetyNine
      simp [acceptsBelowHundred, responseState, payoff, ninetyNine, hundred]
        at hNinetyNine
    · have hNinetyNine := h ninetyNine
      have hxle : (x.val : ℤ) ≤ 99 :=
        offer_val_le_ninetyNine_of_ne_hundred x hx
      have hge : (99 : ℤ) ≤ x.val := by
        simpa [acceptsBelowHundred, hx, ninetyNine_ne_hundred, responseState,
          payoff, ninetyNine] using hNinetyNine
      have hval : (x.val : ℤ) = 99 := by omega
      exact eq_ninetyNine_of_val_eq x hval
  · intro hx
    subst x
    exact allenBest_acceptsBelowHundred_ninetyNine

/-- The SPE where Rick accepts the offer 100, so Allen asks for 100. -/
def acceptHundredProfile : Profile where
  allen := hundred
  rick := acceptsAll

/-- The SPE where Rick rejects the offer 100, so Allen asks for 99. -/
def rejectHundredProfile : Profile where
  allen := ninetyNine
  rick := acceptsBelowHundred

theorem acceptHundredProfile_isSubgamePerfect :
    IsSubgamePerfectProfile acceptHundredProfile :=
  ⟨allenBest_acceptsAll_hundred, acceptsAll_sequentiallyRational⟩

theorem rejectHundredProfile_isSubgamePerfect :
    IsSubgamePerfectProfile rejectHundredProfile :=
  ⟨allenBest_acceptsBelowHundred_ninetyNine,
    acceptsBelowHundred_sequentiallyRational⟩

/-- The full pure-strategy SPE characterization for the 0..100 ultimatum game. -/
theorem isSubgamePerfectProfile_iff (σ : Profile) :
    IsSubgamePerfectProfile σ ↔
      σ = acceptHundredProfile ∨ σ = rejectHundredProfile := by
  constructor
  · intro hσ
    rcases hσ with ⟨hAllen, hRick⟩
    cases h100 : σ.rick hundred with
    | Accept =>
        have hr : σ.rick = acceptsAll :=
          rickSequentiallyRational_eq_acceptsAll_of_hundred_accept hRick h100
        have hAllen' : AllenBestAgainst σ.allen acceptsAll := by
          simpa [hr] using hAllen
        have hx : σ.allen = hundred := (allenBest_acceptsAll_iff σ.allen).mp hAllen'
        exact Or.inl (Profile.ext hx hr)
    | Reject =>
        have hr : σ.rick = acceptsBelowHundred :=
          rickSequentiallyRational_eq_acceptsBelowHundred_of_hundred_reject
            hRick h100
        have hAllen' : AllenBestAgainst σ.allen acceptsBelowHundred := by
          simpa [hr] using hAllen
        have hx : σ.allen = ninetyNine :=
          (allenBest_acceptsBelowHundred_iff σ.allen).mp hAllen'
        exact Or.inr (Profile.ext hx hr)
  · rintro (rfl | rfl)
    · exact acceptHundredProfile_isSubgamePerfect
    · exact rejectHundredProfile_isSubgamePerfect

theorem acceptHundredProfile_payoff :
    acceptHundredProfile.payoff Allen = 100 ∧
      acceptHundredProfile.payoff Rick = 0 := by
  constructor
  · change (hundred.val : ℤ) = 100
    simp [hundred_val]
  · change (100 : ℤ) - (hundred.val : ℤ) = 0
    simp [hundred_val]

theorem rejectHundredProfile_payoff :
    rejectHundredProfile.payoff Allen = 99 ∧
      rejectHundredProfile.payoff Rick = 1 := by
  constructor
  · change Full.payoff (responseState ninetyNine (acceptsBelowHundred ninetyNine))
      Allen = 99
    change (ninetyNine.val : ℤ) = 99
    simp [ninetyNine_val]
  · change Full.payoff (responseState ninetyNine (acceptsBelowHundred ninetyNine))
      Rick = 1
    change (100 : ℤ) - (ninetyNine.val : ℤ) = 1
    simp [ninetyNine_val]

end Examples.UltimatumGame.Full

namespace Examples.UltimatumGame

open GameTree

/-! ### Players and terminal payoffs -/

/-- The two players in the ultimatum game. -/
inductive Player
  | Proposer
  | Responder
  deriving DecidableEq, Repr

open Player

/-- Payoff vector for a terminal split. -/
def payoff (proposer responder : ℤ) : Player → ℤ
  | Proposer => proposer
  | Responder => responder

/-- Terminal tree for a payoff vector. -/
def terminal (proposer responder : ℤ) : GameTree Player ℤ :=
  Leaf (payoff proposer responder)

/-- Rejection gives both players zero. -/
def reject : GameTree Player ℤ :=
  terminal 0 0

/-- The low offer gives the proposer 2 and the responder 1 if accepted. -/
def acceptLow : GameTree Player ℤ :=
  terminal 2 1

/-- The high offer gives the proposer 1 and the responder 2 if accepted. -/
def acceptHigh : GameTree Player ℤ :=
  terminal 1 2

/-! ### Game tree -/

/-- The responder's decision after the low offer.

The head child is acceptance; the tail child is rejection. -/
def lowOfferResponse : GameTree Player ℤ :=
  Node Responder acceptLow (List.cons reject List.nil)

/-- The responder's decision after the high offer.

The head child is acceptance; the tail child is rejection. -/
def highOfferResponse : GameTree Player ℤ :=
  Node Responder acceptHigh (List.cons reject List.nil)

/-- The full two-offer ultimatum game.

The proposer chooses the low offer first or the high offer second. -/
def ultimatumGame : GameTree Player ℤ :=
  Node Proposer lowOfferResponse (List.cons highOfferResponse List.nil)

/-! ### Basic payoff and tree checks -/

example : payoff 2 1 Proposer = 2 := rfl

example : payoff 2 1 Responder = 1 := rfl

example : payoff 0 0 Proposer = 0 := rfl

example : children lowOfferResponse = List.cons acceptLow (List.cons reject List.nil) := rfl

example : children highOfferResponse = List.cons acceptHigh (List.cons reject List.nil) := rfl

example : children ultimatumGame =
    List.cons lowOfferResponse (List.cons highOfferResponse List.nil) := rfl

/-! ### Backward-induction values -/

/-- At the low-offer response node, backward induction accepts the low offer. -/
theorem lowOfferResponse_value :
    value lowOfferResponse = payoff 2 1 := by
  have hchild :
      ∃ c ∈ List.cons acceptLow (List.cons reject List.nil),
        value lowOfferResponse = value c := by
    simpa [lowOfferResponse] using
      (value_Node_eq_some_child_value
        (m := Responder)
        (h := acceptLow)
        (t := List.cons reject List.nil))
  rcases hchild with ⟨c, hmem, hvalue⟩
  rcases List.mem_cons.mp hmem with rfl | hmem_tail
  · simpa [acceptLow, terminal] using hvalue
  · have hc : c = reject := by
      simpa using hmem_tail
    subst c
    have hge :
        (value acceptLow) Responder ≤ (value lowOfferResponse) Responder := by
      simpa [lowOfferResponse] using
        (value_Node_ge Responder acceptLow (List.cons reject List.nil)
          acceptLow (by simp))
    have hbad : (1 : ℤ) ≤ 0 := by
      simp [acceptLow, reject, terminal, payoff, hvalue] at hge
    exact False.elim ((by decide : ¬ ((1 : ℤ) ≤ 0)) hbad)

/-- At the high-offer response node, backward induction accepts the high offer. -/
theorem highOfferResponse_value :
    value highOfferResponse = payoff 1 2 := by
  have hchild :
      ∃ c ∈ List.cons acceptHigh (List.cons reject List.nil),
        value highOfferResponse = value c := by
    simpa [highOfferResponse] using
      (value_Node_eq_some_child_value
        (m := Responder)
        (h := acceptHigh)
        (t := List.cons reject List.nil))
  rcases hchild with ⟨c, hmem, hvalue⟩
  rcases List.mem_cons.mp hmem with rfl | hmem_tail
  · simpa [acceptHigh, terminal] using hvalue
  · have hc : c = reject := by
      simpa using hmem_tail
    subst c
    have hge :
        (value acceptHigh) Responder ≤ (value highOfferResponse) Responder := by
      simpa [highOfferResponse] using
        (value_Node_ge Responder acceptHigh (List.cons reject List.nil)
          acceptHigh (by simp))
    have hbad : (2 : ℤ) ≤ 0 := by
      simp [acceptHigh, reject, terminal, payoff, hvalue] at hge
    exact False.elim ((by decide : ¬ ((2 : ℤ) ≤ 0)) hbad)

/-- At the root, backward induction selects the low offer because it gives the
    proposer payoff `2`, while the high offer gives proposer payoff `1`. -/
theorem ultimatumGame_value :
    value ultimatumGame = payoff 2 1 := by
  have hchild :
      ∃ c ∈ List.cons lowOfferResponse (List.cons highOfferResponse List.nil),
        value ultimatumGame = value c := by
    simpa [ultimatumGame] using
      (value_Node_eq_some_child_value
        (m := Proposer)
        (h := lowOfferResponse)
        (t := List.cons highOfferResponse List.nil))
  rcases hchild with ⟨c, hmem, hvalue⟩
  rcases List.mem_cons.mp hmem with rfl | hmem_tail
  · simpa [lowOfferResponse_value] using hvalue
  · have hc : c = highOfferResponse := by
      simpa using hmem_tail
    subst c
    have hge :
        (value lowOfferResponse) Proposer ≤ (value ultimatumGame) Proposer := by
      simpa [ultimatumGame] using
        (value_Node_ge Proposer lowOfferResponse
          (List.cons highOfferResponse List.nil) lowOfferResponse (by simp))
    have hbad : (2 : ℤ) ≤ 1 := by
      simp [lowOfferResponse_value, highOfferResponse_value, payoff, hvalue] at hge
    exact False.elim ((by decide : ¬ ((2 : ℤ) ≤ 1)) hbad)

/-- The canonical backward-induction strategy reaches the low accepted split. -/
theorem ultimatum_optStrategy_outcome :
    outcome (optStrategy : Strategy Player ℤ) ultimatumGame = payoff 2 1 := by
  rw [outcome_optStrategy_eq_value]
  exact ultimatumGame_value

/-- Under the canonical backward-induction strategy, the proposer gets `2`. -/
theorem ultimatum_optStrategy_proposer_payoff :
    outcome (optStrategy : Strategy Player ℤ) ultimatumGame Proposer = 2 := by
  rw [ultimatum_optStrategy_outcome]
  rfl

/-- Under the canonical backward-induction strategy, the responder gets `1`. -/
theorem ultimatum_optStrategy_responder_payoff :
    outcome (optStrategy : Strategy Player ℤ) ultimatumGame Responder = 1 := by
  rw [ultimatum_optStrategy_outcome]
  rfl

/-! ### Subgames and terminal subgames -/

/-- The low-offer response node is the head subgame of the full game. -/
theorem lowOfferResponse_subtree :
    Subtree lowOfferResponse ultimatumGame := by
  unfold ultimatumGame
  exact Subtree.head Proposer lowOfferResponse
    (List.cons highOfferResponse List.nil)

/-- The low-offer response node is a proper subgame of the full game. -/
theorem lowOfferResponse_properSubgame :
    ProperSubgame lowOfferResponse ultimatumGame := by
  unfold ultimatumGame
  exact ProperSubgame.head Proposer lowOfferResponse
    (List.cons highOfferResponse List.nil)

/-- The high-offer response node is the tail subgame of the full game. -/
theorem highOfferResponse_subtree :
    Subtree highOfferResponse ultimatumGame := by
  unfold ultimatumGame
  exact Subtree.tail_mem Proposer lowOfferResponse
    (List.cons highOfferResponse List.nil) (by simp)

/-- The high-offer response node is a proper subgame of the full game. -/
theorem highOfferResponse_properSubgame :
    ProperSubgame highOfferResponse ultimatumGame := by
  unfold ultimatumGame
  exact ProperSubgame.tail_mem Proposer lowOfferResponse
    (List.cons highOfferResponse List.nil) (by simp)

/-- The accepted low offer is the head terminal subgame of the low-offer
    response node. -/
theorem acceptLow_subtree_lowOfferResponse :
    Subtree acceptLow lowOfferResponse := by
  unfold lowOfferResponse
  exact Subtree.head Responder acceptLow (List.cons reject List.nil)

/-- Rejection is the tail terminal subgame of the low-offer response node. -/
theorem reject_subtree_lowOfferResponse :
    Subtree reject lowOfferResponse := by
  unfold lowOfferResponse
  exact Subtree.tail_mem Responder acceptLow (List.cons reject List.nil) (by simp)

/-- The accepted high offer is the head terminal subgame of the high-offer
    response node. -/
theorem acceptHigh_subtree_highOfferResponse :
    Subtree acceptHigh highOfferResponse := by
  unfold highOfferResponse
  exact Subtree.head Responder acceptHigh (List.cons reject List.nil)

/-- Rejection is also the tail terminal subgame of the high-offer response node. -/
theorem reject_subtree_highOfferResponse :
    Subtree reject highOfferResponse := by
  unfold highOfferResponse
  exact Subtree.tail_mem Responder acceptHigh (List.cons reject List.nil) (by simp)

/-- The accepted low offer is a terminal subtree of the full game. -/
theorem acceptLow_subtree_ultimatumGame :
    Subtree acceptLow ultimatumGame :=
  Subtree.trans acceptLow_subtree_lowOfferResponse lowOfferResponse_subtree

/-- The accepted low offer is a proper terminal subgame of the full game. -/
theorem acceptLow_properSubgame_ultimatumGame :
    ProperSubgame acceptLow ultimatumGame :=
  Subtree.trans_properSubgame acceptLow_subtree_lowOfferResponse
    lowOfferResponse_properSubgame

/-- The accepted high offer is a terminal subtree of the full game. -/
theorem acceptHigh_subtree_ultimatumGame :
    Subtree acceptHigh ultimatumGame :=
  Subtree.trans acceptHigh_subtree_highOfferResponse highOfferResponse_subtree

/-- The accepted high offer is a proper terminal subgame of the full game. -/
theorem acceptHigh_properSubgame_ultimatumGame :
    ProperSubgame acceptHigh ultimatumGame :=
  Subtree.trans_properSubgame acceptHigh_subtree_highOfferResponse
    highOfferResponse_properSubgame

/-- Rejection is a terminal subtree of the full game through the low-offer
    response node. -/
theorem reject_subtree_ultimatumGame :
    Subtree reject ultimatumGame :=
  Subtree.trans reject_subtree_lowOfferResponse lowOfferResponse_subtree

/-- Rejection is a proper terminal subgame of the full game through the
    low-offer response node. -/
theorem reject_properSubgame_ultimatumGame :
    ProperSubgame reject ultimatumGame :=
  Subtree.trans_properSubgame reject_subtree_lowOfferResponse
    lowOfferResponse_properSubgame

/-- Terminal accepted-low subgames have no proper subgames. -/
theorem acceptLow_hasOnlyRootSubgames :
    HasOnlyRootSubgames acceptLow := by
  unfold acceptLow terminal
  exact hasOnlyRootSubgames_Leaf (payoff 2 1)

/-- Terminal rejection subgames have no proper subgames. -/
theorem reject_hasOnlyRootSubgames :
    HasOnlyRootSubgames reject := by
  unfold reject terminal
  exact hasOnlyRootSubgames_Leaf (payoff 0 0)

/-- On the accepted-low terminal subgame, root Nash already implies
    root-scoped subgame perfection.  This instantiates the no-proper-subgames
    theorem on a concrete terminal branch. -/
theorem acceptLow_nash_to_spe_on {σ : Strategy Player ℤ}
    (hnash : IsNashAt σ acceptLow) :
    IsSubgamePerfectOn σ acceptLow :=
  hnash.toSubgamePerfectOn_of_hasOnlyRootSubgames acceptLow_hasOnlyRootSubgames

/-- On the rejection terminal subgame, root Nash already implies root-scoped
    subgame perfection. -/
theorem reject_nash_to_spe_on {σ : Strategy Player ℤ}
    (hnash : IsNashAt σ reject) :
    IsSubgamePerfectOn σ reject :=
  hnash.toSubgamePerfectOn_of_hasOnlyRootSubgames reject_hasOnlyRootSubgames

/-! ### Equilibrium facts from the `GameTree` library -/

/-- The ultimatum game has a pure subgame-perfect equilibrium by Kuhn's theorem. -/
theorem ultimatum_has_spe :
    ∃ σ : Strategy Player ℤ, IsSubgamePerfect σ :=
  Kuhn_exists_SPE

/-- The ultimatum game has a root-scoped subgame-perfect equilibrium. -/
theorem ultimatum_has_spe_on :
    ∃ σ : Strategy Player ℤ, IsSubgamePerfectOn σ ultimatumGame :=
  Kuhn_exists_SPE_on ultimatumGame

/-- The ultimatum game has a pure Nash equilibrium at the root. -/
theorem ultimatum_has_nash_at :
    ∃ σ : Strategy Player ℤ, IsNashAt σ ultimatumGame :=
  Kuhn_exists_NE ultimatumGame

/-- One pure strategy is subgame-perfect on every subtree of the ultimatum game. -/
theorem ultimatum_has_spe_on_every_subtree :
    ∃ σ : Strategy Player ℤ,
      ∀ s : GameTree Player ℤ,
        Subtree s ultimatumGame → IsSubgamePerfectOn σ s :=
  Kuhn_exists_SPE_on_subtrees ultimatumGame

/-- The same pure strategy is Nash at every subtree of the ultimatum game. -/
theorem ultimatum_has_nash_at_every_subtree :
    ∃ σ : Strategy Player ℤ,
      ∀ s : GameTree Player ℤ, Subtree s ultimatumGame → IsNashAt σ s :=
  Kuhn_exists_NE_on_subtrees ultimatumGame

/-- The canonical backward-induction strategy is subgame-perfect on the root. -/
theorem ultimatum_optStrategy_spe_on :
    IsSubgamePerfectOn (optStrategy : Strategy Player ℤ) ultimatumGame :=
  optStrategy_isSubgamePerfectOn ultimatumGame

/-- The canonical backward-induction strategy is Nash at the root. -/
theorem ultimatum_optStrategy_nash_at :
    IsNashAt (optStrategy : Strategy Player ℤ) ultimatumGame :=
  optStrategy_isNashAt ultimatumGame

/-- Root-scoped SPE restricts to the low-offer response subgame. -/
theorem ultimatum_optStrategy_spe_on_lowOfferResponse :
    IsSubgamePerfectOn (optStrategy : Strategy Player ℤ) lowOfferResponse :=
  optStrategy_isSubgamePerfectOn_properSubgame lowOfferResponse_properSubgame

/-- Root-scoped SPE restricts to the high-offer response subgame. -/
theorem ultimatum_optStrategy_spe_on_highOfferResponse :
    IsSubgamePerfectOn (optStrategy : Strategy Player ℤ) highOfferResponse :=
  optStrategy_isSubgamePerfectOn_properSubgame highOfferResponse_properSubgame

/-- The low-offer response subgame is Nash under the backward-induction
    strategy. -/
theorem ultimatum_optStrategy_nash_at_lowOfferResponse :
    IsNashAt (optStrategy : Strategy Player ℤ) lowOfferResponse :=
  optStrategy_isNashAt_properSubgame lowOfferResponse_properSubgame

/-- The high-offer response subgame is Nash under the backward-induction
    strategy. -/
theorem ultimatum_optStrategy_nash_at_highOfferResponse :
    IsNashAt (optStrategy : Strategy Player ℤ) highOfferResponse :=
  optStrategy_isNashAt_properSubgame highOfferResponse_properSubgame

/-- The backward-induction strategy is Nash at every subtree of the root. -/
theorem ultimatum_optStrategy_nash_at_every_subtree :
    ∀ s : GameTree Player ℤ, Subtree s ultimatumGame →
      IsNashAt (optStrategy : Strategy Player ℤ) s :=
  ultimatum_optStrategy_spe_on.forall_subtree_isNashAt

/-- Subgame perfection on the full ultimatum game decomposes into root Nash,
    SPE on the low-offer response subgame, and SPE on the high-offer response
    subgame. -/
theorem ultimatum_optStrategy_spe_on_decomposes :
    IsNashAt (optStrategy : Strategy Player ℤ) ultimatumGame ∧
      IsSubgamePerfectOn (optStrategy : Strategy Player ℤ) lowOfferResponse ∧
        ∀ c ∈ List.cons highOfferResponse List.nil,
          IsSubgamePerfectOn (optStrategy : Strategy Player ℤ) c := by
  change IsNashAt (optStrategy : Strategy Player ℤ)
      (Node Proposer lowOfferResponse (List.cons highOfferResponse List.nil)) ∧
    IsSubgamePerfectOn (optStrategy : Strategy Player ℤ) lowOfferResponse ∧
      ∀ c ∈ List.cons highOfferResponse List.nil,
        IsSubgamePerfectOn (optStrategy : Strategy Player ℤ) c
  exact
    (isSubgamePerfectOn_Node_iff
      (σ := (optStrategy : Strategy Player ℤ))
      (m := Proposer)
      (h := lowOfferResponse)
      (t := List.cons highOfferResponse List.nil)).mp
        (by simpa [ultimatumGame] using ultimatum_optStrategy_spe_on)

/-- Subgame perfection on the low-offer response node decomposes into Nash at
    that response node and SPE on both terminal branches. -/
theorem lowOfferResponse_optStrategy_spe_on_decomposes :
    IsNashAt (optStrategy : Strategy Player ℤ) lowOfferResponse ∧
      IsSubgamePerfectOn (optStrategy : Strategy Player ℤ) acceptLow ∧
        ∀ c ∈ List.cons reject List.nil,
          IsSubgamePerfectOn (optStrategy : Strategy Player ℤ) c := by
  change IsNashAt (optStrategy : Strategy Player ℤ)
      (Node Responder acceptLow (List.cons reject List.nil)) ∧
    IsSubgamePerfectOn (optStrategy : Strategy Player ℤ) acceptLow ∧
      ∀ c ∈ List.cons reject List.nil,
        IsSubgamePerfectOn (optStrategy : Strategy Player ℤ) c
  exact
    (isSubgamePerfectOn_Node_iff
      (σ := (optStrategy : Strategy Player ℤ))
      (m := Responder)
      (h := acceptLow)
      (t := List.cons reject List.nil)).mp
        (by simpa [lowOfferResponse] using ultimatum_optStrategy_spe_on_lowOfferResponse)

/-! ### Strategic-form extraction -/

/-- The extracted strategic-form game for the ultimatum tree. -/
noncomputable def ultimatumStrategicGame : StrategicGame Player ℤ :=
  toStrategicGame ultimatumGame

/-- The extracted strategic-form game has a pure Nash equilibrium, and the
    extracted profile corresponds to root-scoped Nash equilibrium in the
    original tree. -/
theorem ultimatum_strategic_form_has_nash :
    ∃ σ : ultimatumStrategicGame.Profile,
      _root_.IsNashEquilibrium ultimatumStrategicGame σ ∧
        IsNashAt (profileStrategy σ) ultimatumGame := by
  have hprofile :
      profileStrategy (fun _ => optStrategy : ultimatumStrategicGame.Profile) =
        (optStrategy : Strategy Player ℤ) := rfl
  refine ⟨fun _ => optStrategy, ?_, ?_⟩
  · exact (toStrategicGame_nash_iff_isNashAt ultimatumGame
      (fun _ => optStrategy)).mpr
      (by simpa [ultimatumStrategicGame, hprofile] using
        optStrategy_isSubgamePerfect.toNE ultimatumGame)
  · simpa [hprofile] using optStrategy_isSubgamePerfect.toNE ultimatumGame

end Examples.UltimatumGame
