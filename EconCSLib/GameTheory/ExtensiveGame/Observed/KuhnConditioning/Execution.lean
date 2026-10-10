/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Observed.KuhnConditioning.Core
import EconCSLib.GameTheory.ExtensiveGame.Observed.DeferredSampling.Execution

/-!
# EconCSLib.GameTheory.ExtensiveGame.Observed.KuhnConditioning.Execution

Sequential posterior execution and root-scoped payoff-law equality.
-/

namespace ExtensiveGame.ObservedChanceGame

variable {N U : Type*} (G : ObservedChanceGame N U)

private theorem FiniteLaw.bind_conditionOnFiber_map_pair
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (law : FiniteLaw α) (observe : α → β)
    (offPath : β → FiniteLaw α) :
    ((law.map observe).bind fun value =>
      ((law.conditionOnFiber observe value).getD
        (offPath value)).map fun sample => (value, sample)).Equivalent
      (law.map fun sample => (observe sample, sample)) := by
  apply FiniteLaw.Equivalent.of_mass_eq
  rintro ⟨value, sample⟩
  rw [FiniteLaw.mass_bind]
  rw [FiniteLaw.map_atoms]
  simp only [List.map_map, Function.comp_def]
  simp_rw [FiniteLaw.mass, FiniteLaw.eventMass_map]
  let posterior : β → FiniteLaw α :=
    fun target =>
      (law.conditionOnFiber observe target).getD (offPath target)
  change
    (law.atoms.map fun atom =>
      atom.2 *
        ((posterior (observe atom.1)).eventMass
          (fun candidate => decide
            ((observe atom.1, candidate) = (value, sample))))).sum =
      law.eventMass (fun candidate => decide
        ((observe candidate, candidate) = (value, sample)))
  have hfactor (target : β) (posteriorMass : ℚ≥0) :
      (law.atoms.map fun atom =>
        atom.2 * if observe atom.1 = target then posteriorMass else 0).sum =
        law.eventMass (fun sample => decide (observe sample = target)) *
          posteriorMass := by
    unfold FiniteLaw.eventMass
    induction law.atoms with
    | nil => simp
    | cons atom atoms ih =>
        simp only [List.map_cons, List.sum_cons]
        rw [ih]
        by_cases heq : observe atom.1 = target
        · simp [heq, add_mul]
        · simp [heq]
  have hsum :
      (law.atoms.map fun atom =>
        atom.2 *
          ((posterior (observe atom.1)).eventMass
            (fun candidate => decide
              ((observe atom.1, candidate) = (value, sample))))).sum =
        law.eventMass (fun candidate => decide (observe candidate = value)) *
          (posterior value).mass sample := by
    rw [← hfactor value
      ((posterior value).mass sample)]
    apply congrArg List.sum
    apply List.map_congr_left
    intro atom _
    rcases atom with ⟨candidate, weight⟩
    by_cases hatom : observe candidate = value
    · simp [hatom, FiniteLaw.mass, FiniteLaw.eventMass]
    · simp [hatom, FiniteLaw.eventMass]
  have hright :
      law.eventMass (fun candidate =>
        decide ((observe candidate, candidate) = (value, sample))) =
        if observe sample = value then law.mass sample else 0 := by
    by_cases hvalue : observe sample = value
    · rw [if_pos hvalue]
      unfold FiniteLaw.mass FiniteLaw.eventMass
      apply congrArg List.sum
      apply List.map_congr_left
      intro atom _
      rcases atom with ⟨candidate, weight⟩
      by_cases hsample : candidate = sample
      · subst candidate
        simp [hvalue]
      · simp [hsample]
    · rw [if_neg hvalue]
      unfold FiniteLaw.eventMass
      apply List.sum_eq_zero
      intro term hterm
      rw [List.mem_map] at hterm
      obtain ⟨atom, _, rfl⟩ := hterm
      rcases atom with ⟨candidate, weight⟩
      by_cases hsample : candidate = sample
      · subst candidate
        simp [hvalue]
      · simp [hsample]
  rw [hsum, hright]
  let marginal :=
    law.eventMass (fun candidate => decide (observe candidate = value))
  cases hcondition : law.conditionOnFiber observe value with
  | none =>
      have hzero : marginal = 0 := by
        unfold FiniteLaw.conditionOnFiber at hcondition
        exact (FiniteLaw.condition?_eq_none_iff law _).1 hcondition
      dsimp [posterior]
      simp only [hcondition, Option.getD]
      change marginal * (offPath value).mass sample = _
      by_cases hvalue : observe sample = value
      · rw [if_pos hvalue, hzero, zero_mul]
        have hsampleZero : law.mass sample = 0 := by
          dsimp [marginal] at hzero
          unfold FiniteLaw.mass FiniteLaw.eventMass at hzero ⊢
          have hlist : ∀ atoms : List (α × ℚ≥0),
              (atoms.map fun atom =>
                if decide (observe atom.1 = value) then atom.2 else 0).sum = 0 →
              (atoms.map fun atom =>
                if decide (atom.1 = sample) then atom.2 else 0).sum = 0 := by
            intro atoms
            induction atoms with
            | nil => simp
            | cons atom atoms ih =>
                rcases atom with ⟨candidate, weight⟩
                intro htotal
                simp only [List.map_cons, List.sum_cons] at htotal ⊢
                let head :=
                  if decide (observe candidate = value) then weight else 0
                let tail :=
                  (atoms.map fun atom =>
                    if decide (observe atom.1 = value) then atom.2 else 0).sum
                have htotal' : head + tail = 0 := by
                  simpa [head, tail] using htotal
                have hcast :=
                  congrArg (fun q : ℚ≥0 => (q : ℚ)) htotal'
                simp only [NNRat.coe_add, NNRat.coe_zero] at hcast
                have hpartsCast : (head : ℚ) = 0 ∧ (tail : ℚ) = 0 :=
                  (add_eq_zero_iff_of_nonneg
                    (NNRat.coe_nonneg head) (NNRat.coe_nonneg tail)).mp hcast
                have hhead : head = 0 :=
                  NNRat.coe_eq_zero.mp hpartsCast.1
                have htail : tail = 0 :=
                  NNRat.coe_eq_zero.mp hpartsCast.2
                rw [ih htail]
                by_cases heq : candidate = sample
                · subst candidate
                  simpa [head, hvalue] using hhead
                · simp [heq]
          simpa [Function.comp_def] using hlist law.atoms hzero
        exact hsampleZero.symm
      · simp [hvalue, hzero]
  | some conditioned =>
      have hnonzero : marginal ≠ 0 := by
        intro hzero
        have hnone : law.conditionOnFiber observe value = none := by
          unfold FiniteLaw.conditionOnFiber
          exact (FiniteLaw.condition?_eq_none_iff law _).2 hzero
        rw [hcondition] at hnone
        exact Option.some_ne_none _ hnone
      dsimp [posterior]
      simp only [hcondition, Option.getD]
      change marginal * conditioned.mass sample = _
      rw [FiniteLaw.mass_conditionOnFiber law observe value conditioned
        hcondition sample]
      by_cases hvalue : observe sample = value
      · simp only [if_pos hvalue]
        dsimp [marginal]
        apply mul_div_cancel₀
        exact hnonzero
      · simp [hvalue]

private theorem FiniteLaw.bind_map_bind_conditionOnFiber
    {α β γ : Type*} [DecidableEq α] [DecidableEq β]
    (law : FiniteLaw α) (observe : α → β)
    (offPath : β → FiniteLaw α)
    (continuation : β → α → FiniteLaw γ) :
    ((law.map observe).bind fun value =>
      ((law.conditionOnFiber observe value).getD
        (offPath value)).bind (continuation value)).Equivalent
      (law.bind fun sample => continuation (observe sample) sample) := by
  let jointContinuation : β × α → FiniteLaw γ :=
    fun outcome => continuation outcome.1 outcome.2
  apply FiniteLaw.Equivalent.trans
    (second :=
      (law.map observe).bind fun value =>
        (((law.conditionOnFiber observe value).getD
          (offPath value)).map fun sample =>
            (value, sample)).bind jointContinuation)
  · apply (FiniteLaw.Equivalent.refl (law.map observe)).bind
    intro value
    apply FiniteLaw.Equivalent.of_eq
    rw [FiniteLaw.bind_map]
    rfl
  apply FiniteLaw.Equivalent.trans
    (second :=
      ((law.map observe).bind fun value =>
        ((law.conditionOnFiber observe value).getD
          (offPath value)).map fun sample =>
            (value, sample)).bind jointContinuation)
  · exact FiniteLaw.Equivalent.of_eq
      (FiniteLaw.bind_bind (law.map observe) _ jointContinuation).symm
  apply FiniteLaw.Equivalent.trans
    (second :=
      (law.map fun sample => (observe sample, sample)).bind
        jointContinuation)
  · exact (FiniteLaw.bind_conditionOnFiber_map_pair
      law observe offPath).bind
      (fun _ => FiniteLaw.Equivalent.refl _)
  exact FiniteLaw.Equivalent.of_eq (by
    rw [FiniteLaw.bind_map]
    rfl)

private theorem FiniteLaw.bind_pure_const_equivalent
    {α β : Type*} (law : FiniteLaw α) (value : β) :
    (law.bind fun _ => FiniteLaw.pure value).Equivalent
      (FiniteLaw.pure value) := by
  intro observable
  change
    (law.bind fun _ => FiniteLaw.pure value).expectRat observable =
      (FiniteLaw.pure value).expectRat observable
  rw [FiniteLaw.expectRat_bind, FiniteLaw.expectRat_pure]
  exact FiniteLaw.expectRat_const law (observable value)

private theorem FiniteLaw.fintypePi_conditionOnFiber_observe
    {ι : Type*} [Fintype ι] [LinearOrder ι]
    {X : ι → Type*} [∀ i, DecidableEq (X i)]
    [DecidableEq ((i : ι) → X i)]
    {Observation : Type*} [DecidableEq Observation]
    (laws : (i : ι) → FiniteLaw (X i))
    (selected : ι) (observe : X selected → Observation)
    (observation : Observation)
    (offPath : FiniteLaw (X selected)) :
    (((FiniteLaw.fintypePi laws).conditionOnFiber
      (fun tuple => observe (tuple selected)) observation).getD
        (FiniteLaw.fintypePi
          (Function.update laws selected offPath))).Equivalent
      (FiniteLaw.fintypePi
        (Function.update laws selected
          ((laws selected).conditionOnFiber
            observe observation |>.getD offPath))) := by
  classical
  let selectedEvent : X selected → Bool :=
    fun outcome => decide (observe outcome = observation)
  have heventMass :
      (FiniteLaw.fintypePi laws).eventMass
          (fun tuple => decide (observe (tuple selected) = observation)) =
        (laws selected).eventMass selectedEvent := by
    have hmarginal :=
      ((FiniteLaw.fintypePi_map_apply laws selected).map observe).eventMass
        (fun outcome => decide (outcome = observation))
    rw [FiniteLaw.eventMass_map, FiniteLaw.eventMass_map,
      FiniteLaw.eventMass_map] at hmarginal
    simpa [selectedEvent, Function.comp_def] using hmarginal
  cases hselected :
      (laws selected).conditionOnFiber observe observation with
  | none =>
      have hselectedZero :
          (laws selected).eventMass selectedEvent = 0 := by
        unfold FiniteLaw.conditionOnFiber at hselected
        exact (FiniteLaw.condition?_eq_none_iff (laws selected) _).1 hselected
      have hproductZero :
          (FiniteLaw.fintypePi laws).eventMass
              (fun tuple => decide
                (observe (tuple selected) = observation)) = 0 := by
        rw [heventMass, hselectedZero]
      have hproduct :
          (FiniteLaw.fintypePi laws).conditionOnFiber
              (fun tuple => observe (tuple selected)) observation = none := by
        unfold FiniteLaw.conditionOnFiber
        exact (FiniteLaw.condition?_eq_none_iff
          (FiniteLaw.fintypePi laws) _).2 hproductZero
      simpa [hselected, hproduct] using
        FiniteLaw.Equivalent.refl
          (FiniteLaw.fintypePi
            (Function.update laws selected offPath))
  | some selectedLaw =>
      have hselectedNonzero :
          (laws selected).eventMass selectedEvent ≠ 0 := by
        intro hzero
        have hnone :
            (laws selected).conditionOnFiber observe observation = none := by
          unfold FiniteLaw.conditionOnFiber
          exact (FiniteLaw.condition?_eq_none_iff (laws selected) _).2 hzero
        rw [hselected] at hnone
        exact Option.some_ne_none _ hnone
      have hproductNonzero :
          (FiniteLaw.fintypePi laws).eventMass
              (fun tuple => decide
                (observe (tuple selected) = observation)) ≠ 0 := by
        rw [heventMass]
        exact hselectedNonzero
      have hproductSome :
          (FiniteLaw.fintypePi laws).conditionOnFiber
              (fun tuple => observe (tuple selected)) observation ≠ none := by
        intro hnone
        unfold FiniteLaw.conditionOnFiber at hnone
        exact hproductNonzero
          ((FiniteLaw.condition?_eq_none_iff
            (FiniteLaw.fintypePi laws) _).1 hnone)
      obtain ⟨productLaw, hproduct⟩ :=
        Option.ne_none_iff_exists'.mp hproductSome
      simp only [hproduct, Option.getD]
      apply FiniteLaw.Equivalent.of_mass_eq
      intro tuple
      rw [FiniteLaw.mass_conditionOnFiber
          (FiniteLaw.fintypePi laws)
          (fun tuple => observe (tuple selected)) observation
          productLaw hproduct tuple,
        FiniteLaw.fintypePi_mass, heventMass,
        Fintype.prod_eq_mul_prod_subtype_ne _ selected]
      have hrest :
          (∏ i : {i : ι // i ≠ selected},
            (Function.update laws selected selectedLaw i.1).mass
              (tuple i.1)) =
            ∏ i : {i : ι // i ≠ selected},
              (laws i.1).mass (tuple i.1) := by
        apply Finset.prod_congr rfl
        intro i _
        unfold Function.update
        split
        · rename_i heq
          exact (i.2 heq).elim
        · rfl
      have hupdatedProduct :
          (∏ i : ι,
            (Function.update laws selected selectedLaw i).mass
              (tuple i)) =
            selectedLaw.mass (tuple selected) *
              ∏ i : {i : ι // i ≠ selected},
                (laws i.1).mass (tuple i.1) := by
        rw [Fintype.prod_eq_mul_prod_subtype_ne _ selected]
        rw [show Function.update laws selected selectedLaw selected =
            selectedLaw by simp [Function.update], hrest]
      rw [FiniteLaw.fintypePi_mass
          (Function.update laws selected selectedLaw) tuple,
        hupdatedProduct,
        FiniteLaw.mass_conditionOnFiber
          (laws selected) observe observation selectedLaw hselected]
      change
        (if observe (tuple selected) = observation then
            ((laws selected).mass (tuple selected) *
              ∏ i : {i : ι // i ≠ selected},
                (laws i.1).mass (tuple i.1)) /
                  (laws selected).eventMass selectedEvent
          else 0) =
          (if observe (tuple selected) = observation then
              (laws selected).mass (tuple selected) /
                (laws selected).eventMass selectedEvent
            else 0) *
              ∏ i : {i : ι // i ≠ selected},
                (laws i.1).mass (tuple i.1)
      by_cases heq : observe (tuple selected) = observation
      · simp [heq, div_mul_eq_mul_div]
      · simp [heq]

private lemma FiniteLaw.exists_conditionOnFiber_of_positive
    {α β : Type*} [DecidableEq β] (law : FiniteLaw α)
    (observe : α → β) (value : β)
    (hpositive : (law.map observe).HasPositiveAtom value) :
    ∃ conditioned, law.conditionOnFiber observe value = some conditioned := by
  obtain ⟨sample, ⟨weight, hmem, hweight⟩, hvalue⟩ :=
    (FiniteLaw.hasPositiveAtom_map_iff observe law value).mp hpositive
  have hweight_le : (weight : ℚ) ≤
      (law.eventMass (fun candidate => decide (observe candidate = value)) : ℚ) := by
    rw [FiniteLaw.eventMass, NNRat.cast_listSum]
    apply List.single_le_sum (by
      intro term hterm
      obtain ⟨weight, _, rfl⟩ := List.mem_map.mp hterm
      exact NNRat.coe_nonneg weight)
    apply List.mem_map.mpr
    refine ⟨weight, ?_, rfl⟩
    exact List.mem_map.mpr ⟨(sample, weight), hmem, by simp [hvalue]⟩
  have hmass : law.eventMass (fun candidate => decide (observe candidate = value)) ≠ 0 := by
    intro hzero
    rw [hzero, NNRat.coe_zero] at hweight_le
    exact hweight (NNRat.coe_eq_zero.mp
      (le_antisymm hweight_le (NNRat.coe_nonneg weight)))
  exact Option.ne_none_iff_exists'.mp fun hnone =>
    hmass ((FiniteLaw.condition?_eq_none_iff law _).mp hnone)

set_option maxHeartbeats 800000 in
/-- Sequential posterior exposure of arbitrary mixed pure plans has exactly
the same bounded complete-history law as the root-scoped conditional
behavioral profile.

The theorem is strengthened over every suffix whose playerwise posterior is
present.  Its source law samples the supplied successful posterior plans
independently; its target keeps one behavioral strategy fixed from the original
root.  The caller-supplied behavioral profile is used only at information
states where conditioning is absent.  This is the induction invariant needed
for exact mixed-to-behavioral realization. -/
theorem posteriorMixedHistoryLawAlong_eq_behavioral
    [Fintype N] [LinearOrder N]
    [∀ (i : N) (information : G.observed.RepresentedInfo i),
      DecidableEq
        (G.observed.InfoAction i information.1)]
    [(state : G.observed.base.State) →
      Decidable
        (G.observed.base.isTerminal state)]
    (certificate : G.observed.RecallCertificate)
    (profile : G.observed.MixedProfile)
    (offPath : G.observed.BehavioralProfile)
    (root :
      G.observed.base.toArena.HistoryFrom
        G.observed.base.init)
    {finish : G.observed.base.State}
    (suffix :
      G.observed.base.toArena.History
        root.1 finish)
    (posteriorProfile : G.observed.MixedProfile)
    (hposterior :
      ∀ i,
        profile.posteriorAfterDecisions
            G.observed
            (G.observed.relativeOwnDecisionHistories
              root
              ⟨finish, root.2.append suffix⟩) i =
          some (posteriorProfile i))
    (fuel : ℕ) :
    let current :
        G.observed.base.toArena.HistoryFrom
          G.observed.base.init :=
      ⟨finish, root.2.append suffix⟩
    ((posteriorProfile.pureProfileLaw G.observed).bind
      (fun pureProfile =>
        G.observed.base.toArena.stochasticHistoryLawFrom
          (BehavioralProfile.toHistoryPolicy G
            (pureProfile.toBehavioral G.observed))
          current fuel)).Equivalent
      (G.observed.base.toArena.stochasticHistoryLawFrom
          (BehavioralProfile.toHistoryPolicy G
            (certificate.behavioralizeMixedProfileFrom
              G.observed root profile offPath))
        current fuel) := by
  classical
  induction fuel generalizing finish posteriorProfile with
  | zero =>
      simpa [Arena.stochasticHistoryLawFrom] using
        FiniteLaw.bind_pure_const_equivalent
          (posteriorProfile.pureProfileLaw G.observed)
          (⟨finish, root.2.append suffix⟩ :
            G.observed.base.toArena.HistoryFrom G.observed.base.init)
  | succ fuel ih =>
      let current :
          G.observed.base.toArena.HistoryFrom
            G.observed.base.init :=
        ⟨finish, root.2.append suffix⟩
      let behavioralProfile :
          G.observed.BehavioralProfile :=
        certificate.behavioralizeMixedProfileFrom
          G.observed root profile offPath
      change
        ((posteriorProfile.pureProfileLaw
          G.observed).bind
            (fun pureProfile =>
              G.observed.base.toArena.stochasticHistoryLawFrom
                (BehavioralProfile.toHistoryPolicy G
                  (pureProfile.toBehavioral
                    G.observed))
                current (fuel + 1))).Equivalent
          (G.observed.base.toArena.stochasticHistoryLawFrom
            (BehavioralProfile.toHistoryPolicy G
              behavioralProfile)
            current (fuel + 1))
      by_cases hterminal :
          G.observed.base.isTerminal current.1
      · simpa [Arena.stochasticHistoryLawFrom, hterminal] using
          FiniteLaw.bind_pure_const_equivalent
            (posteriorProfile.pureProfileLaw G.observed) current
      · rw [G.observed.base.toArena.stochasticHistoryLawFrom_succ_of_not_terminal
          (BehavioralProfile.toHistoryPolicy G
            behavioralProfile)
          current fuel hterminal]
        simp_rw [Arena.stochasticHistoryLawFrom,
          dif_neg hterminal]
        cases hmover :
            G.observed.base.mover current.1 with
        | none =>
            have hchanceSource
                (pureProfile :
                  G.observed.PureProfile) :
                BehavioralProfile.toHistoryPolicy
                    G
                    (pureProfile.toBehavioral
                      G.observed)
                    current hterminal =
                  G.chanceKernel current
                    ⟨hmover, hterminal⟩ :=
              BehavioralProfile.toHistoryPolicy_of_chance
                G
                (pureProfile.toBehavioral
                  G.observed)
                current hterminal hmover
            have hchanceTarget :
                BehavioralProfile.toHistoryPolicy
                    G behavioralProfile
                    current hterminal =
                  G.chanceKernel current
                    ⟨hmover, hterminal⟩ :=
              BehavioralProfile.toHistoryPolicy_of_chance
                G behavioralProfile
                current hterminal hmover
            simp_rw [hchanceSource]
            rw [hchanceTarget]
            apply FiniteLaw.Equivalent.trans
              (second :=
                (G.chanceKernel current
                  ⟨hmover, hterminal⟩).bind fun action =>
                    (posteriorProfile.pureProfileLaw G.observed).bind
                      fun pureProfile =>
                        G.observed.base.toArena.stochasticHistoryLawFrom
                          (BehavioralProfile.toHistoryPolicy G
                            (pureProfile.toBehavioral G.observed))
                          ⟨G.observed.base.next finish action,
                            root.2.append (suffix.snoc action)⟩ fuel)
            · exact FiniteLaw.bind_comm_equivalent
                (posteriorProfile.pureProfileLaw G.observed)
                (G.chanceKernel current ⟨hmover, hterminal⟩)
                (fun pureProfile action =>
                  G.observed.base.toArena.stochasticHistoryLawFrom
                    (BehavioralProfile.toHistoryPolicy G
                      (pureProfile.toBehavioral G.observed))
                    ⟨G.observed.base.next finish action,
                      root.2.append (suffix.snoc action)⟩ fuel)
            apply (FiniteLaw.Equivalent.refl
              (G.chanceKernel current ⟨hmover, hterminal⟩)).bind
            intro action
            have hrelative :
                G.observed.relativeOwnDecisionHistories
                    root
                    ⟨G.observed.base.next
                        finish action,
                      (root.2.append suffix).snoc
                        action⟩ =
                  G.observed.relativeOwnDecisionHistories
                    root current := by
              funext i
              apply
                (G.observed.relativeOwnDecisionHistories_snoc_of_not_mover
                  root suffix action i)
              simp [current, hmover]
            have hposteriorAction :
                ∀ j,
                  profile.posteriorAfterDecisions
                      G.observed
                      (G.observed.relativeOwnDecisionHistories
                        root
                        ⟨G.observed.base.next finish action,
                          root.2.append (suffix.snoc action)⟩) j =
                    some (posteriorProfile j) := by
              intro j
              rw [Arena.History.append_snoc, hrelative]
              exact hposterior j
            have ihAction :=
              ih
                (suffix := suffix.snoc action)
                (posteriorProfile := posteriorProfile)
                hposteriorAction
            dsimp only at ihAction
            change
              ((posteriorProfile.pureProfileLaw
                G.observed).bind
                  (fun pureProfile =>
                    G.observed.base.toArena.stochasticHistoryLawFrom
                      (BehavioralProfile.toHistoryPolicy G
                        (pureProfile.toBehavioral
                          G.observed))
                      ⟨G.observed.base.next
                          finish action,
                        root.2.append
                          (suffix.snoc action)⟩
                      fuel)).Equivalent
                (G.observed.base.toArena.stochasticHistoryLawFrom
                  (BehavioralProfile.toHistoryPolicy G
                    behavioralProfile)
                  ⟨G.observed.base.next
                      finish action,
                    root.2.append
                      (suffix.snoc action)⟩
                  fuel)
            simpa [behavioralProfile, current,
              Arena.History.append_snoc] using
                ihAction
        | some i =>
            have hmover' :
                G.observed.base.mover finish =
                  some i := by
              simpa [current] using hmover
            have hnonterminal' :
                ¬ G.observed.base.isTerminal finish := by
              simpa [current] using hterminal
            let hdecision :=
              G.observed.base.toArena.isDecision_of_not_isTerminal
                current.1 hterminal
            let hdecision' :=
              G.observed.base.toArena.isDecision_of_not_isTerminal
                finish hnonterminal'
            let information :=
              G.observed.representedInfoAt
                current i hmover hdecision
            let abstractToConcrete :=
              G.observed.actionEquiv
                current i hmover hdecision
            let currentPlanLaw :
                FiniteLaw
                  (G.observed.PureStrategy i) :=
              posteriorProfile i
            have hposteriorAtCurrent :
                (profile i).posteriorAfterDecisions
                    G.observed
                    (G.observed.relativeOwnDecisionHistories
                      root
                      ⟨finish, root.2.append suffix⟩ i) =
                  some currentPlanLaw := by
              simpa [ObservedGame.MixedProfile.posteriorAfterDecisions,
                currentPlanLaw, current] using hposterior i
            have hpureStep
                (pureProfile :
                  G.observed.PureProfile) :
                BehavioralProfile.toHistoryPolicy
                    G
                    (pureProfile.toBehavioral
                      G.observed)
                    current hterminal =
                  FiniteLaw.pure
                    (abstractToConcrete
                      (pureProfile i
                        information)) := by
              simpa [abstractToConcrete,
                information] using
                G.pureProfile_toBehavioral_toHistoryPolicy_of_mover
                  pureProfile current hterminal
                  i hmover
            simp_rw [hpureStep, FiniteLaw.pure_bind]
            have htargetAction :
                BehavioralProfile.toHistoryPolicy
                    G behavioralProfile
                    current hterminal =
                  (currentPlanLaw.map
                    (fun pureStrategy =>
                      pureStrategy information)).map
                        abstractToConcrete := by
              rw [BehavioralProfile.toHistoryPolicy_of_mover
                G behavioralProfile current
                hterminal i hmover]
              unfold
                ObservedGame.BehavioralProfile.actionLawAt
                ObservedGame.BehavioralStrategy.actionLawAt
                ControlledObservedGame.BehavioralStrategy.actionLawAt
              dsimp only
              change
                (certificate.behavioralizeMixedFrom
                    G.observed root i (profile i)
                    (offPath i)
                    information).map
                      abstractToConcrete =
                  _
              rw [certificate.behavioralizeMixedFrom_at_append
                G.observed root suffix i hmover' hdecision'
                (profile i) (offPath i)]
              change
                (((profile i).posteriorAfterDecisions
                    G.observed
                    (G.observed.relativeOwnDecisionHistories
                      root current i)).map
                  (fun conditioned =>
                    conditioned.map fun pureStrategy =>
                      pureStrategy information) |>.getD
                    (offPath i information)).map abstractToConcrete = _
              rw [show
                (profile i).posteriorAfterDecisions
                    G.observed
                    (G.observed.relativeOwnDecisionHistories
                      root current i) = some currentPlanLaw by
                  simpa [current] using hposteriorAtCurrent]
              rfl
            rw [htargetAction, FiniteLaw.bind_map]
            let continuation :
                G.observed.InfoAction i information.1 →
                  G.observed.PureProfile →
                    FiniteLaw
                      (G.observed.base.toArena.HistoryFrom
                        G.observed.base.init) :=
              fun abstractAction pureProfile =>
                G.observed.base.toArena.stochasticHistoryLawFrom
                  (BehavioralProfile.toHistoryPolicy G
                    (pureProfile.toBehavioral
                      G.observed))
                  ⟨G.observed.base.next
                      finish
                      (abstractToConcrete
                        abstractAction),
                    root.2.append
                      (suffix.snoc
                        (abstractToConcrete
                          abstractAction))⟩
                  fuel
            let disintegrationFallback :
                FiniteLaw G.observed.PureProfile :=
              FiniteLaw.fintypePi
                (Function.update posteriorProfile i currentPlanLaw)
            have hdisintegrate :=
              FiniteLaw.bind_map_bind_conditionOnFiber
                (FiniteLaw.fintypePi posteriorProfile)
                (fun pureProfile =>
                  pureProfile i information)
                (fun _ => disintegrationFallback)
                continuation
            have hmarginal :
                ((FiniteLaw.fintypePi posteriorProfile).map
                  (fun pureProfile =>
                    pureProfile i information)).Equivalent
                  (currentPlanLaw.map
                    (fun pureStrategy =>
                      pureStrategy information)) := by
              simpa [FiniteLaw.map_comp, Function.comp_def,
                currentPlanLaw] using
                (FiniteLaw.fintypePi_map_apply
                  posteriorProfile i).map
                    (fun pureStrategy =>
                      pureStrategy information)
            change
              ((posteriorProfile.pureProfileLaw
                G.observed).bind
                  (fun pureProfile =>
                    continuation
                      (pureProfile i information)
                      pureProfile)).Equivalent
                ((currentPlanLaw.map
                  (fun pureStrategy =>
                    pureStrategy information)).bind
                  (fun abstractAction =>
                    G.observed.base.toArena.stochasticHistoryLawFrom
                      (BehavioralProfile.toHistoryPolicy G
                        behavioralProfile)
                      ⟨G.observed.base.next
                          finish
                          (abstractToConcrete
                            abstractAction),
                        root.2.append
                          (suffix.snoc
                          (abstractToConcrete
                            abstractAction))⟩
                      fuel))
            unfold
              ObservedGame.MixedProfile.pureProfileLaw
            refine hdisintegrate.symm.trans ?_
            refine (hmarginal.bind
              (fun _ => FiniteLaw.Equivalent.refl _)).trans ?_
            apply (currentPlanLaw.map
              (fun pureStrategy =>
                pureStrategy information)).bind_congr_positive
            intro abstractAction hpositive
            obtain ⟨conditionedPlanLaw, hconditioned⟩ :=
              FiniteLaw.exists_conditionOnFiber_of_positive currentPlanLaw
                (fun pureStrategy => pureStrategy information) abstractAction hpositive
            let updatedProfile : G.observed.MixedProfile :=
              Function.update posteriorProfile i conditionedPlanLaw
            have hconditionRaw :=
              FiniteLaw.fintypePi_conditionOnFiber_observe
                posteriorProfile i
                (fun pureStrategy =>
                  pureStrategy information)
                abstractAction
                currentPlanLaw
            have hcondition :
                (((FiniteLaw.fintypePi posteriorProfile).conditionOnFiber
                    (fun pureProfile =>
                      pureProfile i information)
                    abstractAction).getD
                  disintegrationFallback).Equivalent
                (FiniteLaw.fintypePi updatedProfile) := by
              simpa [disintegrationFallback, updatedProfile,
                currentPlanLaw, hconditioned] using hconditionRaw
            have hposteriorUpdate :=
              profile.posteriorAfterDecisions_relative_snoc_of_mover
                G.observed root suffix i hmover' hdecision'
                abstractAction
            have hposteriorNext :
                ∀ j,
                  profile.posteriorAfterDecisions
                      G.observed
                      (G.observed.relativeOwnDecisionHistories
                        root
                        ⟨G.observed.base.next finish
                            (abstractToConcrete abstractAction),
                          root.2.append
                            (suffix.snoc
                              (abstractToConcrete abstractAction))⟩) j =
                    some (updatedProfile j) := by
              intro j
              rw [hposteriorUpdate j]
              by_cases hji : j = i
              · subst j
                simp only [updatedProfile, Function.update_self]
                rw [hposteriorAtCurrent, Option.bind_some]
                simpa [information, current] using hconditioned
              · simp only [updatedProfile,
                  Function.update_of_ne hji]
                exact hposterior j
            have ihAction :=
              ih
                (suffix :=
                  suffix.snoc
                    (abstractToConcrete
                      abstractAction))
                (posteriorProfile := updatedProfile)
                hposteriorNext
            dsimp only at ihAction
            unfold
              ObservedGame.MixedProfile.pureProfileLaw
                at ihAction
            refine hcondition.bind
              (fun _ => FiniteLaw.Equivalent.refl _) |>.trans ?_
            simpa [updatedProfile, currentPlanLaw, information,
              abstractToConcrete,
              behavioralProfile, current,
              continuation,
              Arena.History.append_snoc] using ihAction

/-- From the selected root itself, an arbitrary mixed profile and its
root-scoped conditional behavioralization have identical bounded complete
history laws. -/
theorem mixedToBehavioral_stoppedHistoryLawFrom
    [Fintype N] [LinearOrder N]
    [∀ (i : N) (information : G.observed.RepresentedInfo i),
      DecidableEq
        (G.observed.InfoAction i information.1)]
    [(state : G.observed.base.State) →
      Decidable
        (G.observed.base.isTerminal state)]
    (certificate : G.observed.RecallCertificate)
    (profile : G.observed.MixedProfile)
    (offPath : G.observed.BehavioralProfile)
    (current :
      G.observed.base.toArena.HistoryFrom
        G.observed.base.init)
    (fuel : ℕ) :
    (G.mixedStoppedHistoryLawFrom
        profile current fuel).Equivalent
      (G.observed.base.toArena.stochasticHistoryLawFrom
        (BehavioralProfile.toHistoryPolicy G
          (certificate.behavioralizeMixedProfileFrom
            G.observed current profile offPath))
        current fuel) := by
  have hrelative :
      G.observed.relativeOwnDecisionHistories
          current current =
        fun _ => [] := by
    funext i
    exact
      G.observed.relativeOwnDecisionHistories_self
        current i
  have hposteriorRoot :
      ∀ i,
        profile.posteriorAfterDecisions
            G.observed
            (G.observed.relativeOwnDecisionHistories
              current current) i =
          some (profile i) := by
    intro i
    rw [hrelative]
    rfl
  have hrealization :=
    G.posteriorMixedHistoryLawAlong_eq_behavioral
      certificate profile offPath current
      (Arena.History.nil :
        G.observed.base.toArena.History
          current.1 current.1)
      profile hposteriorRoot fuel
  dsimp only at hrealization
  rw [Arena.History.append_nil] at hrealization
  simpa [mixedStoppedHistoryLawFrom]
    using hrealization

/-- Finite rational mixed-to-behavioral realization at every finite
execution depth, without a finite information-state hypothesis.

This is the implemented Kuhn boundary beyond finite information carriers.
The mixed carrier is a `FiniteLaw` over complete pure plans, the player type
is finite, and the conclusion is `FiniteLaw.Equivalent` of bounded
complete-history laws at one selected root.
The theorem permits infinitely many information states and arbitrarily long
plays, but it does not assert equality of an infinite path measure or an
arbitrary-measure realization. See [Kuhn 1953, §4 and Thm. 4] for the finite
perfect-recall theorem and `docs/design/efg-infinite-kuhn-boundary.md` for the
representation boundary. -/
theorem finiteLawMixedToBehavioral_boundedHistoryLaw
    [Fintype N] [LinearOrder N]
    [∀ (i : N) (information : G.observed.RepresentedInfo i),
      DecidableEq
        (G.observed.InfoAction i information.1)]
    [(state : G.observed.base.State) →
      Decidable
        (G.observed.base.isTerminal state)]
    (certificate : G.observed.RecallCertificate)
    (profile : G.observed.MixedProfile)
    (offPath : G.observed.BehavioralProfile)
    (current :
      G.observed.base.toArena.HistoryFrom
        G.observed.base.init)
    (fuel : ℕ) :
    (G.mixedStoppedHistoryLawFrom profile current fuel).Equivalent
      (G.observed.base.toArena.stochasticHistoryLawFrom
        (BehavioralProfile.toHistoryPolicy G
          (certificate.behavioralizeMixedProfileFrom
            G.observed current profile offPath))
        current fuel) :=
  G.mixedToBehavioral_stoppedHistoryLawFrom
    certificate profile offPath current fuel

/-- Root-scoped conditional behavioralization preserves the complete bounded
optional-payoff law of every arbitrary mixed profile. -/
theorem mixedToBehavioral_stoppedPayoffLawFrom
    [Fintype N] [LinearOrder N]
    [∀ (i : N) (information : G.observed.RepresentedInfo i),
      DecidableEq
        (G.observed.InfoAction i information.1)]
    [(state : G.observed.base.State) →
      Decidable
        (G.observed.base.isTerminal state)]
    (certificate : G.observed.RecallCertificate)
    (profile : G.observed.MixedProfile)
    (offPath : G.observed.BehavioralProfile)
    (current :
      G.observed.base.toArena.HistoryFrom
        G.observed.base.init)
    (fuel : ℕ) :
    (G.mixedStoppedPayoffLawFrom
        profile current fuel).Equivalent
      (G.behavioralStoppedPayoffLawFrom
        (certificate.behavioralizeMixedProfileFrom
          G.observed current profile offPath)
        current fuel) := by
  apply FiniteLaw.Equivalent.trans
    (second := (G.mixedStoppedHistoryLawFrom
      profile current fuel).map G.stoppedPayoffAtHistory)
  · exact FiniteLaw.Equivalent.of_eq
      (G.mixedStoppedPayoffLawFrom_eq_map_history
        profile current fuel)
  exact (G.mixedToBehavioral_stoppedHistoryLawFrom
    certificate profile offPath current fuel).map G.stoppedPayoffAtHistory


end ExtensiveGame.ObservedChanceGame
