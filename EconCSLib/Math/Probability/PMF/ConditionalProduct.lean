/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.Math.Probability.PMF.ConditionalSampling
import EconCSLib.Math.Probability.PMF.FiniteProduct

/-!
# EconCSLib.Math.Probability.PMF.ConditionalProduct

Conditional exposure of one coordinate of a finite independent dependent PMF
product.

The main theorem first observes a function of one selected coordinate, updates
only that coordinate law to its posterior fiber, and then samples the complete
dependent table.  This is exactly equivalent to sampling the complete table
up front and revealing the selected observation.  It is the playerwise product
step needed by mixed-to-behavioral execution: players' pure plans are
independent, while the actions inside one player's plan may be correlated.
-/

namespace PMF

universe uι uX uO uY

/-- Conditioning commutes with pushforward along an equivalence. -/
theorem conditionOnFiber_map_equiv
    {α β Observation : Type*}
    (p : PMF α)
    (e : α ≃ β)
    (observe : β → Observation)
    (observation : Observation) :
    (p.map e).conditionOnFiber
        observe observation =
      (p.conditionOnFiber
        (observe ∘ e) observation).map e := by
  classical
  have hpossible :
      (p.map e).FiberPossible
          observe observation ↔
        p.FiberPossible
          (observe ∘ e) observation := by
    rw [fiberPossible_iff_mem_support_map,
      fiberPossible_iff_mem_support_map,
      PMF.map_comp]
  by_cases hsource :
      p.FiberPossible
        (observe ∘ e) observation
  · have htarget :
        (p.map e).FiberPossible
          observe observation :=
      hpossible.mpr hsource
    ext value
    rw [(p.map e).conditionOnFiber_apply_of_possible
      observe observation htarget value]
    rw [PMF.map_equiv_apply]
    rw [p.conditionOnFiber_apply_of_possible
      (observe ∘ e) observation hsource
      (e.symm value)]
    rw [PMF.map_comp]
    by_cases hmem :
        observe value = observation
    · have htargetMem :
          value ∈ fiberSet observe observation :=
        hmem
      have hsourceMem :
          e.symm value ∈
            fiberSet (observe ∘ e) observation := by
        change
          observe (e (e.symm value)) =
            observation
        simpa using hmem
      rw [Set.indicator_of_mem htargetMem,
        Set.indicator_of_mem hsourceMem,
        PMF.map_equiv_apply]
    · have htargetNotMem :
          value ∉ fiberSet observe observation :=
        hmem
      have hsourceNotMem :
          e.symm value ∉
            fiberSet (observe ∘ e) observation := by
        intro hsourceMem
        apply hmem
        change
          observe (e (e.symm value)) =
            observation at hsourceMem
        simpa using hsourceMem
      rw [Set.indicator_of_notMem htargetNotMem,
        Set.indicator_of_notMem hsourceNotMem]
  · have htarget :
        ¬ (p.map e).FiberPossible
          observe observation :=
      fun h => hsource (hpossible.mp h)
    rw [(p.map e).conditionOnFiber_of_impossible
      observe observation htarget]
    rw [p.conditionOnFiber_of_impossible
      (observe ∘ e) observation hsource]

/-- The first marginal of an independent pair is its left component law. -/
theorem independentPair_map_fst
    {α β : Type*}
    (left : PMF α) (right : PMF β) :
    (independentPair left right).map Prod.fst =
      left := by
  unfold independentPair
  rw [PMF.map_bind]
  simp_rw [PMF.map_comp]
  change
    left.bind
        (fun value =>
          right.map (fun _ => value)) =
      left
  calc
    left.bind
        (fun value =>
          right.map (fun _ => value)) =
      left.bind PMF.pure := by
        apply congrArg
          (fun next => left.bind next)
        funext value
        simpa only [Function.const_apply] using
          (PMF.map_const
            (p := right) (b := value))
    _ = left :=
      PMF.bind_pure left

/-- Conditioning an independent pair on its first component updates only the
left law and preserves independence from the right law. -/
theorem independentPair_conditionOnFiber_fst
    {α β : Type*}
    (left : PMF α) (right : PMF β)
    (value : α) :
    (independentPair left right).conditionOnFiber
        Prod.fst value =
      independentPair
        (left.conditionOnFiber id value)
        right := by
  classical
  have hpossible :
      (independentPair left right).FiberPossible
          Prod.fst value ↔
        left.FiberPossible id value := by
    rw [fiberPossible_iff_mem_support_map,
      fiberPossible_iff_mem_support_map,
      independentPair_map_fst,
      PMF.map_id]
  by_cases hleft :
      left.FiberPossible id value
  · have hpair :
        (independentPair left right).FiberPossible
          Prod.fst value :=
      hpossible.mpr hleft
    ext outcome
    rw [(independentPair left right).conditionOnFiber_apply_of_possible
      Prod.fst value hpair outcome]
    rw [independentPair_map_fst]
    rw [independentPair_apply]
    rw [left.conditionOnFiber_apply_of_possible
      id value hleft outcome.1]
    have hindicator :
        (fiberSet Prod.fst value).indicator
            (independentPair left right) outcome =
          (fiberSet id value).indicator
              left outcome.1 *
            right outcome.2 := by
      by_cases heq : outcome.1 = value
      · have hpairMem :
            outcome ∈ fiberSet Prod.fst value :=
          heq
        have hleftMem :
            outcome.1 ∈ fiberSet id value := by
          simpa [fiberSet] using heq
        rw [Set.indicator_of_mem hpairMem,
          Set.indicator_of_mem hleftMem,
          independentPair_apply]
      · have hpairNotMem :
            outcome ∉ fiberSet Prod.fst value :=
          heq
        have hleftNotMem :
            outcome.1 ∉ fiberSet id value := by
          simpa [fiberSet] using heq
        rw [Set.indicator_of_notMem hpairNotMem,
          Set.indicator_of_notMem hleftNotMem]
        simp
    rw [hindicator]
    rw [PMF.map_id]
    ac_rfl
  · have hpair :
        ¬ (independentPair left right).FiberPossible
          Prod.fst value :=
      fun h => hleft (hpossible.mp h)
    rw [(independentPair left right).conditionOnFiber_of_impossible
      Prod.fst value hpair]
    rw [left.conditionOnFiber_of_impossible
      id value hleft]

/-- Expose an observation of one coordinate of a finite independent
dependent product, condition that coordinate on the observation, and continue
with the posterior complete table.

Only the selected coordinate law is updated.  All other coordinate laws remain
independent and unchanged. -/
theorem fintypePi_bind_conditionOnCoordinate
    {ι : Type uι} [Fintype ι] [DecidableEq ι]
    {X : ι → Type uX}
    {Observation : Type uO}
    {Y : Type uY}
    (laws : (i : ι) → PMF (X i))
    (selected : ι)
    (observe : X selected → Observation)
    (continuation :
      Observation →
        ((i : ι) → X i) →
          PMF Y) :
    ((laws selected).map observe).bind
        (fun observation =>
          (fintypePi
            (Function.update laws selected
              ((laws selected).conditionOnFiber
                observe observation))).bind
            (continuation observation)) =
      (fintypePi laws).bind
        (fun table =>
          continuation
            (observe (table selected))
            table) := by
  classical
  let split :
      ((i : ι) → X i) ≃
        X selected ×
          ((remaining : {i : ι // i ≠ selected}) →
            X remaining.1) :=
    Equiv.piSplitAt selected X
  let remainingLaw :
      PMF
        ((remaining : {i : ι // i ≠ selected}) →
          X remaining.1) :=
    fintypePi
      (fun remaining : {i : ι // i ≠ selected} =>
        laws remaining.1)
  have splitOriginal :
      (fintypePi laws).map split =
        independentPair
          (laws selected)
          remainingLaw := by
    exact
      fintypePi_map_piSplitAt laws selected
  have splitUpdated
      (selectedLaw : PMF (X selected)) :
      (fintypePi
        (Function.update laws selected
          selectedLaw)).map split =
        independentPair
          selectedLaw
          remainingLaw := by
    rw [fintypePi_map_piSplitAt]
    congr 1
    · simp
    · apply congrArg fintypePi
      funext remaining
      simp [remaining.property]
  have bindOriginal :
      (fintypePi laws).bind
          (fun table =>
            continuation
              (observe (table selected))
              table) =
        (laws selected).bind
          (fun selectedValue =>
            remainingLaw.bind
              (fun remaining =>
                continuation
                  (observe selectedValue)
                  (split.symm
                    (selectedValue, remaining)))) := by
    calc
      (fintypePi laws).bind
          (fun table =>
            continuation
              (observe (table selected))
              table) =
        ((fintypePi laws).map split).bind
          (fun separated =>
            continuation
              (observe separated.1)
              (split.symm separated)) := by
            rw [PMF.bind_map]
            apply congrArg
              (fun next =>
                (fintypePi laws).bind next)
            funext table
            change
              continuation
                  (observe (table selected)) table =
                continuation
                  (observe (split table).1)
                  (split.symm (split table))
            rw [split.symm_apply_apply]
            rfl
      _ = (independentPair
            (laws selected)
            remainingLaw).bind
          (fun separated =>
            continuation
              (observe separated.1)
              (split.symm separated)) := by
            rw [splitOriginal]
      _ = (laws selected).bind
          (fun selectedValue =>
            remainingLaw.bind
              (fun remaining =>
                continuation
                  (observe selectedValue)
                  (split.symm
                    (selectedValue, remaining)))) := by
            unfold independentPair
            rw [PMF.bind_bind]
            apply congrArg
              (fun next =>
                (laws selected).bind next)
            funext selectedValue
            rw [PMF.bind_map]
            rfl
  have bindUpdated
      (observation : Observation) :
      (fintypePi
        (Function.update laws selected
          ((laws selected).conditionOnFiber
            observe observation))).bind
          (continuation observation) =
        ((laws selected).conditionOnFiber
          observe observation).bind
            (fun selectedValue =>
              remainingLaw.bind
                (fun remaining =>
                  continuation observation
                    (split.symm
                      (selectedValue, remaining)))) := by
    let selectedLaw :=
      (laws selected).conditionOnFiber
        observe observation
    calc
      (fintypePi
        (Function.update laws selected
          selectedLaw)).bind
          (continuation observation) =
        ((fintypePi
          (Function.update laws selected
            selectedLaw)).map split).bind
          (fun separated =>
            continuation observation
              (split.symm separated)) := by
            rw [PMF.bind_map]
            apply congrArg
              (fun next =>
                (fintypePi
                  (Function.update laws selected
                    selectedLaw)).bind next)
            funext table
            change
              continuation observation table =
                continuation observation
                  (split.symm (split table))
            rw [split.symm_apply_apply]
      _ = (independentPair
            selectedLaw remainingLaw).bind
          (fun separated =>
            continuation observation
              (split.symm separated)) := by
            rw [splitUpdated selectedLaw]
      _ = selectedLaw.bind
          (fun selectedValue =>
            remainingLaw.bind
              (fun remaining =>
                continuation observation
                  (split.symm
                    (selectedValue, remaining)))) := by
            unfold independentPair
            rw [PMF.bind_bind]
            apply congrArg
              (fun next =>
                selectedLaw.bind next)
            funext selectedValue
            rw [PMF.bind_map]
            rfl
  calc
    ((laws selected).map observe).bind
        (fun observation =>
          (fintypePi
            (Function.update laws selected
              ((laws selected).conditionOnFiber
                observe observation))).bind
            (continuation observation)) =
      ((laws selected).map observe).bind
        (fun observation =>
          ((laws selected).conditionOnFiber
            observe observation).bind
              (fun selectedValue =>
                remainingLaw.bind
                  (fun remaining =>
                    continuation observation
                      (split.symm
                        (selectedValue, remaining))))) := by
      apply congrArg
        (fun next =>
          ((laws selected).map observe).bind
            next)
      funext observation
      exact bindUpdated observation
    _ = (laws selected).bind
        (fun selectedValue =>
          remainingLaw.bind
            (fun remaining =>
              continuation
                (observe selectedValue)
                (split.symm
                  (selectedValue, remaining)))) := by
      exact
        bind_map_bind_conditionOnFiber
          (laws selected) observe
          (fun observation selectedValue =>
            remainingLaw.bind
              (fun remaining =>
                continuation observation
                  (split.symm
                    (selectedValue, remaining))))
    _ = (fintypePi laws).bind
        (fun table =>
          continuation
            (observe (table selected))
            table) :=
      bindOriginal.symm

/-- Conditioning a finite independent dependent product on one coordinate
updates exactly that coordinate law. -/
theorem fintypePi_conditionOnFiber_apply
    {ι : Type uι} [Fintype ι] [DecidableEq ι]
    {X : ι → Type uX}
    (laws : (i : ι) → PMF (X i))
    (selected : ι)
    (value : X selected) :
    (fintypePi laws).conditionOnFiber
        (fun table => table selected)
        value =
      fintypePi
        (Function.update laws selected
          ((laws selected).conditionOnFiber
            id value)) := by
  classical
  let split :
      ((i : ι) → X i) ≃
        X selected ×
          ((remaining : {i : ι // i ≠ selected}) →
            X remaining.1) :=
    Equiv.piSplitAt selected X
  apply
    (show Function.Injective
        (fun probability :
          PMF ((i : ι) → X i) =>
            probability.map split) from by
      intro first second heq
      have hback :=
        congrArg
          (fun probability =>
            probability.map split.symm)
          heq
      dsimp only at hback
      rw [PMF.map_comp, PMF.map_comp] at hback
      have hcomp :
          split.symm ∘ split = id := by
        funext table
        exact split.symm_apply_apply table
      rw [hcomp] at hback
      rw [PMF.map_id, PMF.map_id] at hback
      exact hback)
  calc
    ((fintypePi laws).conditionOnFiber
        (fun table => table selected)
        value).map split =
      ((fintypePi laws).map split).conditionOnFiber
        Prod.fst value := by
          rw [conditionOnFiber_map_equiv]
          rfl
    _ = (independentPair
          (laws selected)
          (fintypePi
            (fun remaining : {i : ι // i ≠ selected} =>
              laws remaining.1))).conditionOnFiber
            Prod.fst value := by
      rw [fintypePi_map_piSplitAt]
    _ = independentPair
          ((laws selected).conditionOnFiber
            id value)
          (fintypePi
            (fun remaining : {i : ι // i ≠ selected} =>
              laws remaining.1)) := by
      rw [independentPair_conditionOnFiber_fst]
    _ = (fintypePi
          (Function.update laws selected
            ((laws selected).conditionOnFiber
              id value))).map split := by
      rw [fintypePi_map_piSplitAt]
      congr 1
      · simp
      · apply congrArg fintypePi
        funext remaining
        simp [remaining.property]

end PMF
