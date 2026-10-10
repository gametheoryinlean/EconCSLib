/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Execution.StochasticExecution
import EconCSLib.GameTheory.ExtensiveGame.Relations.Discrete.Morphism

/-!
# Naturality of bounded stochastic history execution

This relation-side module proves exact FiniteLaw naturality under a strict
isomorphism of complete-history unfoldings. The execution implementation
therefore remains independent of the higher Arena relation hierarchy.
-/

namespace ExtensiveGame.Arena.Iso

variable {A B : Arena} {sourceStart : A.State}
  {targetStart : B.State}

/-- Exact naturality of bounded stochastic execution under a strict
isomorphism of complete-history unfoldings. -/
theorem map_stochasticHistoryLawFrom
    [(state : A.State) → Decidable (A.IsTerminal state)]
    [(state : B.State) → Decidable (B.IsTerminal state)]
    (e :
      (A.unfoldFrom sourceStart).Iso
        (B.unfoldFrom targetStart))
    (sourcePolicy : A.StochasticHistoryPolicy sourceStart)
    (targetPolicy : B.StochasticHistoryPolicy targetStart)
    (hpolicy :
      ∀ (history : A.HistoryFrom sourceStart)
        (hsource : ¬ A.IsTerminal history.1)
        (htarget :
          ¬ B.IsTerminal (e.stateEquiv history).1),
        (sourcePolicy history hsource).map
            (e.actionEquiv history) =
          targetPolicy (e.stateEquiv history) htarget)
    (current : A.HistoryFrom sourceStart) :
    ∀ fuel,
      (A.stochasticHistoryLawFrom
          sourcePolicy current fuel).map e.stateEquiv =
        B.stochasticHistoryLawFrom
          targetPolicy (e.stateEquiv current) fuel := by
  intro fuel
  induction fuel generalizing current with
  | zero =>
      exact FiniteLaw.pure_map e.stateEquiv current
  | succ fuel ih =>
      by_cases hsource : A.IsTerminal current.1
      · have htarget :
            B.IsTerminal (e.stateEquiv current).1 :=
          (e.isTerminal_iff current).mp hsource
        rw [A.stochasticHistoryLawFrom_succ_of_terminal
          sourcePolicy current fuel hsource]
        rw [B.stochasticHistoryLawFrom_succ_of_terminal
          targetPolicy (e.stateEquiv current)
          fuel htarget]
        exact FiniteLaw.pure_map e.stateEquiv current
      · have htarget :
            ¬ B.IsTerminal (e.stateEquiv current).1 :=
          not_congr (e.isTerminal_iff current) |>.mp hsource
        rw [A.stochasticHistoryLawFrom_succ_of_not_terminal
          sourcePolicy current fuel hsource]
        rw [B.stochasticHistoryLawFrom_succ_of_not_terminal
          targetPolicy (e.stateEquiv current)
          fuel htarget]
        let sourceLaw := sourcePolicy current hsource
        let targetContinuation :=
          fun action =>
            B.stochasticHistoryLawFrom targetPolicy
              ⟨B.next (e.stateEquiv current).1 action,
                (e.stateEquiv current).2.snoc action⟩
              fuel
        calc
          (sourceLaw.bind
              (fun action =>
                A.stochasticHistoryLawFrom sourcePolicy
                  ⟨A.next current.1 action,
                    current.2.snoc action⟩
                  fuel)).map e.stateEquiv =
            sourceLaw.bind
              (fun action =>
                (A.stochasticHistoryLawFrom sourcePolicy
                    ⟨A.next current.1 action,
                      current.2.snoc action⟩
                    fuel).map e.stateEquiv) :=
              FiniteLaw.map_bind sourceLaw
                (fun action =>
                  A.stochasticHistoryLawFrom sourcePolicy
                    ⟨A.next current.1 action,
                      current.2.snoc action⟩ fuel)
                e.stateEquiv
          _ = sourceLaw.bind
              (fun action =>
                B.stochasticHistoryLawFrom targetPolicy
                  (e.stateEquiv
                    ⟨A.next current.1 action,
                      current.2.snoc action⟩)
                  fuel) := by
            apply congrArg (fun continuation =>
              sourceLaw.bind continuation)
            funext action
            exact ih
              ⟨A.next current.1 action,
                current.2.snoc action⟩
          _ = sourceLaw.bind
              (targetContinuation ∘
                e.actionEquiv current) := by
            apply congrArg (fun continuation =>
              sourceLaw.bind continuation)
            funext action
            unfold targetContinuation
            apply congrArg
              (fun next =>
                B.stochasticHistoryLawFrom
                  targetPolicy next fuel)
            exact e.map_next current action
          _ = (sourceLaw.map
                (e.actionEquiv current)).bind
              targetContinuation :=
            (FiniteLaw.bind_map sourceLaw
              (e.actionEquiv current)
              targetContinuation).symm
          _ = (targetPolicy
                (e.stateEquiv current) htarget).bind
              targetContinuation := by
            rw [hpolicy current hsource htarget]
            rfl

end ExtensiveGame.Arena.Iso
