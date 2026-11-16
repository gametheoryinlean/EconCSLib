/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Execution.StochasticExecution

/-!
# Executable complete paths from bounded finite execution

This module turns a bounded `FiniteLaw` of complete Arena histories into a
finite law of terminal-absorbing paths. A path stores no infinite array: it is
a computable function that reads the retained finite history and holds its
terminal endpoint after that history is exhausted.

The construction itself needs only a decidable terminal test. Its correctness
theorems take an explicit bounded-termination certificate for the positive
atoms at the chosen horizon. Zero-weight unfinished atoms may remain in the
sparse representation, but no legality claim is made for them. Every positive
path keeps the incoming absolute history and action occurrences, is terminal
at the supplied horizon, and has the same finite-coordinate laws as the
original executor.

No measure, integral, infinite sampler, or choice principle is used here.
-/

namespace Arena

variable {A : Arena} {start : A.State}

/-- A transition is legal for terminal-absorbing stochastic execution when it
either stays at a terminal history or appends an action with positive policy
mass at a nonterminal history. -/
def IsLegalAbsorbingTransition
    [(state : A.State) → Decidable (A.IsTerminal state)]
    (policy : A.StochasticHistoryPolicy start)
    (current next : A.HistoryFrom start) : Prop :=
  (A.IsTerminal current.1 ∧ next = current) ∨
    ∃ hnonterminal : ¬ A.IsTerminal current.1,
      ∃ action,
        (policy current hnonterminal).HasPositiveAtom action ∧
        next = ⟨A.next current.1 action, current.2.snoc action⟩

namespace FiniteCompletePath

section Replay

/-- Read an absolute history prefix, holding its endpoint after exhaustion. -/
def prefixAt : {finish : A.State} → A.History start finish → ℕ → A.HistoryFrom start
  | _, .nil, _ => Arena.HistoryFrom.nil A start
  | _, .snoc history action, n =>
      if n ≤ history.length then prefixAt history n
      else ⟨_, history.snoc action⟩

private theorem prefixAt_of_length_le {finish : A.State}
    (history : A.History start finish) (n : ℕ) (h : history.length ≤ n) :
    prefixAt history n = ⟨finish, history⟩ := by
  cases history with
  | nil => rfl
  | snoc history action =>
      simp only [Arena.History.length_snoc] at h
      simp [prefixAt, show ¬ n ≤ history.length by omega]

private theorem prefixAt_append {middle finish : A.State}
    (history : A.History start middle) (suffix : A.History middle finish)
    (n : ℕ) (h : n ≤ history.length) :
    prefixAt (history.append suffix) n = prefixAt history n := by
  induction suffix with
  | nil => rfl
  | snoc suffix action ih =>
      simp only [Arena.History.append_snoc, prefixAt]
      rw [if_pos (by simp only [Arena.History.length_append]; omega), ih]

private theorem prependHistory_at_le {finish : A.State}
    (history : A.History start finish)
    (play : A.CompletePlayFromHistory ⟨finish, history⟩)
    (n : ℕ) (h : n ≤ history.length) :
    (Arena.CompletePlayFromHistory.prependHistory history play).historyAt n =
      prefixAt history n := by
  induction history generalizing n with
  | nil =>
      have : n = 0 := by simpa using h
      subst n
      exact play.historyAt_zero
  | snoc history action ih =>
      by_cases hn : n ≤ history.length
      · simpa only [Arena.CompletePlayFromHistory.prependHistory, prefixAt,
          if_pos hn] using ih _ n hn
      · have hn' : n = (history.snoc action).length + 0 := by
          simp only [Arena.History.length_snoc] at h ⊢
          omega
        rw [hn', Arena.CompletePlayFromHistory.prependHistory_at_add,
          play.historyAt_zero, prefixAt_of_length_le _ _ (by omega)]

private theorem prefixAt_eq_stutterReplay {finish : A.State}
    (history : A.History start finish) (ht : A.IsTerminal finish) (n : ℕ) :
    prefixAt history n =
      (Arena.CompletePlayFromHistory.prependHistory history
        (Arena.CompletePlayFromHistory.stutter ⟨finish, history⟩ ht)).historyAt n := by
  by_cases h : n ≤ history.length
  · exact (prependHistory_at_le history _ n h).symm
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (by omega : history.length ≤ n)
    rw [Arena.CompletePlayFromHistory.prependHistory_at_add]
    exact prefixAt_of_length_le _ _ (by omega)

end Replay

section Execution

variable [(state : A.State) → Decidable (A.IsTerminal state)]

private theorem prefixAt_current (policy : A.StochasticHistoryPolicy start)
    (current final : A.HistoryFrom start) (horizon : ℕ)
    (hfinal : (A.stochasticHistoryLawFrom policy current horizon).HasPositiveAtom final) :
    prefixAt final.2 current.2.length = current := by
  obtain ⟨suffix, hsuffix⟩ :=
    A.exists_suffix_of_hasPositiveAtom_stochasticHistoryLawFrom
      policy current final horizon hfinal
  rw [hsuffix, prefixAt_append _ _ _ (le_refl _)]
  exact prefixAt_of_length_le _ _ (le_refl _)

/-- Execute to `horizon` and replay every stored finite history on demand.

The returned `FiniteLaw` is executable even though its outcomes are functions:
the sparse law never compares paths for equality, and each coordinate reduces
to a finite history lookup. -/
def law (policy : A.StochasticHistoryPolicy start)
    (current : A.HistoryFrom start) (horizon : ℕ) :
    FiniteLaw (ℕ → A.HistoryFrom start) :=
  (A.stochasticHistoryLawFrom policy current horizon).map
    (fun final n => prefixAt final.2 (current.2.length + n))

/-- Every positive replay starts at the actual incoming complete history. -/
theorem law_initial (policy : A.StochasticHistoryPolicy start)
    (current : A.HistoryFrom start) (horizon : ℕ)
    (path : ℕ → A.HistoryFrom start)
    (hpath : (law policy current horizon).HasPositiveAtom path) :
    path 0 = current := by
  obtain ⟨final, hfinal, rfl⟩ := (FiniteLaw.hasPositiveAtom_map_iff _ _ _).mp hpath
  simpa using prefixAt_current policy current final horizon hfinal

/-- Under a bounded positive-support termination certificate, every path
coordinate has the same law as direct execution to that coordinate. This also
holds after the supplied horizon because both processes absorb at terminals. -/
theorem law_marginal (policy : A.StochasticHistoryPolicy start)
    (current : A.HistoryFrom start) (horizon : ℕ)
    (terminated : ∀ final,
      (A.stochasticHistoryLawFrom policy current horizon).HasPositiveAtom final →
        A.IsTerminal final.1) (n : ℕ) :
    ((law policy current horizon).map (fun path => path n)).Equivalent
      (A.stochasticHistoryLawFrom policy current n) := by
  intro value
  change ((law policy current horizon).map (fun path => path n)).expectRat value =
    (A.stochasticHistoryLawFrom policy current n).expectRat value
  simp only [law, FiniteLaw.expectRat_map, Function.comp_def]
  induction horizon generalizing current n with
  | zero =>
      have ht := terminated current ((FiniteLaw.hasPositiveAtom_pure_iff _ _).mpr rfl)
      rw [A.stochasticHistoryLawFrom_zero,
        A.stochasticHistoryLawFrom_of_terminal policy current ht]
      simp only [FiniteLaw.expectRat_pure]
      rw [prefixAt_of_length_le _ _ (by omega)]
  | succ horizon ih =>
      by_cases ht : A.IsTerminal current.1
      · rw [A.stochasticHistoryLawFrom_of_terminal policy current ht,
          A.stochasticHistoryLawFrom_of_terminal policy current ht]
        simp only [FiniteLaw.expectRat_pure]
        rw [prefixAt_of_length_le _ _ (by omega)]
      · cases n with
        | zero =>
            rw [A.stochasticHistoryLawFrom_zero, FiniteLaw.expectRat_pure]
            calc
              _ = (A.stochasticHistoryLawFrom policy current (horizon + 1)).expectRat
                  (fun _ => value current) := by
                apply FiniteLaw.expectRat_congr_positive
                intro final hfinal
                simp only [Nat.add_zero, prefixAt_current policy current final _ hfinal]
              _ = value current := FiniteLaw.expectRat_const _ _
        | succ n =>
            rw [A.stochasticHistoryLawFrom_succ_of_not_terminal policy current horizon ht,
              A.stochasticHistoryLawFrom_succ_of_not_terminal policy current n ht,
              FiniteLaw.expectRat_bind, FiniteLaw.expectRat_bind]
            apply FiniteLaw.expectRat_congr_positive
            intro action ha
            have hb : ∀ final,
                (A.stochasticHistoryLawFrom policy
                  ⟨A.next current.1 action, current.2.snoc action⟩ horizon).HasPositiveAtom final →
                    A.IsTerminal final.1 := by
              intro final hf
              apply terminated final
              rw [A.stochasticHistoryLawFrom_succ_of_not_terminal policy current horizon ht]
              exact (FiniteLaw.hasPositiveAtom_bind_iff _ _ _).mpr ⟨action, ha, hf⟩
            simpa only [Arena.History.length_snoc, Nat.add_assoc, Nat.add_left_comm,
              Nat.add_comm] using ih _ hb n

private theorem replay_legalTransition (policy : A.StochasticHistoryPolicy start)
    (current final : A.HistoryFrom start) (horizon : ℕ)
    (hfinal : (A.stochasticHistoryLawFrom policy current horizon).HasPositiveAtom final)
    (ht : A.IsTerminal final.1) (n : ℕ) :
    Arena.IsLegalAbsorbingTransition policy
      (prefixAt final.2 (current.2.length + n))
      (prefixAt final.2 (current.2.length + (n + 1))) := by
  induction horizon generalizing current n with
  | zero =>
      have heq := (FiniteLaw.hasPositiveAtom_pure_iff _ _).mp hfinal
      subst final
      have hp (k : ℕ) : prefixAt current.2 (current.2.length + k) = current :=
        prefixAt_of_length_le _ _ (Nat.le_add_right _ _)
      rw [hp, hp]
      exact Or.inl ⟨ht, rfl⟩
  | succ horizon ih =>
      by_cases hc : A.IsTerminal current.1
      · rw [A.stochasticHistoryLawFrom_of_terminal policy current hc] at hfinal
        have heq := (FiniteLaw.hasPositiveAtom_pure_iff _ _).mp hfinal
        subst final
        have hp (k : ℕ) : prefixAt current.2 (current.2.length + k) = current :=
          prefixAt_of_length_le _ _ (Nat.le_add_right _ _)
        rw [hp, hp]
        exact Or.inl ⟨hc, rfl⟩
      · have hf := hfinal
        rw [A.stochasticHistoryLawFrom_succ_of_not_terminal policy current horizon hc] at hf
        obtain ⟨action, ha, hf⟩ := (FiniteLaw.hasPositiveAtom_bind_iff _ _ _).mp hf
        cases n with
        | zero =>
            have hnext := prefixAt_current policy
              ⟨A.next current.1 action, current.2.snoc action⟩ final horizon hf
            simp only [Arena.History.length_snoc] at hnext
            simp only [Nat.add_zero, prefixAt_current policy current final _ hfinal, hnext]
            exact Or.inr ⟨hc, action, ha, rfl⟩
        | succ n =>
            simpa only [Arena.History.length_snoc, Nat.add_assoc, Nat.add_left_comm,
              Nat.add_comm] using ih _ hf n

/-- Every positive replay uses only positive-policy actions, and terminal
coordinates absorb. -/
theorem law_legalTransition (policy : A.StochasticHistoryPolicy start)
    (current : A.HistoryFrom start) (horizon : ℕ)
    (terminated : ∀ final,
      (A.stochasticHistoryLawFrom policy current horizon).HasPositiveAtom final →
        A.IsTerminal final.1)
    (path : ℕ → A.HistoryFrom start)
    (hpath : (law policy current horizon).HasPositiveAtom path) (n : ℕ) :
    Arena.IsLegalAbsorbingTransition policy (path n) (path (n + 1)) := by
  obtain ⟨final, hf, rfl⟩ := (FiniteLaw.hasPositiveAtom_map_iff _ _ _).mp hpath
  exact replay_legalTransition policy current final horizon hf (terminated final hf) n

/-- Every positive replay is a canonical complete legal play from the supplied
absolute history. -/
theorem law_legal (policy : A.StochasticHistoryPolicy start)
    (current : A.HistoryFrom start) (horizon : ℕ)
    (terminated : ∀ final,
      (A.stochasticHistoryLawFrom policy current horizon).HasPositiveAtom final →
        A.IsTerminal final.1)
    (path : ℕ → A.HistoryFrom start)
    (hpath : (law policy current horizon).HasPositiveAtom path) :
    A.IsCompletePlayPathFrom current path := by
  refine ⟨law_initial policy current horizon path hpath, ?_⟩
  obtain ⟨final, hf, rfl⟩ := (FiniteLaw.hasPositiveAtom_map_iff _ _ _).mp hpath
  intro n
  simp only [prefixAt_eq_stutterReplay final.2 (terminated final hf)]
  simpa only [Nat.add_assoc] using
    (Arena.CompletePlayFromHistory.prependHistory final.2
      (Arena.CompletePlayFromHistory.stutter final (terminated final hf))).step
        (current.2.length + n)

private theorem length_le_of_positive (policy : A.StochasticHistoryPolicy start)
    (current final : A.HistoryFrom start) (horizon : ℕ)
    (hf : (A.stochasticHistoryLawFrom policy current horizon).HasPositiveAtom final) :
    final.2.length ≤ current.2.length + horizon := by
  induction horizon generalizing current with
  | zero =>
      have heq := (FiniteLaw.hasPositiveAtom_pure_iff _ _).mp hf
      subst final
      omega
  | succ horizon ih =>
      by_cases ht : A.IsTerminal current.1
      · rw [A.stochasticHistoryLawFrom_of_terminal policy current ht] at hf
        have heq := (FiniteLaw.hasPositiveAtom_pure_iff _ _).mp hf
        subst final
        omega
      · rw [A.stochasticHistoryLawFrom_succ_of_not_terminal policy current horizon ht] at hf
        obtain ⟨action, _, hf⟩ := (FiniteLaw.hasPositiveAtom_bind_iff _ _ _).mp hf
        have h := ih _ hf
        simp only [Arena.History.length_snoc] at h
        omega

/-- Every positive replay is terminal at the supplied horizon. -/
theorem law_terminal (policy : A.StochasticHistoryPolicy start)
    (current : A.HistoryFrom start) (horizon : ℕ)
    (terminated : ∀ final,
      (A.stochasticHistoryLawFrom policy current horizon).HasPositiveAtom final →
        A.IsTerminal final.1)
    (path : ℕ → A.HistoryFrom start)
    (hpath : (law policy current horizon).HasPositiveAtom path) :
    A.IsTerminal (path horizon).1 := by
  obtain ⟨final, hf, rfl⟩ := (FiniteLaw.hasPositiveAtom_map_iff _ _ _).mp hpath
  change A.IsTerminal (prefixAt final.2 (current.2.length + horizon)).1
  rw [prefixAt_of_length_le _ _ (length_le_of_positive policy current final horizon hf)]
  exact terminated final hf

end Execution

end FiniteCompletePath
end Arena
