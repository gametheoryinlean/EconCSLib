/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.Examples.ExtensiveGame.FiniteLawIntegral
import EconCSLib.GameTheory.ExtensiveGame.Execution.InfiniteTrajectory

/-!
# Finite complete paths under a bounded termination hypothesis

This opt-in prototype executes a finite-support history policy to a supplied
horizon, then replays each resulting complete history and holds its last value.
Coordinates are computed on demand, with the absolute length of the incoming
history retained. No infinite array or equality decision on paths is needed.

The termination hypothesis concerns only positive atoms at the given horizon.
Zero-weight nonterminal atoms may remain in the sparse presentation; no legal
complete play is fabricated for them. Under the hypothesis all positive paths
are legal and absorbing, and every coordinate law agrees with the original
executor, including coordinates beyond the supplied horizon.

Finite path data remain executable. Their weighted Dirac interpretation and
the certificates for the existing supplied-law interface occur downstream in
theorems. This example does not change the general infinite execution API.
-/

open MeasureTheory

namespace Examples.ExtensiveGame.FiniteCompletePath

section Replay

variable {A : Arena} {start : A.State}

/-- Read an absolute history prefix, holding the endpoint after exhaustion. -/
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

variable {A : Arena} {start : A.State}
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

/-- Execute to the horizon and replay the stored finite histories on demand.
Only positive atoms are claimed to be complete legal paths under termination.
In particular, a zero-weight unfinished history is never bundled as a play. -/
def completePaths (policy : A.StochasticHistoryPolicy start)
    (current : A.HistoryFrom start) (horizon : ℕ) :
    FiniteLaw (ℕ → A.HistoryFrom start) :=
  (A.stochasticHistoryLawFrom policy current horizon).map
    (fun final n => prefixAt final.2 (current.2.length + n))

/-- Positive paths start at the actual incoming history, including its actions. -/
theorem completePaths_initial (policy : A.StochasticHistoryPolicy start)
    (current : A.HistoryFrom start) (horizon : ℕ)
    (path : ℕ → A.HistoryFrom start)
    (hpath : (completePaths policy current horizon).HasPositiveAtom path) :
    path 0 = current := by
  obtain ⟨final, hfinal, rfl⟩ := (FiniteLaw.hasPositiveAtom_map_iff _ _ _).mp hpath
  simpa using prefixAt_current policy current final horizon hfinal

/-- The supplied bound suffices for all natural-number marginals, both before
and after the bound. Sparse representation equality is deliberately not required. -/
theorem completePaths_marginal (policy : A.StochasticHistoryPolicy start)
    (current : A.HistoryFrom start) (horizon : ℕ)
    (terminated : ∀ final,
      (A.stochasticHistoryLawFrom policy current horizon).HasPositiveAtom final →
        A.IsTerminal final.1) (n : ℕ) :
    ((completePaths policy current horizon).map (fun path => path n)).Equivalent
      (A.stochasticHistoryLawFrom policy current n) := by
  intro value
  change ((completePaths policy current horizon).map (fun path => path n)).expectRat value =
    (A.stochasticHistoryLawFrom policy current n).expectRat value
  simp only [completePaths, FiniteLaw.expectRat_map, Function.comp_def]
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

/-- Every positive path uses only positive-policy actions, and terminal
coordinates absorb. No legality is claimed for a zero-mass branch. -/
theorem completePaths_legalTransition (policy : A.StochasticHistoryPolicy start)
    (current : A.HistoryFrom start) (horizon : ℕ)
    (terminated : ∀ final,
      (A.stochasticHistoryLawFrom policy current horizon).HasPositiveAtom final →
        A.IsTerminal final.1)
    (path : ℕ → A.HistoryFrom start)
    (hpath : (completePaths policy current horizon).HasPositiveAtom path) (n : ℕ) :
    Arena.IsLegalAbsorbingTransition policy (path n) (path (n + 1)) := by
  obtain ⟨final, hf, rfl⟩ := (FiniteLaw.hasPositiveAtom_map_iff _ _ _).mp hpath
  exact replay_legalTransition policy current final horizon hf (terminated final hf) n

/-- The replay is a canonical complete play. This identifies the algorithm
with `prependHistory` followed by terminal `stutter`, shifted by the actual
incoming history length. -/
theorem completePaths_legal (policy : A.StochasticHistoryPolicy start)
    (current : A.HistoryFrom start) (horizon : ℕ)
    (terminated : ∀ final,
      (A.stochasticHistoryLawFrom policy current horizon).HasPositiveAtom final →
        A.IsTerminal final.1)
    (path : ℕ → A.HistoryFrom start)
    (hpath : (completePaths policy current horizon).HasPositiveAtom path) :
    A.IsCompletePlayPathFrom current path := by
  refine ⟨completePaths_initial policy current horizon path hpath, ?_⟩
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

/-- Every positive path is terminal at the supplied horizon. -/
theorem completePaths_terminal (policy : A.StochasticHistoryPolicy start)
    (current : A.HistoryFrom start) (horizon : ℕ)
    (terminated : ∀ final,
      (A.stochasticHistoryLawFrom policy current horizon).HasPositiveAtom final →
        A.IsTerminal final.1)
    (path : ℕ → A.HistoryFrom start)
    (hpath : (completePaths policy current horizon).HasPositiveAtom path) :
    A.IsTerminal (path horizon).1 := by
  obtain ⟨final, hf, rfl⟩ := (FiniteLaw.hasPositiveAtom_map_iff _ _ _).mp hpath
  change A.IsTerminal (prefixAt final.2 (current.2.length + horizon)).1
  rw [prefixAt_of_length_le _ _ (length_le_of_positive policy current final horizon hf)]
  exact terminated final hf

end Execution

local notation "μ[" atoms "]" =>
  List.foldr (fun (atom : _ × ℚ≥0) rest =>
    ((Prod.snd atom : ℚ≥0) : ENNReal) • Measure.dirac (Prod.fst atom) + rest) 0 atoms

section MeasureInterpretation

private theorem measure_map {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (law : FiniteLaw α) (f : α → β) (hf : Measurable f) :
    (μ[law.atoms]).map f = μ[(law.map f).atoms] := by
  change (μ[law.atoms]).map f = μ[law.atoms.map (fun atom => (f atom.1, atom.2))]
  induction law.atoms with
  | nil => simp
  | cons atom atoms ih =>
      simp only [List.foldr_cons, List.map_cons, Measure.map_add _ _ hf,
        Measure.map_smul, Measure.map_dirac' hf, ih]

private theorem ae_of_positive {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] (law : FiniteLaw α) (p : α → Prop)
    (hp : ∀ x, law.HasPositiveAtom x → p x) : ∀ᵐ x ∂μ[law.atoms], p x := by
  have aux (atoms : List (α × ℚ≥0))
      (h : ∀ atom ∈ atoms, atom.2 ≠ 0 → p atom.1) : ∀ᵐ x ∂μ[atoms], p x := by
    induction atoms with
    | nil => simp
    | cons atom atoms ih =>
        rw [List.foldr_cons, ae_add_measure_iff]
        refine ⟨?_, ih (fun a ha => h a (by simp [ha]))⟩
        by_cases hz : atom.2 = 0
        · simp [hz, ← ENNReal.coe_nnratCast]
        · apply Measure.ae_smul_measure
          simpa only [ae_dirac_eq, Filter.eventually_pure] using
            h atom (by simp) hz
  exact aux law.atoms (fun atom ha hz => hp atom.1 ⟨atom.2, ha, hz⟩)

variable {A : Arena} {start : A.State}
variable [(state : A.State) → Decidable (A.IsTerminal state)]
variable [MeasurableSpace (A.HistoryFrom start)]

/-- The actual finite weighted Dirac path measure has the executor's coordinate
measures at every time. Only coordinate projection must be measurable here. -/
theorem measure_finiteMarginal (policy : A.StochasticHistoryPolicy start)
    (current : A.HistoryFrom start) (horizon : ℕ)
    (terminated : ∀ final,
      (A.stochasticHistoryLawFrom policy current horizon).HasPositiveAtom final →
        A.IsTerminal final.1) (n : ℕ) :
    (μ[(completePaths policy current horizon).atoms]).map (fun path => path n) =
      μ[(A.stochasticHistoryLawFrom policy current n).atoms] := by
  rw [measure_map _ _ (measurable_pi_apply n)]
  exact FiniteLawIntegral.measure_eq_of_equivalent
    (completePaths_marginal policy current horizon terminated n)

variable [MeasurableSingletonClass (A.HistoryFrom start)]

/-- Construct the existing supplied-law interface's probability measure and
all coherence certificates from the finite algorithm. The only termination
input is the positive-atom bound; neither a measure nor realization is assumed.
The measure is explicitly the weighted Dirac interpretation of `completePaths`.
Measurable singletons make arbitrary predicates valid almost surely at atoms. -/
theorem exists_pathLaw (policy : A.StochasticHistoryPolicy start)
    (current : A.HistoryFrom start) (horizon : ℕ)
    (terminated : ∀ final,
      (A.stochasticHistoryLawFrom policy current horizon).HasPositiveAtom final →
        A.IsTerminal final.1) :
    ∃ supplied : ProbabilityMeasure (ℕ → A.HistoryFrom start),
      (supplied : Measure (ℕ → A.HistoryFrom start)) =
          μ[(completePaths policy current horizon).atoms] ∧
      (∀ n, (Arena.pathLaw policy current supplied).map (fun path => path n) =
        μ[(A.stochasticHistoryLawFrom policy current n).atoms]) ∧
      (∀ᵐ path ∂Arena.pathLaw policy current supplied,
        ∀ n, Arena.IsLegalAbsorbingTransition policy (path n) (path (n + 1))) ∧
      (∀ᵐ path ∂Arena.pathLaw policy current supplied,
        A.IsCompletePlayPathFrom current path) ∧
      (∀ᵐ path ∂Arena.pathLaw policy current supplied,
        A.IsTerminal (path horizon).1) ∧
      (∀ᵐ path ∂Arena.pathLaw policy current supplied,
        ∀ n, A.IsTerminal (path n).1 → path (n + 1) = path n) := by
  let law := completePaths policy current horizon
  letI := FiniteLawIntegral.isProbabilityMeasure law
  refine ⟨⟨μ[law.atoms], inferInstance⟩, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · exact measure_finiteMarginal policy current horizon terminated
  · exact ae_of_positive law _ (fun path hp =>
      completePaths_legalTransition policy current horizon terminated path hp)
  · exact ae_of_positive law _ (fun path hp =>
      completePaths_legal policy current horizon terminated path hp)
  · exact ae_of_positive law _ (fun path hp =>
      completePaths_terminal policy current horizon terminated path hp)
  · apply ae_of_positive law
    intro path hp n ht
    rcases completePaths_legalTransition policy current horizon terminated path hp n with
      hs | ⟨hn, _⟩
    · exact hs.2
    · exact (hn ht).elim

end MeasureInterpretation

section Regression

/-- A prehistory, a fork, a delayed terminal route, and a zero-probability loop. -/
inductive Node
  | entry | fork | middle | terminal | loop
  deriving DecidableEq, Repr

/-- The loop has legal actions forever; only its chance weight is zero. -/
def arena : Arena where
  State := Node
  Action
    | .entry | .middle | .loop => Unit
    | .fork => Fin 3
    | .terminal => PEmpty
  next
    | .entry, _ => .fork
    | .fork, a => if a = 0 then .terminal else if a = 1 then .middle else .loop
    | .middle, _ => .terminal
    | .loop, _ => .loop
    | .terminal, a => PEmpty.elim a

local instance terminalDecidable : (state : arena.State) → Decidable (arena.IsTerminal state)
  | .entry | .middle | .loop => isFalse (fun h => h.false ())
  | .fork => isFalse (fun h => h.false (0 : Fin 3))
  | .terminal => isTrue ⟨PEmpty.elim⟩

/-- Duplicated immediate termination, delayed termination, and a zero loop. -/
def forkLaw : FiniteLaw (Fin 3) where
  atoms := [(0, 1 / 2), (1, 1 / 3), (0, 1 / 6), (2, 0)]
  normalized := by norm_num

/-- Every non-fork nonterminal state has its explicit sole action. -/
def policy : arena.StochasticHistoryPolicy .entry := by
  intro history hn
  rcases history with ⟨state, history⟩
  cases state with
  | entry | middle | loop => exact FiniteLaw.pure ()
  | fork => exact forkLaw
  | terminal => exact (hn ⟨PEmpty.elim⟩).elim

/-- The incoming history already contains one action. -/
def current : arena.HistoryFrom .entry := ⟨.fork, Arena.History.nil.snoc ()⟩

/-- The immediate route reaches the terminal state after one further action. -/
def direct : arena.HistoryFrom .entry := ⟨_, current.2.snoc (0 : Fin 3)⟩

/-- The delayed route reaches the same world endpoint one action later. -/
def delayed : arena.HistoryFrom .entry := ⟨_, (current.2.snoc (1 : Fin 3)).snoc ()⟩

/-- This history has zero weight and is still nonterminal at the chosen bound. -/
def ghost : arena.HistoryFrom .entry := ⟨_, (current.2.snoc (2 : Fin 3)).snoc ()⟩

/-- The executor preserves duplicate and zero atoms in its sparse representation. -/
theorem two_step_atoms :
    (arena.stochasticHistoryLawFrom policy current 2).atoms =
      [(direct, 1 / 2), (delayed, 1 / 3), (direct, 1 / 6), (ghost, 0)] := by
  change [(direct, (1 / 2 : ℚ≥0) * 1), (delayed, (1 / 3 : ℚ≥0) * (1 * 1)),
    (direct, (1 / 6 : ℚ≥0) * 1), (ghost, 0 * (1 * 1))] = _
  norm_num

/-- The bound is proved only on positive atoms: it does not claim the loop terminates. -/
theorem terminated_by_two : ∀ final,
    (arena.stochasticHistoryLawFrom policy current 2).HasPositiveAtom final →
      arena.IsTerminal final.1 := by
  rintro final ⟨weight, hmem, hw⟩
  rw [two_step_atoms] at hmem
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
  rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨PEmpty.elim⟩
  · exact ⟨PEmpty.elim⟩
  · exact ⟨PEmpty.elim⟩
  · exact (hw rfl).elim

/-- The zero-weight loop history is unfinished and cannot be claimed as a play. -/
theorem ghost_unfinished : ¬ arena.IsTerminal ghost.1 := fun h => h.false ()

/-- Holding the unfinished zero atom after the horizon would be illegal.
Its presence is harmless only because every occurrence has weight zero. -/
theorem ghost_replay_not_legal :
    ¬ arena.IsCompletePlayPathFrom current
      (fun n => prefixAt ghost.2 (current.2.length + n)) := by
  intro hp
  have hs := hp.2 2
  change (arena.IsTerminal ghost.1 ∧ ghost = ghost) ∨ arena.IsChildFrom ghost ghost at hs
  rcases hs with ⟨ht, _⟩ | hc
  · exact ghost_unfinished ht
  · have hlength := hc.length_eq
    change 3 = 3 + 1 at hlength
    omega

/-- Two terminal histories share a world endpoint but retain different actions
and different absolute lengths. -/
theorem distinct_histories : direct.1 = delayed.1 ∧ direct ≠ delayed ∧
    direct.2.length = 2 ∧ delayed.2.length = 3 := by
  refine ⟨rfl, ?_, rfl, rfl⟩
  intro h
  have := congrArg (fun history : arena.HistoryFrom .entry => history.2.length) h
  contradiction

/-- Sampling a finite list of coordinates executes without path equality or an
infinite array. The retained zero atom visibly stays in the loop. -/
theorem coordinate_samples :
    ((completePaths policy current 2).map
      (fun path => (List.range 5).map (fun n => path n |>.1))).atoms =
      [([.fork, .terminal, .terminal, .terminal, .terminal], 1 / 2),
       ([.fork, .middle, .terminal, .terminal, .terminal], 1 / 3),
       ([.fork, .terminal, .terminal, .terminal, .terminal], 1 / 6),
       ([.fork, .loop, .loop, .loop, .loop], 0)] := by
  simp only [completePaths, FiniteLaw.map_atoms, two_step_atoms, List.map_map]
  rfl

/-- At the bound and long afterward the same exact expected absolute length
distinguishes the delayed history from the direct one. -/
theorem lengths_after_bound :
    (completePaths policy current 2).expectRat (fun path => (path 2).2.length) = 7 / 3 ∧
    (completePaths policy current 2).expectRat (fun path => (path 100).2.length) = 7 / 3 := by
  decide +kernel

/-- Horizon zero at an already terminal nonempty history constructs its constant path. -/
theorem terminal_at_zero :
    ((completePaths policy direct 0).map
      (fun path => ((path 0).2.length, (path 100).2.length))).atoms = [((2, 2), 1)] := by
  decide +kernel

local instance : MeasurableSpace (arena.HistoryFrom .entry) := ⊤

/-- A concrete downstream consumer obtains the complete probability measure,
all coordinate marginals, and legality from the proved bound, without supplying
any path law or realization certificate. -/
theorem regression_pathLaw : ∃ supplied : ProbabilityMeasure (ℕ → arena.HistoryFrom .entry),
    (supplied : Measure (ℕ → arena.HistoryFrom .entry)) =
        μ[(completePaths policy current 2).atoms] ∧
    (∀ n, (Arena.pathLaw policy current supplied).map (fun path => path n) =
      μ[(arena.stochasticHistoryLawFrom policy current n).atoms]) ∧
    (∀ᵐ path ∂Arena.pathLaw policy current supplied,
      arena.IsCompletePlayPathFrom current path) := by
  obtain ⟨law, heq, hmarginal, _, hlegal, _⟩ := exists_pathLaw policy current 2 terminated_by_two
  exact ⟨law, heq, hmarginal, hlegal⟩

/-- info: ([(2, 1 / 2), (3, 1 / 3), (2, 1 / 6), (3, 0)], 7 / 3) -/
#guard_msgs in
#eval ((completePaths policy current 2).atoms.map (fun atom =>
    ((atom.1 100).2.length, (atom.2 : ℚ))),
  (completePaths policy current 2).expectRat (fun path => (path 100).2.length))

end Regression

end Examples.ExtensiveGame.FiniteCompletePath
