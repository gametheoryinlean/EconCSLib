import EconCSLib.GameTheory.ExtensiveGame.Execution.Discrete.DiscountedPathUtility

/-!
# Computable history-kernel smoke test

This file exercises the main-library finite history executor without importing
`EconCSLib.Examples`.  The policy loops at absolute time zero, terminates at
absolute time one, and then remains absorbed.  The resulting exact laws check
complete-prefix retention, absolute-clock continuation, and action occurrence
recording.
It also checks the general effective-path discounted wrapper at the
off-by-one-sensitive horizon `H = 3`: rewards use coordinates `0, 1, 2`, and
the remaining geometric radius starts at exponent `3`.
-/

namespace HistoryKernelSmoke

inductive State where
  | active
  | terminal
deriving DecidableEq, Repr

def Action : State → Type
  | .active => Bool
  | .terminal => Empty

instance actionIsEmptyDecidable :
    (state : State) → Decidable (IsEmpty (Action state))
  | .active => isFalse fun h => h.false false
  | .terminal => isTrue ⟨fun action => nomatch action⟩

abbrev arena : KernelArena where
  State := State
  Action := Action
  next
    | .active, false => FiniteLaw.pure .active
    | .active, true => FiniteLaw.pure .terminal
    | .terminal, action => nomatch action

/-- Select the terminating action from absolute time one onward. -/
def policy : arena.StateHistoryPolicy :=
  fun time history hnonterminal => by
    cases hstate : history.latest with
    | active =>
        exact FiniteLaw.pure (time != 0)
    | terminal =>
        have : IsEmpty (arena.Action history.latest) := by
          rw [hstate]
          exact ⟨fun action => nomatch action⟩
        exact (hnonterminal this).elim

def root : arena.StatePrefix 0 :=
  KernelArena.StatePrefix.initial .active

def validPrefixAtOne : arena.StatePrefix 1 :=
  fun _ => .active

def stateSignature (history : arena.StatePrefix 3) :
    State × State × State × State :=
  (history ⟨0, by decide⟩, history ⟨1, by decide⟩,
    history ⟨2, by decide⟩, history ⟨3, by decide⟩)

def recordedAction? (event : arena.PathEvent) : Option Bool :=
  match event.action with
  | Sum.inl _ => none
  | Sum.inr ⟨.active, action⟩ => some action
  | Sum.inr ⟨.terminal, action⟩ => nomatch action

def eventSignature (history : arena.EventPrefix 3) :
    State × Option Bool × Option Bool × Option Bool :=
  (history.latestState,
    recordedAction? (history ⟨1, by decide⟩),
    recordedAction? (history ⟨2, by decide⟩),
    recordedAction? (history ⟨3, by decide⟩))

example :
    ((policy.prefixLawFrom 0 root 3).map stateSignature).mass
        (.active, .active, .terminal, .terminal) = 1 := by
  native_decide

/-- Starting from an already valid time-one prefix uses time one rather than
silently rebasing the policy clock to zero. -/
example :
    ((policy.prefixLawFrom 1 validPrefixAtOne 1).map
        KernelArena.StatePrefix.latest).mass .terminal = 1 := by
  native_decide

example :
    (((policy.toEventHistoryPolicy).prefixLawFrom 0
        (KernelArena.EventPrefix.initial .active) 3).map
          eventSignature).mass
      (.terminal, some false, some true, none) = 1 := by
  native_decide

example :
    policy.actionLaw? 0 (KernelArena.StatePrefix.initial .terminal) = none := by
  rw [KernelArena.StateHistoryPolicy.actionLaw?_eq_none_iff (A := arena)]
  exact ⟨fun action => nomatch action⟩

def discountedUtility : arena.StateDiscountedPathUtility where
  reward := fun _ _ => 2
  discount := 1 / 2
  discount_lt_one := by native_decide
  bound := 2
  reward_abs_le := by
    intro _ _
    norm_num

example : discountedUtility.tailRadius 3 = 1 / 2 := by
  native_decide

example :
    discountedUtility.center (policy.effectivePathLawFrom 0 root) 3 = 7 / 2 := by
  native_decide

end HistoryKernelSmoke
