# Arrow's Theorem: External Proof Source Found

## mdnestor/GameTheory — Complete Arrow Proof

**Repo**: https://github.com/mdnestor/GameTheory
**File**: `GameTheory/SocialChoice.lean` (~400 lines)
**Status**: Fully proved without placeholders, Lean 4

### Proof Structure

Uses decisive coalitions argument (same as MSZ Ch.21):

1. `unanimity_univ_isDecisive` — unanimity/Pareto ⟹ grand coalition is decisive
2. `isDecisive_spread` — decisive for one pair ⟹ decisive for all pairs
   (implemented through private forward/backward/symmetry steps)
3. `isDecisive_contraction` — if a decisive coalition has ≥ 2 members,
   there exists a strictly smaller decisive coalition
4. `minimal_decisive_coalition_card_one` — minimal decisive coalition has size 1
5. `arrow_of_unanimity_iia` — that single individual is a dictator

### Key Technical Elements

- `Pref R` — class for reflexive, transitive, total relations
- `Prefs X = {R | Pref R}` — the set of all preference relations
- `IsDecisiveFor`, `IsWeaklyDecisiveFor`, `IsDecisive` — coalition properties
- `iia_strict` — IIA transfers strict preferences between profiles
- private preference-construction helpers — constructing new preference profiles
  by inserting alternatives (the "contagion" step)
- private tripartition helpers — splitting a coalition into three parts for the
  Condorcet-type argument
- `exists_minimal_of_wellFoundedLT` — Mathlib well-foundedness for
  finding minimal decisive coalition

### Differences from Our Design

| Aspect | mdnestor | Ours |
|--------|----------|------|
| Preference | `Pref R` class (reflexive+transitive+total) | `Pref A` structure (reflexive+transitive+total) |
| SWF type | `(I → Prefs X) → Prefs X` | `SocialChoice.Voting.SWF N A` structure |
| Strict pref | `strict R x y := R x y ∧ ¬R y x` (derived) | `strict R x y := R x y ∧ ¬ R y x` (derived) |
| Decisive | `decisive_over F C x y` (function) | `SocialChoice.Voting.IsDecisiveFor F C a b` |
| IIA | `iia F` (on the function) | `F.IIA` directly on `SWF` |

### Porting Assessment

**Status**: Ported. The proof logic is now adapted to the current social-choice
preference model, where weak preference is primitive (`Pref A`) and strict
preference is derived by `strict`.

The decisive-coalitions proof vocabulary now lives in
`EconCSLib/SocialChoice/Voting/Decisive.lean`.
