# EFG Minimal-Core Freeze Readiness

**Effective date:** 2026-08-05; carrier review updated 2026-08-12; A19 aggregate decision 2026-09-04
**Scope:** Canonical/Frontend API growth, candidate carrier data, and the
literal `Interface.StructuralCore` dependency boundary
**Status:** API growth frozen at the reviewed 2026-08-12 post-audit baseline;
minimal-core source compatibility remains deferred; the decision/observation
carrier split and the later two-path A19 pure/analytic aggregate split were
admitted as explicitly bounded exceptions

## Decision

The minimal carrier line remains:

```text
Arena
  -> ControlledGame
    -> ControlledDecisionGame
      -> ControlledObservedGame
```

The carrier, readability, ecosystem, reuse, and mathematical review remains
active. None of `Arena`, `ControlledGame`, `ControlledDecisionGame`, or
`ControlledObservedGame` is source-fingerprint-frozen, and the present
`Interface.StructuralCore` closure is not an external compatibility promise.
Changes still require an explicit representation argument, synchronized
downstream migration, and regression evidence.

Separately, the registered Canonical and Frontend surface is now under an API
growth freeze. No new Canonical/Frontend module path or explicit public
declaration is added after the checked baseline. Internal proof engineering
and opt-in Experimental work may continue, but Experimental declarations are
not promoted during the freeze. New mathematical targets belong in the
knowledge blueprint until the policy is explicitly reopened.

The 2026-08-12 literature-guided carrier audit established a concrete
representation failure in the previous baseline: decision information was
inseparable from optional observations, terminal mover labels could induce
spurious strategy obligations, and unused raw information values leaked into
strategy, finiteness, and belief coordinates. The maintainer therefore
approved one explicit growth-freeze exception for the synchronized hard
migration recorded in this document. Relative to the 2026-08-05 snapshot, the
reviewed surface has zero new governed modules, 31 added declarations, and
three removed declarations; the replacement snapshot contains 102 governed
modules and 1,739 explicit public declarations.

The exception covers only the decision/observation carrier split,
`RepresentedInfo` strategy coordinates and their structural transports,
constructive decision evidence, the public-signal trace builder needed by the
repaired recall hierarchy, and the bridge declarations relocated or exposed
by that migration. It does not generally reopen Canonical/Frontend growth.
The API-growth freeze resumes at the new snapshot, and any later addition
requires a new explicit policy decision.

The recorded 2026-09-04 A19 architecture decision adds a second, narrower
library-architecture exception. It adds exactly two declaration-free Canonical
module paths:
the measure-free `EconCSLib.Math.Probability.Effective` aggregate and the
opt-in `EconCSLib.Math.Probability.Effective.Analytic` aggregate. This prevents
Measure/Kernel/integral dependencies from leaking into executable clients.
The exception adds no public declaration and leaves the declaration ceiling
at 1,689; it does not reopen general Canonical/Frontend endpoint growth.

This is deliberately not a source-compatibility announcement. Existing
carrier fields, declaration types, implementation ownership, and module paths
may still require a reviewed correction or hard migration while the carrier
review remains open. The growth guard prevents the surface from becoming
larger during that convergence; it does not promise that every current
spelling will remain unchanged.

Usability work should prefer documentation, examples, per-game module
packages, and the existing constructors/frontends/compilers. Repeated
boilerplate may be studied in examples, but it does not justify a new
Canonical or Frontend abstraction during the freeze.

```lean
structure Arena where
  State : Type*
  Action : State → Type*
  next : (s : State) → Action s → State

structure ControlledGame (N : Type*) extends Arena where
  init : State
  mover : State → Option N

structure ControlledDecisionGame (N : Type uN) where
  base : ControlledGame.{uN, uA, uS} N
  InfoState : N → Type uI
  infoAt :
    ∀ (history : base.toArena.HistoryFrom base.init) (i : N),
      base.mover history.1 = some i →
      base.toArena.IsDecision history.1 →
      InfoState i
  InfoAction : (i : N) → InfoState i → Type uA
  actionEquiv :
    ∀ (history : base.toArena.HistoryFrom base.init) (i : N)
      (hmover : base.mover history.1 = some i)
      (hdecision : base.toArena.IsDecision history.1),
      InfoAction i (infoAt history i hmover hdecision) ≃
        base.Action history.1

structure ControlledObservedGame (N : Type uN)
    extends ControlledDecisionGame.{uN, uA, uS, uI} N where
  Observation : N → Type uO
  PublicObservation : Type uP
  observe :
    (i : N) → base.toArena.HistoryFrom base.init → Observation i
  publicObserve :
    base.toArena.HistoryFrom base.init → PublicObservation
  publicOf : (i : N) → Observation i → PublicObservation
  observe_public :
    ∀ (i : N) (history : base.toArena.HistoryFrom base.init),
      publicOf i (observe i history) = publicObserve history
  infoObserve : (i : N) → InfoState i → Observation i
  infoAt_observe :
    ∀ (history : base.toArena.HistoryFrom base.init) (i : N)
      (hmover : base.mover history.1 = some i)
      (hdecision : base.toArena.IsDecision history.1),
      infoObserve i (infoAt history i hmover hdecision) =
        observe i history
```

`ControlledDecisionGame` and its observation extension have a narrow
regression guard for the corrected universe mapping. `ControlledGame`'s
exposed universe order is player/action/state, so the base must be instantiated
as `ControlledGame.{uN, uA, uS}`. This keeps `InfoAction : Type uA` aligned
with the base action fiber while leaving the base state independently in
`Type uS`. `ControlledObservedGame` must extend it with
`ControlledDecisionGame.{uN, uA, uS, uI}`.

The previous spelling `ControlledGame.{uN, uS, uA}` accidentally put the base
action in `uS` and the base state in `uA`. It therefore tied `InfoAction` to
the state universe, collapsed action/state universes in the payoff-aware
projection, and forced an artificial `ULift` in finite unfolding. The
correction is representation-preserving at the term level and removes those
unnecessary universe equalities. The guard protects this specific mathematical
correction without freezing any other carrier field.

The literal structural facade currently has the exact five-module EFG
closure:

1. `Structural.Basic`
2. `Structural.Reachability`
3. `Structural.History`
4. `Execution.CompletePlay`
5. `Observed.Controlled`

Governance checks that closure as an import-boundary regression. During
pre-stability it may be deliberately revised together with its tests and
architecture rationale; it is not a source-compatibility freeze.

## Candidate semantic boundary

The current candidate design preserves these interpretations:

- terminality is derived from an empty action fiber;
- `mover s = none` is a non-player-control label, not a probability law;
- terminal mover labels create no strategy coordinate because decision
  information requires constructive `IsDecision` evidence;
- strategies range over `RepresentedInfo`, so unused raw `InfoState` values
  create neither obligations nor deviations;
- private/public observation is an optional extension of the decision core,
  not the definition of an information set;
- histories remain occurrence-sensitive even when world-state paths merge;
- payoff, objective, probability, recall, finiteness, termination,
  root-selection, equilibrium, measurability, and compiler data remain
  external.

During the growth freeze, a new capability is recorded in the knowledge
blueprint or an opt-in Experimental module rather than added to the
Canonical/Frontend surface. A carrier change remains possible during the
review, but must demonstrate a concrete representation failure that the
downstream alternatives cannot express.

## What remains open

The current review may still change:

- any of the four carrier declarations;
- the `Interface.StructuralCore` membership and dependency boundary;
- existing derived definitions, lemmas, instances, constructors, and
  equivalences, without growing the checked public surface;
- implementation ownership and existing higher-level facade boundaries;
- theorem statements under honestly stated additional hypotheses.

The corrected decision/observation action-state universe mapping remains a
required invariant unless a later representation change explicitly replaces
it with a more general, proved design.

## Machine enforcement

`scripts/check_efg_governance.py` currently enforces two carrier-review
invariants:

1. the corrected action/state universe mapping of
   `ControlledDecisionGame` and the universe order of its
   `ControlledObservedGame` extension, without fingerprinting either
   declaration; and
2. the current exact transitive EFG closure of `Interface.StructuralCore` as
   an import-boundary regression.

The generic fingerprint helper remains available in the checker, but the
active frozen-structure set is empty. A future freeze requires an explicit
architectural decision after the current review, followed by reviewed
fingerprints, documentation, and regression evidence in the same change.

`scripts/check_efg_api_growth.py` separately compares all registered
Canonical/Frontend module paths and explicit public source declarations
against `scripts/efg_api_growth_baseline.json`. CI rejects additions.
After cleanup and the explicit A19 path exception, the baseline records 97
governed Canonical/Frontend modules and a ceiling of 1,689 explicit public
declarations. The current tree owns 1,670 such declarations, 19 below the
ceiling. The A19 baseline update adds only the two zero-declaration aggregate
paths; it does not rewrite the declaration ceiling. Any later update is a
policy change, not routine maintenance, and must be accompanied by another
explicit revision of this decision.
