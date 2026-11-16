# EFG semantic execution regimes

This note is the authoritative ownership and bridge contract for the distinct
EFG execution regimes. Lean declarations remain authoritative for individual
definitions and theorems; [`efg-preservation-matrix.md`](efg-preservation-matrix.md)
remains authoritative for the strength of each proved relation.

The regimes are deliberately not fields of one universal game record. They
share structural occurrences and, where a full lawful probability is
available, a representation-independent path-law comparison layer. This
factorization avoids imposing countability on analytic models or measurability
on structural and finite models.

## Ownership ledger

| Regime | Native owner or producer | Recommended facade | Common-law status | What is not supplied |
|---|---|---|---|---|
| Structural occurrence semantics | `EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled` | `EconCSLib.GameTheory.ExtensiveGame.Interface.StructuralCore` | No probability law; owns the common history and legal-play predicates | chance normalization, execution, utility, and equilibrium |
| Finite discrete execution | `EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Law.Discrete` | `EconCSLib.GameTheory.ExtensiveGame.Interface.Execution.Finite` | Executable bounded history `FiniteLaw` values only; does not import the full measure-valued path-law carrier | infinite path measure and non-atomic kernels |
| Infinite discrete execution | `EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Law.DiscretePath` | `EconCSLib.GameTheory.ExtensiveGame.Interface.Execution.Infinite` | Consumes a supplied probability path law and bounded measure marginals, with exact certificates relating them to executable `FiniteLaw` prefixes | construction of an infinite law, non-atomic action kernels, and arbitrary-measure behavioral strategies |
| Analytic kernel execution | `EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Law.Analytic` | `EconCSLib.GameTheory.ExtensiveGame.Interface.Execution.Analytic` | Constructs the same `CompletePathLawSemantics` from an explicitly lawful measurable-kernel presentation | automatic legality for an arbitrary stochastic-state kernel or a canonical measurable strategy space |
| Simultaneous FOSG frontend | `EconCSLib.GameTheory.ExtensiveGame.FOSG.FOSG` | `EconCSLib.GameTheory.ExtensiveGame.Interface.Compilation.Discrete` | Compiler-specific weak serialization, finite-horizon laws, and couplings only | strict EFG isomorphism, a general complete-path-law adapter, and standard SPE preservation |

`ControlledObservedGame.CompletePathLawSemantics`, owned by
`EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Law`, is the maximum
common probability-law carrier. It stores normalized, almost-surely legal
per-root complete-path marginals. It intentionally stores no PMF, local
kernel, countability assumption, strategic-mode tag, payoff, or claim that
the marginals are one common causal process. Local execution coherence,
restart consistency, conditioning, and cross-root coherence remain separate
certificates.

## Direction of adapters

The dependency direction is fixed:

```text
structural occurrences
        |
        v
common lawful complete-path marginals
       / \
      /   \
supplied discrete law  measurable-kernel executor

FiniteLaw prefixes --certified marginals--> supplied discrete law

FOSG --weak serialization/coupling--> discrete observed EFG
```

The common path-law module may not import either concrete producer. The
discrete adapter imports the common carrier and packages caller-supplied laws
with exact finite-prefix certificates; the analytic adapter proves that its
existing executor realizes the same carrier. The FOSG route remains a
frontend/compiler:
it acquires a common path-law conclusion only when a named compiler-specific
realization or coupling theorem actually supplies one.

## Claim discipline

Every generality claim must use one of these labels:

- **native**: represented directly by the structural occurrence carrier;
- **adapter-backed**: a concrete executor constructs the common lawful
  path-law carrier;
- **compiler-backed**: a frontend theorem states the exact preserved axes;
- **open**: no Lean declaration currently closes the requested semantic axis.

“Supported by EconCSLib” is not by itself a preservation statement. In
particular, a PMF theorem does not cover non-atomic kernels, a weak serializer
does not provide a strict isomorphism, and equality of bounded marginals does
not provide equality of full path laws without a named bridge.

## Governed import consequences

`scripts/check_efg_governance.py` checks the following route boundaries:

1. finite execution contains no full path-law or analytic adapter;
2. infinite discrete execution contains the common law and discrete adapter,
   but no analytic adapter or measurable-kernel arena;
3. analytic execution contains the common law, both concrete adapters, and
   the measurable-kernel arena;
4. discrete compilation and the FOSG sequentializer contain no common
   full-path or analytic execution implementation;
5. the common law does not depend on either producer adapter.

The checker establishes import ownership, not mathematical preservation.
Cross-regime conclusions still require the declarations catalogued in the
preservation matrix.

## Executable/analytic compatibility

Execution regimes identify where a model lives; the
[`semantic compatibility contract`](efg-semantic-compatibility.md) identifies
how a result crosses from an effective representation to general analytic
semantics. The finite algorithm owns the computed `FiniteLaw`, rational value,
Boolean, or partial result. A neighboring analytic leaf proves its interpreted
measure, marginal, integral, or error bound. The analytic definition remains
the active general semantic reference and is not classified as legacy.

There is deliberately no aggregate that imports every compatibility theorem.
`Interface.Execution.Analytic`, `Interface.Equilibrium.Analytic`, and
`Interface.Restart` expose the bridge belonging to their own semantic branch.
This preserves the regime directions above and prevents finite execution from
acquiring a reverse dependency on `Measure`, `Kernel`, or infinite paths.

This is the two-track representation boundary. Structural occurrences and
representation-neutral predicates are shared; executable probability and
analytic probability are separate producers. A declaration is placed on the
executable track whenever an effective representation preserves its intended
meaning. It remains analytic-only when no such representation exists at the
required generality.

## Computability boundary

The complete EFG/FiniteLaw/example audit counts every noncomputable identity,
including analytic constructions and generated proof helpers. Its reviewed
classification supplements the unchanged identity-subset ratchet. Explicit
zero modules, cleared declarations, import boundaries, and execution
regressions protect finite computation; a directory name is not an exemption.
See [`efg-computability-migration.md`](efg-computability-migration.md) for the
live review policy and the dated A–F result.

Bounded stopped utility uses a supplied executable terminal decision to select
the payoff at one coordinate or zero. General eventual absorption, arbitrary
measure/kernel construction, conditional distributions, and integrals retain
their analytic semantics. A supplied full path law and its coherence proofs
remain external mathematical data, even if their adapter has no noncomputable
markers. Neither returning a supplied real payoff nor projecting a path-law
certificate implements integration or construction of that law.
