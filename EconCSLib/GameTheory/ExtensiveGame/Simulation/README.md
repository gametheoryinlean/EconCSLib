# Analytic simulation implementation

This directory contains internal implementation leaves behind the public
`Interface.Execution.Analytic`, `Interface.Equilibrium.Analytic`, and
`Interface.Restart` facades.

The directory carries the repeated context so filenames stay short:

```text
Simulation/
├── Kernel/         measurable-kernel execution and path laws
├── Presentation/   observed/chance presentation and profile assembly
│   ├── Chance/     PMF observed-chance adapters
│   └── Kernel/     general kernel-valued observed profiles
├── Equilibrium/    outcome and equilibrium semantics
├── Continuation/   absolute-prefix and conditional continuations
└── Restart/        fresh-restart certificates and transfer
```

Do not repeat `MeasurableKernel`, `ObservedChance`, or
`ObservedMeasurableKernel` in new filenames when the directory already supplies
that context. Keep declaration names literature-facing and independent of
physical module paths.

Ordinary users should import the corresponding `Interface.*` facade. Internal
module paths may be reorganized. The former long restart-compatibility
aggregate was deleted; use `Interface.Restart`.
