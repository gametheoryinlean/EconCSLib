# Staged Linear Algebra Topic Catalog

Canonical folder topic: `math.linear_algebra`

## Subtopics

- `math.linear_algebra.alternatives` - Farkas-style alternatives and separation statements.

## Boundary

Put optimization-duality statements under `math.linear_programming` when the LP
formulation is essential.

Perron-Frobenius for positive matrices lives under `zero_sum.applications`
because the EconCSLib proof goes via Loomis (see
`docs/knowledge/nodes/zero_sum/perron_frobenius_positive_matrix.md`,
which keeps its physical location to track the Lean module
`EconCSLib/LinearAlgebra/PerronFrobenius.lean`).
