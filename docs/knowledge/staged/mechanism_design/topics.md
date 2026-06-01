# Staged Mechanism Design Topic Catalog

Canonical folder topic: `mechanism_design`

## Local Scope

`mechanism_design.basic` owns the direct-revelation interface and the first
bridges from mechanisms to strategic games. It should contain the direct
mechanism structure, the induced strategic game, DSIC, ex-post individual
rationality, and the theorem that DSIC truthfulness gives a Nash equilibrium.

Do not put Bayesian priors, transfers, VCG welfare maximization, Myerson payment
formulae, or auction-format specializations in `mechanism_design.basic`; those
belong to the subtopics below.

## Subtopics

- `mechanism_design.basic` - direct mechanisms, DSIC, ex-post IR, and truthfulness-to-Nash interfaces.
- `mechanism_design.transfer` - mechanisms with transfers, quasi-linear utility, and parameter layers.
- `mechanism_design.bayesian` - Bayesian mechanisms, strategies, ex-ante equilibrium, and revelation principles.
- `mechanism_design.vcg` - welfare, payments, VCG mechanisms, truthfulness, and individual rationality.
- `mechanism_design.myerson` - payment formulae and monotonicity characterizations.

## Source Guidance

- Use [Krishna 2010] Vijay Krishna, *Auction Theory*, 2nd ed., especially Chapters 5 and 10, for
  auction-facing mechanism design: mechanisms, revelation principles, incentive
  compatibility, individual rationality, optimal mechanisms, efficient
  mechanisms, VCG, and interdependent-value mechanism design.

## Boundary

Put auction-format specializations under `auction`.

## Expected Basic Nodes

- `mechanism_design.basic.direct_mechanism_interface` - the direct mechanism structure and outcome map.
- `mechanism_design.basic.induced_strategic_game` - the strategic game induced by a direct mechanism, utility function, and true type profile.
- `mechanism_design.basic.dsic_predicate` - dominant-strategy incentive compatibility as weak dominance of truthful reports.
- `mechanism_design.basic.ex_post_ir_predicate` - pointwise nonnegative truthful utility.
- `mechanism_design.basic.truthfulness_from_dsic` - DSIC implies truthful reporting is a Nash equilibrium of the induced game.
