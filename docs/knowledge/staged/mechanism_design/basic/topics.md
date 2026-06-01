# Mechanism Design Basic Topic Catalog

Canonical folder topic: `mechanism_design.basic`

## Scope

`mechanism_design.basic` contains the direct-revelation interface and the first
bridges from mechanisms to strategic games:

- a direct mechanism structure with report spaces and an outcome map;
- the strategic game induced by a direct mechanism, utilities, and a true type profile;
- dominant-strategy incentive compatibility as weak dominance of truthful reports;
- ex-post individual rationality as pointwise nonnegative truthful utility;
- the theorem that DSIC truthfulness gives a Nash equilibrium in the induced game.

## Boundary

Do not put Bayesian priors, transfer/quasi-linear utility structure, VCG welfare
maximization, Myerson payment formulae, or auction-format specializations here.
Use `mechanism_design.bayesian`, `mechanism_design.transfer`,
`mechanism_design.vcg`, `mechanism_design.myerson`, or `auction` for those.

## Expected Nodes

- `mechanism_design.basic.direct_mechanism_interface` - direct mechanism structure and outcome map.
- `mechanism_design.basic.induced_strategic_game` - the normal-form game induced by reports and utilities.
- `mechanism_design.basic.dsic_predicate` - DSIC as weak dominance of truthful reporting.
- `mechanism_design.basic.ex_post_ir_predicate` - ex-post individual rationality.
- `mechanism_design.basic.truthfulness_from_dsic` - DSIC implies truthful reporting is Nash.
