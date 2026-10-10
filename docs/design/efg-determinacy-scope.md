# Determinacy scope

This note is the authority for the word “determinacy” in the EFG library.
`IsTotal` says every complete play is won by someone; it does not construct a
strategy. `IsTwoPlayerDetermined` is the pure pathwise disjunction saying
player `0` or player `1` has a strategy winning against every compatible
opponent play.

## Declaration inventory

| API | Players / objective | Information / chance | Horizon | Strategy | Foundations | Exact conclusion |
|---|---|---|---|---|---|---|
| `GameTree.zermelo_determinacy` | two-player rational zero-sum payoff | perfect information, no chance | inductive finite `GameTree` | pure tree strategy | finite recursion and classical finite selection | saddle-value/payoff determinacy for the compact frontend |
| `ControlledObservedGame.FiniteTwoPlayerHypotheses.isTwoPlayerDetermined` | exactly two; complete-play winning sets are total and exclusive | perfect information; no chance | uniform finite history bound, finite action/represented-information presentation | pure strategy over represented coordinates | specializes the well-founded proof; classical choice | one player has a robust pathwise winning strategy |
| `ControlledObservedGame.WellFoundedTwoPlayerHypotheses.isTwoPlayerDetermined` | exactly two; complete-play winning sets are total and exclusive | perfect information; no chance | child relation well founded; supplied complete finite action lists at every history | pure strategy over represented coordinates | `WellFounded.fix` with `BackwardInductionData`: terminality test, certified terminal winners, action lists, and represented-coordinate representatives | one player has a robust pathwise winning strategy under both the structural hypotheses and the supplied data |
| `ControlledObservedGame.WellFoundedPrefixHypotheses.isTwoPlayerDetermined` | same two-player zero-sum winning-set scope | same perfect-information/no-chance scope | structurally well founded, plus a persistent prefix-decision certificate and complete finite action lists | pure | the same explicit `BackwardInductionData` is required | same pathwise determinacy; the prefix certificate additionally records clopen-style objective evidence |
| `not_both_havePathwiseWinningStrategy` | two players; exclusivity only | arbitrary observed information; no chance | arbitrary | pure | constructs the joint pure-profile play; requires decidable terminality | the two players cannot both have robust winners; no existence conclusion |
| `HasPathwiseWinningStrategy`, `HasWinningQuasiStrategy`, and payoff-aware `HasStrategicWinningStrategy` | arbitrary player type and winning family | information restrictions are explicit in later theorems | arbitrary | pure or quasistrategy | definitions/bridges only | compatibility or robust-winning predicates, not determinacy |
| `PrefixDecision.isPrefixOpen`, `.isPrefixClosed`, and `.hasFinitePrefixDecision` | arbitrary winning family, with explicit exclusivity where used | path topology only | possibly infinite | none | ordinary topology | openness/closedness/measurability facts; no winning-strategy existence |
| `IsAlmostSurelyWinningUnder` and `StochasticHistoryPolicy.IsAlmostSurelyWinning` | one measurable winning event under a fixed policy | chance/randomized history policy | possibly infinite | stochastic policy | measure theory | probability-one membership under that policy; neither logical nor two-player determinacy |
| `Arena.AETerminates`, `TerminatesAlmostSurely`, and `ReachesTerminalAlmostSurely` | no winning-set claim | stochastic execution | possibly infinite | stochastic policy/profile | measure theory | almost-sure termination only |

The compatibility declarations under `ObservedGame` retain old payoff-aware
names. The existence theorems are owned by the payoff-free
`ControlledObservedGame` carrier.

## Implemented next layer

The implemented theorem is well-founded backward determinacy with explicit
`BackwardInductionData`. Its recursive winner and action selection need:

- well-founded recursion on the immediate-child relation;
- a supplied terminality decision procedure and certified terminal winner;
- a complete finite action list at every history, searched for a winning child;
- a supplied occurrence representative for each represented information coordinate;
- perfect information to transport the representative's action back to the
  actual complete-history occurrence; and
- the decision witness stored in each represented coordinate, which makes its
  dependent abstract-action fiber inhabited without global representation or
  mover-coherence hypotheses.

No ordinal-valued transfinite recursion is exposed, no descriptive-set
theory is imported, and no external determinacy axiom is assumed.
`IsWellFoundedFrom.eventuallyTerminates` replaces the finite theorem's
uniform terminal coordinate. The finite theorem constructs the required data
from its finite presentation using classical choice, then specializes this
recursive theorem. `WellFoundedTwoPlayerHypotheses` alone does not supply
`BackwardInductionData`: the structural package permits infinite branching,
whereas a complete finite action list does not.

`WellFoundedPrefixHypotheses` keeps a `PrefixDecision` field so that the same
model can be related to the prefix topology. The determinacy proof itself
uses structural well-foundedness, which is stronger than merely saying that
each play eventually reaches a deciding prefix.

## Infinite boundary

The theorem says nothing about a tree with a genuine infinite branch:
`WellFounded.fix` is then unavailable, terminal replay does not assign the
winner of a nonterminating play, and an arbitrary winning subset of infinite
paths need not be prefix-decided.
`Examples.StructuralTermination.InfiniteLoop` exhibits a legal
never-terminating complete play and proves that root well-foundedness fails;
`Examples.StructuralTermination.UnboundedWellFounded` separately shows that
structural well-foundedness alone need not give a uniform finite depth bound.
Its root has action type `Nat`, so it cannot supply a complete finite action
list and is not an instance of the implemented determinacy theorem. General
well-founded determinacy with arbitrary branching remains unimplemented.

Open/closed Gale--Stewart determinacy is a separate future theorem. Arbitrary
winning-set determinacy and Borel determinacy are not consequences of either
finite or well-founded backward induction and are not claimed by any facade.

## Sources

- Ernst Zermelo, “Über eine Anwendung der Mengenlehre auf die Theorie des
  Schachspiels,” *Proceedings of the Fifth International Congress of
  Mathematicians*, 1913, pp. 501--504.
- David Gale and F. M. Stewart, “Infinite Games with Perfect Information,”
  in *Contributions to the Theory of Games II*, Annals of Mathematics Studies
  28, 1953, pp. 245--266. This is the source boundary for the distinct
  infinite open/closed-game track, not a theorem imported by the current
  backward proof.
