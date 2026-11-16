---
id: game_theory.strategic_game.bayesian.war_of_attrition
primary_topic: game_theory.strategic_game
topics:
  - game_theory.strategic_game
  - game_theory.strategic_game.bayesian_correlated
title: Bayesian War of Attrition
kind: example
status: staged
uses:
  - game_theory.strategic_game.bayesian.bayesian_game
lean:
  modules:
    - EconCSLib.GameTheory.StrategicGame.BayesianGame.WarOfAttrition
    - EconCSLib.GameTheory.StrategicGame.BayesianGame.WarOfAttrition.CompactApproximation
  declarations:
    - StrategicGame.WarOfAttrition.payoff
    - StrategicGame.WarOfAttrition.IsSymmetricEquilibrium
    - StrategicGame.WarOfAttrition.mixedPayoffIntegrable_exponentialOpponent
    - StrategicGame.WarOfAttrition.isSymmetricEquilibrium_exponentialConcessionLaw
    - StrategicGame.WarOfAttrition.RegularFullSupportEquilibrium.exponential
    - StrategicGame.WarOfAttrition.RegularFullSupportEquilibrium.measure_eq_exponential
    - StrategicGame.WarOfAttrition.DensityModel.candidateStrategy
    - StrategicGame.WarOfAttrition.DensityModel.candidate_isRegularSymmetricEquilibrium
    - StrategicGame.WarOfAttrition.DensityModel.regularEquilibrium_eq_candidate
    - StrategicGame.WarOfAttrition.CompactDensityModel
    - StrategicGame.WarOfAttrition.CompactDensityModel.candidate_isSymmetricBayesianEquilibrium
    - StrategicGame.WarOfAttrition.CompactDensityModel.candidate_isRegularSymmetricBayesianEquilibrium
    - StrategicGame.WarOfAttrition.CompactDensityModel.candidate_absolutelyContinuousOnInterval
    - StrategicGame.WarOfAttrition.CompactDensityModel.regularEquilibrium_eq_candidate
    - StrategicGame.WarOfAttrition.CompactDensityModel.dist_candidate_center_mul_hazard_le
    - StrategicGame.WarOfAttrition.map_exponentialQuantile
    - StrategicGame.WarOfAttrition.CompactActionLawSequence.candidate_isEquilibrium
    - StrategicGame.WarOfAttrition.CompactActionLawSequence.convergesToExponentialLaw
verification:
  statement: accepted
  proof: accepted
  alignment: aligned
tags:
  - strategic-game
  - bayesian-game
  - war-of-attrition
  - continuous-game
---

# Bayesian War of Attrition

Two players have independently drawn nonnegative prize values $v_i$ and choose
concession times $s_i\ge 0$. Player $i$ receives
$$
  u_i(v_i;s_i,s_j)=
  \begin{cases}
    v_i-s_j,&s_j<s_i,\\
    -s_i,&s_j\ge s_i.
  \end{cases}
$$

For a common known value $v>0$, the symmetric equilibrium concession-time law
has distribution function
$$
  Q_v(t)=1-\exp(-t/v).
$$
For an absolutely continuous value distribution with density $g$ and
cumulative distribution $G$, the source gives the type-contingent concession
time
$$
  s(v_i)=\int_0^{v_i}\frac{t\,g(t)}{1-G(t)}\,dt.
$$

The Lean development keeps the analytic hypotheses suppressed by the short
textbook example explicit. In the complete-information case, it proves the
exponential law is an equilibrium against every admissible probability-law
deviation and separately proves that every such deviation has an integrable
iterated payoff against the exponential opponent. Its uniqueness theorem is
for an explicit regular full-support class: the law has a density continuous
on strictly positive times, its CDF and actual pure expected payoff have the
stated derivatives, and all nonnegative pure concession times are indifferent.
The exponential candidate is formally constructed as a member of this class,
so the uniqueness result is not an implication from an empty regularity class.

For private values, the implementation proves that the displayed cutoff
objective equals the original expected-payoff integral under a continuous
strictly increasing strategy. Under strictly positive density and an explicit
tail/onto condition, the displayed candidate is a regular symmetric
equilibrium. Any other locally absolutely continuous regular equilibrium has
the same strategy on all nonnegative values; its equilibrium premise remains
only type-law almost everywhere.

For the bounded-support approximation, Lean uses the explicit regularity class
suppressed by the textbook's phrase "has a density": the density is continuous,
strictly positive on the interior of its compact support, and zero outside it;
the actual CDF has that density as its derivative and has the stated endpoint
values. The CDF order isomorphism pushes a uniform random variable to the type
law. The displayed strategy is proved to be an equilibrium against every
nonnegative concession-time deviation. It is also an inhabited member of the
regular class used for uniqueness: Lean proves its local absolute continuity,
and every locally absolutely continuous regular symmetric equilibrium agrees
with it throughout the half-open type support.

For a sequence supported on
$[v-\varepsilon_n,v+\varepsilon_n]$ with $\varepsilon_n\to0$, Lean derives
$$
  \lvert s_n(x)-vH_n(x)\rvert
  \le \varepsilon_n H_n(x),
  \qquad H_n(x)=-\log(1-G_n(x)),
$$
directly from the support and density hypotheses. It also constructs the
uniform exponential quantile and proves that its pushforward is $Q_v$.
Dominated convergence then gives convergence of the equilibrium action laws
against every bounded continuous test function. No coupling, equilibrium, or
convergence certificate is assumed. The source's separate weak convergence
$G_n\Rightarrow\delta_v$ is redundant here: shrinking support already forces
concentration at $v$. Thus item 3 is fully proved for this explicit compact
positive-density regularity class, with the Lean theorem stated for arbitrary
error radii $\varepsilon_n\to0$ rather than only $\varepsilon_n=1/n$.

## References

- [MFoGT, Example 7.4.1] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. War of attrition with private values.
- [Milgrom-Weber 1985, Section 2] Paul R. Milgrom and Robert J. Weber, "Distributional Strategies for Games with Incomplete Information," *Mathematics of Operations Research* 10(4):619-632, <https://doi.org/10.1287/moor.10.4.619>.
- [Bishop-Cannings 1978] D. T. Bishop and C. Cannings, "A Generalized War of Attrition," *Journal of Theoretical Biology* 70(1):85-124, <https://doi.org/10.1016/0022-5193(78)90304-1>.
