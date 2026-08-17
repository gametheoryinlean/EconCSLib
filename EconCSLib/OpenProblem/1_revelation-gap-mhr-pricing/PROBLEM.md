---
name: Revelation Gap for MHR Pricing from One Sample
contributor: Jason Hartline
---

## Revelation Gap for MHR Pricing from One Sample

### Background

In prior-independent mechanism design, a single mechanism must be fixed before
the distribution of agents' values is known.  The revelation gap measures the
loss from requiring this prior-independent mechanism to be truthful, direct, or
otherwise a revelation mechanism.  Non-revelation mechanisms can sometimes do
better because the protocol is distribution-independent while the agents'
equilibrium strategies adapt to the prior.

Fix an objective and let $M(F)$ denote the value of mechanism $M$ on
distribution $F$.  Let $\mathrm{OPT}_F$ denote an objective-maximizing
mechanism for distribution $F$, so $\mathrm{OPT}_F(F)$ is the optimal value
on $F$.  For a distribution family $\mathcal{D}$ and mechanism class
$\mathcal{M}$, write:

$$
\beta(\mathcal{M},\mathcal{D}) =
  \inf_{M\in \mathcal{M}}\sup_{F\in\mathcal{D}}
  \frac{\mathrm{OPT}_F(F)}{M(F)}.
$$

Here $M(F)$ is evaluated at the equilibrium selected for mechanism $M$ on distribution $F$. If $\mathcal{M}\_{\mathrm{rev}}$ is the
truthful/revelation subclass and $\mathcal{M}\_{\mathrm{all}}$ is the broader class of prior-independent mechanisms, the revelation gap is:

$$
\frac{\beta(\mathcal{M}_{\mathrm{rev}},\mathcal{D})}
       {\beta(\mathcal{M}_{\mathrm{all}},\mathcal{D})}.
$$

The central technical difficulty is that the revelation principle moves
distributional knowledge into the direct mechanism.  A non-revelation protocol
can be fixed before the prior is known while agents' equilibrium strategies
adapt to the prior.  The direct mechanism that simulates those strategies
usually depends on the prior and is therefore not prior-independent.

### Problem Description

In **single-buyer pricing from one sample**, a seller has one item and faces
one buyer.  The buyer's value $v\sim F$ is drawn from an unknown distribution
$F$.  The seller has access to one independent sample $s\sim F$.  The
buyer knows $F$ and her value $v$, but does not know the realized sample
before acting in the non-revelation mechanisms.

For this problem, $M(F)$ is the revenue of mechanism $M$ on distribution $F$.
The benchmark mechanism $\mathrm{OPT}_F$ posts the monopoly price for $F$, so:

$$
\mathrm{OPT}_F(F)=\sup_p p(1-F(p)).
$$

The prior-independent approximation factor of a mechanism $M$ is

$$
\sup_F \frac{\mathrm{OPT}_F(F)}{M(F)}.
$$

The cleanest version of the problem focuses on **MHR distributions**.  The two
mechanism classes in the baseline comparison are:
- **Truthful sample-pricing mechanisms**: scale-invariant mechanisms that are
  equivalent to posting a price as a function of the sample.
- **All mechanisms**: prior-independent mechanisms that may be non-truthful.
  The central simple example is the **sample-bid mechanism**: for multiplier
  $a>0$, the mechanism solicits a bid $b$, allocates if $b\ge s$, and
  charges $a\min\{b,s\}$ regardless of allocation.

### Known Results

- **Truthful MHR sample pricing is nearly characterized.**  The optimal
  truthful prior-independent approximation factor for MHR distributions lies
  in $[1.543,1.575]$.
  The lower bound is the barrier any scale-invariant truthful mechanism must
  face; the upper bound is achieved by the best known truthful sample-pricing
  rule.

- **Sample-bid beats truthful sample pricing.**  Feng, Hartline, and Li (2021)
  prove that the sample-bid mechanism has prior-independent approximation
  factor at most about $1.296$ for MHR distributions.  This is strictly better
  than the truthful lower bound $1.543$, giving a non-trivial revelation gap
  for revenue.

- **All mechanisms have a nontrivial lower bound.**  Feng, Hartline, and Li
  also prove that no prior-independent mechanism can have approximation factor
  better than about $1.0737$, even on uniform and degenerate-uniform
  instances.

- **Baseline MHR revelation-gap interval.**  Combining the truthful MHR
  interval with the all-mechanism interval from the one-bid/sample-bid model,
  $[1.0737,1.296]$, gives:

$$
1.190
  \le
  \frac{\beta(\mathcal{M}_{\mathrm{rev}},\mathcal{D}_{\mathrm{MHR}})}
       {\beta(\mathcal{M}_{\mathrm{all}},\mathcal{D}_{\mathrm{MHR}})}
  \le
  1.467.
$$

- **Regular distributions have a parallel but looser story.**  For regular
  distributions, the truthful factor is in $[1.957,1.996]$, while sample-bid
  gives an all-mechanism upper bound of $1.835$.  This proves a nontrivial
  revelation gap for regular revenue as well, but the MHR case gives the
  cleanest numerical comparison.

- **Recent extension: hidden-sample pricing.**  Tang, Tao, and Wang (2026)
  study a richer hidden-sample/message-space model in which the buyer may
  report distributional information.  They characterize strong hidden-pricing
  mechanisms and, for MHR distributions, give a positive guarantee of about
  $0.79$ of monopoly revenue, i.e., an approximation factor of about
  $1/0.79\approx 1.266$.  They also prove that no general prior-independent
  mechanism in their model can exceed about $0.838$ of monopoly revenue, i.e.,
  no factor better than about $1/0.838\approx 1.193$.  This tightens the
  all-mechanism side in the richer hidden-pricing model.  It should be treated
  as a distinct comparison from the value-only truthful/sample-pricing baseline
  because the permitted message space is different.

### Research Goal

Identify the tight MHR revelation gap for one-sample revenue maximization.
In the Feng-Hartline-Li one-bid/sample-bid formulation, this means closing

$$
1.190
  \le
  \text{MHR revelation gap}
  \le
  1.467.
$$

Concrete open questions:
- What is the exact all-mechanism prior-independent approximation factor for
  MHR one-sample pricing?  In the one-bid/sample-bid formulation, the known
  interval is $[1.0737,1.296]$; in the richer 2026 hidden-pricing model, it is
  roughly $[1.193,1.266]$.
- Is sample-bid optimal among simple one-bid non-revelation mechanisms?  If
  not, what structural property should replace it?
- Can the truthful MHR interval $[1.543,1.575]$ be closed?
- For regular distributions, can one close the larger intervals on both the
  truthful and all-mechanism sides?
- Without regularity assumptions, can this model yield a superconstant
  revelation gap, as suggested by Feng, Hartline, and Li?
- What is the right mechanism-class boundary?  Should direct reports of the
  prior, scoring-rule-style distribution reports, or multi-round communication
  be treated as legitimate non-revelation mechanisms, or as a different
  implementation-theory model?

### Key References

- Feng, Hartline, and Li, "Revelation Gap for Pricing from Samples" (STOC
  2021): https://arxiv.org/abs/2102.13496
- Dhangwatnotai, Roughgarden, and Yan, "Revenue Maximization with a Single
  Sample" (Games and Economic Behavior, 2015).
- Allouah and Besbes, "Sample-Based Optimal Pricing" (EC 2019).
- Tang, Tao, and Wang, "Pricing with a Hidden Sample" (2026):
  https://arxiv.org/abs/2602.18038

For the one-sample pricing problem, the Feng-Hartline-Li paper is the
primary reference for the revelation-gap comparison.  The 2026 hidden-sample
paper is best read as a related extension because it changes the mechanism
format from one-bid/sample-pricing mechanisms to richer distribution-report or
hidden-pricing mechanisms.
