---
name: Revelation Gap for Public-Budget Welfare Maximization
contributor: Jason Hartline
---

## Revelation Gap for Public-Budget Welfare Maximization

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

### Problem Description - Closing the 1.013-to-$e$ Gap

In **single-item welfare maximization with public-budget agents**, there are
$n$ agents competing for one item.  Agent $i$'s value is drawn i.i.d. from
an unknown distribution $F$.  All agents share the same public budget $B$.
An agent with value $v$, allocation probability $x$, and payment $p$ has
utility:

$$
vx-p
$$

if $p\le B$, and utility $-\infty$ if $p>B$.  The hard public budget
means that ordinary welfare-maximizing allocation rules may not be
implementable with feasible payments.

For this problem, $M(F)$ is expected welfare:

$$
M(F) =
  \mathbb{E}_{\mathbf{v}\sim F^n}
  \left[\sum_i v_i x_i(\mathbf{v})\right].
$$

The benchmark $\mathrm{OPT}_F(F)$ is the welfare of the Bayesian
welfare-optimal mechanism tailored to distribution $F$.  The
prior-independent mechanism $M$ must be fixed before $F$ is known.

The central comparison is:
- **All mechanisms**: prior-independent mechanisms, including non-revelation
  auctions whose Bayes-Nash equilibria depend on $F$.
- **Revelation mechanisms**: prior-independent truthful or direct mechanisms.

### Known Results

- **All-pay is prior-independent and optimal for regular public-budget
  agents.**  Feng and Hartline (2018) show that for i.i.d. public-budget
  regular agents, the all-pay auction has a unique equilibrium that implements
  the Bayesian optimal welfare outcome.  Since the all-pay auction does not
  depend on $F$, it is prior-independent and
  $\beta(\mathcal{M}_{\mathrm{all}},\mathcal{D}_{\mathrm{PB}})=1$.

- **Truthful prior-independent mechanisms are separated from all-pay.**  For
  two uniform public-budget agents with budget normalized to one, Feng and
  Hartline identify the Bayesian optimal DSIC mechanism as the middle-ironed
  clinching auction and compare it to the BIC/all-pay optimum.  This gives a
  lower bound of about
  $\beta(\mathcal{M}_{\mathrm{rev}},\mathcal{D}_{\mathrm{PB}})\ge 1.013$.

- **Clinching gives the best known general truthful upper bound.**  The
  clinching auction is prior-independent and truthful, and Feng and Hartline
  prove that it is an $e$-approximation for i.i.d. public-budget regular
  agents:
  $\beta(\mathcal{M}_{\mathrm{rev}},\mathcal{D}_{\mathrm{PB}})\le e$.

- **Known public-budget revelation-gap interval.**  Because the all-mechanism side is
  exactly $1$, the known revelation gap for public-budget welfare is:

$$
1.013
  \le
  \frac{\beta(\mathcal{M}_{\mathrm{rev}},\mathcal{D}_{\mathrm{PB}})}
       {\beta(\mathcal{M}_{\mathrm{all}},\mathcal{D}_{\mathrm{PB}})}
  \le
  e.
$$

- **Extensions are known but not tight.**  Feng and Hartline also discuss
  irregular distributions, position environments, and revenue variants.  For
  irregular distributions, the corresponding approximation bounds degrade by a
  factor of two in the known analysis.

### Research Goal

Determine the exact truthful prior-independent approximation factor for
i.i.d. public-budget regular agents.  Since the all-mechanism optimum is
already $1$, this is exactly the problem of identifying the tight revelation
gap:

$$
\text{tight revelation gap} =
  \beta(\mathcal{M}_{\mathrm{rev}},\mathcal{D}_{\mathrm{PB}}).
$$

Concrete open questions:
- Can the clinching upper bound be improved from $e$ to a constant close to
  the known $1.013$ lower bound?
- Is the clinching auction, or a variant such as middle-ironed clinching,
  optimal among prior-independent revelation mechanisms?
- Does the middle-ironed clinching optimality proof extend beyond the
  two-agent uniform instance to broader regular distributions?
- What is the tight revelation gap for the revenue objective with public
  budgets?
- What are the exact regular and irregular public-budget gaps in position
  environments?

### Key Reference

The primary reference is Feng and Hartline, "An End-to-end Argument in
Mechanism Design (Prior-independent Auctions for Budgeted Agents)," FOCS 2018:
https://arxiv.org/abs/1804.01977

This paper introduces the revelation-gap viewpoint, proves all-pay optimality
on the non-revelation side, proves the $1.013$ truthful lower bound, and
gives the clinching $e$-approximation upper bound.
