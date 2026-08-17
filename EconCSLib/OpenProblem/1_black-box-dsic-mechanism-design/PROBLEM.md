---
name: Black-Box Reductions to DSIC Mechanism Design
contributor: Brendan Lucier
---

## Black-Box Reductions from Algorithm Design to DSIC Mechanism Design

### Problem Description

Consider $n$ agents with **single-dimensional types**: each agent $i$ has a private value $v_i \in \mathbb{R}\_{\geq 0}$, drawn independently from a known distribution $F_i$. An **algorithm** $\mathcal{A}$ maps a vector of values $(v_1, \ldots, v_n)$ to an allocation $(x_1, \ldots, x_n) \in [0,1]^n$, subject to an unknown feasibility constraint. The **social welfare** of an allocation is $\sum\_{i=1}^{n} v_i \cdot x_i$.

A **simulator** has black-box (oracle) access to $\mathcal{A}$: given any valuation profile, it can query $\mathcal{A}$ to obtain the corresponding allocation. The simulator knows only that any allocation returned by $\mathcal{A}$ is feasible, but has no other knowledge of the feasibility constraint.

A mechanism is **dominant-strategy incentive compatible (DSIC)** if truthful reporting is a dominant strategy for every agent, regardless of what other agents report.

The goal is to design a simulator that, given oracle access to $\mathcal{A}$, produces a **DSIC mechanism** whose **expected total welfare** $\mathbb{E}\left[\sum_{i} v_i \cdot x_i\right]$ (over the randomness of the type distributions and any internal randomness) is at least the expected total welfare of the original algorithm $\mathcal{A}$.

### Known Results

**Positive Results:**

- Hartline and Lucier (2009) showed that for single-parameter agent settings, there is a general **black-box reduction** that converts any approximation algorithm into a **Bayesian incentive compatible (BIC)** mechanism with essentially the same expected welfare. This solves the BIC variant of the problem.

**Impossibility Results:**

- Gergatsouli, Lucier, and Tzamos (2019) showed that no polynomial-time black-box reduction exists for the stronger notion of **Max-In-Distributional-Range (MIDR)** mechanisms in the single-parameter setting: achieving a sub-polynomial approximation to the expected welfare requires exponentially many queries.
- Chawla, Immorlica, and Lucier (2012) showed that a black-box reduction for the social welfare objective is **not possible** if the resulting mechanism is required to be truthful in expectation (i.e., DSIC) and to **preserve the worst-case approximation ratio** of the original algorithm to within a sub-polynomial factor. They also proved that for other objectives such as makespan, no black-box reduction is possible even under BIC with average-case guarantees.

**Gap:**

- The BIC variant is solved (Hartline and Lucier, 2009). The MIDR variant is impossible (Gergatsouli, Lucier, and Tzamos, 2019). Preserving the worst-case approximation ratio under DSIC is impossible (Chawla, Immorlica, and Lucier, 2012). However, it remains open whether a black-box reduction to a **DSIC** mechanism that preserves **expected welfare** (not worst-case approximation) is possible.

### Research Goal

Does there exist a black-box reduction that, given oracle access to an algorithm $\mathcal{A}$ for a single-parameter welfare maximization problem with independently distributed agent types, simulates a **DSIC mechanism** whose expected social welfare matches that of $\mathcal{A}$? The simulator has query access to $\mathcal{A}$ and knowledge of the type distributions, but no explicit knowledge of the feasibility constraint beyond what $\mathcal{A}$ reveals through its outputs.

### Key References

* Gergatsouli, Evangelia, Brendan Lucier, and Christos Tzamos. "The Complexity of Black-Box Mechanism Design with Priors." arXiv Preprint (2019). Available at https://arxiv.org/abs/1906.10794.
* Hartline, Jason D., and Brendan Lucier. "Bayesian Algorithmic Mechanism Design." STOC 2010 / American Economic Review (2015). Available at https://arxiv.org/abs/0909.4756.
* Chawla, Shuchi, Nicole Immorlica, and Brendan Lucier. "On the Impossibility of Black-Box Transformations in Mechanism Design." STOC 2012. Available at https://arxiv.org/abs/1109.2067.
