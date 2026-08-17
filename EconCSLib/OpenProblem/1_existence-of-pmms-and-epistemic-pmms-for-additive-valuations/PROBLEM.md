---
name: Existence of PMMS and Epistemic PMMS for Additive Valuations
contributor: Michal Feldman
---

## Existence of PMMS and Epistemic PMMS for Additive Valuations

### Problem Description

Consider a fair-division instance with a set $N$ of $n$ agents and a set $M$ of indivisible goods. Each agent $i \in N$ has an additive valuation function $v_i : 2^M \rightarrow \mathbb{R}_{\geq 0}$, meaning that

$$
v_i(S) = \sum_{g \in S} v_i(g)
$$

for every bundle $S \subseteq M$.

For a set of goods $S$, the two-way maximin share of agent $i$ is defined as

$$
\mu_i(2,S)=\max_{(A,B)} \min\{v_i(A),v_i(B)\},
$$

where the maximum is taken over all partitions of $S$ into two bundles.

### PMMS

An allocation $X=(X_1,\ldots,X_n)$ is **pairwise maximin share fair** (PMMS) if, for every pair of agents $i,j \in N$,

$$
v_i(X_i)\geq \mu_i(2,X_i\cup X_j).
$$

Equivalently, if agents $i$ and $j$ pool their allocated goods and agent $i$ acts as the cutter in a cut-and-choose procedure, then agent $i$ should already receive at least the value she could guarantee herself.

### Epistemic PMMS

Epistemic PMMS (EPMMS) is a relaxation of PMMS inspired by the epistemic approach to fairness. We say that an allocation $X=(X_1,\ldots,X_n)$ is **epistemic PMMS** (EPMMS) if, for every agent $i$, there exists a hypothetical allocation

$$
Y^i=(Y^i_1,\ldots,Y^i_n)
$$

such that $Y^i_i=X_i$ and agent $i$ is PMMS-satisfied with respect to $Y^i$. Formally, for every agent $j$,

$$
v_i(X_i)\geq \mu_i(2,Y^i_i\cup Y^i_j).
$$

Thus, each agent can certify the fairness of her own bundle by imagining a suitable repartition of the goods allocated to the other agents. The actual allocation need not satisfy PMMS.

### Known Results

### PMMS

PMMS was introduced by Caragiannis et al. and is known to be a strengthening of EFX. Under mild assumptions, every PMMS allocation is also EFX. Exact PMMS allocations are known to exist in several restricted settings, including binary-valued valuations, pair-demand valuations, and instances in which each item has positive value for at most two agents.

For general additive valuations, however, the existence of PMMS allocations remains unresolved. The best known approximation guarantee is $0.781$-PMMS due to Kurokawa. Earlier work showed that Nash-welfare-maximizing allocations guarantee $0.618$-PMMS. Despite substantial progress on approximation algorithms, no exact existence result is known.

### Epistemic PMMS

EPMMS was introduced by Feldman, Fiat, Nissan, and Ponitka (2026) as an epistemic relaxation of PMMS. Unlike PMMS, exact EPMMS allocations are known to exist in several settings where PMMS remains open.

For additive valuations, every instance admits a polynomial-time computable $4/5$-EPMMS allocation. Exact EPMMS allocations are known to exist for several important special cases, including:
- bivalued valuations (indeed, a stronger EGMMS allocation exists),
- instances with three additive agents,
- instances with two types of additive agents.

These results suggest that the epistemic relaxation substantially increases the scope of instances for which exact fairness guarantees can be obtained.

### Research Goals

**Open Problem 1.** Does every fair-division instance with additive valuations admit a PMMS allocation?

**Open Problem 2.** Does every fair-division instance with additive valuations admit an EPMMS allocation?

The second question asks whether the epistemic relaxation is sufficient to overcome the difficulties that have so far prevented a proof of PMMS existence. A positive answer would provide a strong fairness guarantee for all additive instances while retaining much of the conceptual appeal of PMMS. A negative answer would demonstrate an inherent limitation of the epistemic approach and identify a setting in which even individualized fairness certificates are insufficient to guarantee existence.

### Key Reference

- Michal Feldman, Amos Fiat, Yael Nissan, and Tomasz Ponitka, "Epistemic Pairwise Maximin Share," 2026: https://arxiv.org/abs/2606.18921
