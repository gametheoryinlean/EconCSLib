---
name: MMS Approximation and Truthful Fair Allocation
contributor: Moshe Babaioff
---

## MMS Approximation and Truthful Fair Allocation

### Problem Description

Consider a fair-division instance with a set $N$ of $n$ agents and a set $M$ of indivisible goods. Each agent $i \in N$ has an additive valuation function $v\_i : 2^M \rightarrow \mathbb{R}\_{\geq 0}$, meaning that $v\_i(\emptyset) = 0$, $v\_i(\{g\}) \geq 0$ for every good $g \in M$, and $v\_i(S) = \sum\_{g \in S} v\_i(\{g\})$ for every bundle $S \subseteq M$.

### Maximin Share (MMS)

The **maximin share** of agent $i$ with respect to $n$ agents and goods $M$ is

$$
\text{MMS}_i(n, M) = \max_{(A_1, \ldots, A_n)} \min_{j \in [n]} v_i(A_j),
$$

where the maximum is taken over all partitions of $M$ into $n$ bundles.

An allocation $X = (X_1, \ldots, X_n)$ is an **$\alpha$-MMS allocation** if, for every agent $i \in N$,

$$
v_i(X_i) \geq \alpha \cdot \text{MMS}_i(n, M).
$$

It is known that for $n = 3$ additive agents, an exact MMS allocation (i.e., $\alpha = 1$) might not exist (Kurokawa, Procaccia, and Wang, 2018).

### Truthful Mechanisms

A deterministic mechanism is **(dominant-strategy) truthful** if no agent can benefit from misreporting her valuation, regardless of the reports of the other agents.

A randomized mechanism is **truthful in expectation (TIE)** if no agent can increase her expected utility by misreporting, regardless of the reports of the other agents.

### Known Results

### MMS Approximation (without incentives)

Exact MMS allocations do not always exist, even for three additive agents (Kurokawa, Procaccia, and Wang, 2018). The best known approximation guarantees for $\alpha$-MMS allocations with additive agents have been steadily improved through a sequence of works. The current best approximation factor is $7/9$ (Huang and Zhou, 2025).

### Truthful Mechanisms

- **Deterministic truthful mechanisms.** Babaioff and Manaker Morag (2025) study the limits of fairness achievable by deterministic truthful mechanisms. Their results are based on a characterization that requires the mechanism to be "non-bossy" and "neutral." Under these assumptions, they establish bounds on the best MMS approximation achievable by deterministic truthful mechanisms for $n$ additive agents (when goods can be left unallocated). It is open whether removing these structural restrictions enables better guarantees. Earlier work by Amanatidis et al. (2017) showed that 2-agent deterministic truthful mechanisms that allocate all goods cannot be fair.

- **Randomized TIE mechanisms.** Babaioff, Feige, and Manaker Morag (2026) show that a truthful-in-expectation mechanism can achieve a $1/\log(n)$ ex-post MMS guarantee. Bu and Tao (2025) show that a TIE mechanism can achieve a $1/n$ MMS guarantee.

### Research Goals

**Open Problem 1 (MMS approximation).** Find the best $\alpha$ such that an $\alpha$-MMS allocation is guaranteed to exist for every instance with $n$ additive agents. Furthermore, determine the best $\alpha$ for which such an allocation can be computed in polynomial time.

**Open Problem 2 (Truthful and fair allocation).** What are the limits of fairness achievable by (dominant-strategy) truthful mechanisms?

Specifically:

**Open Problem 2a.** What is the best MMS approximation that a deterministic truthful mechanism can obtain for $n$ additive agents (when goods can be left unallocated)? In particular, do the known bounds (Babaioff and Manaker Morag, 2025), which rely on non-bossiness and neutrality, extend to all deterministic truthful mechanisms?

**Open Problem 2b.** What is the best MMS approximation that a randomized truthful-in-expectation mechanism can ensure? The best known result achieves a $1/\log(n)$ ex-post MMS guarantee (Babaioff, Feige, and Manaker Morag, 2026). Can this be improved, and what is achievable by polynomial-time mechanisms?

### Key References

- Moshe Babaioff and Noam Manaker Morag. "On Truthful Mechanisms without Pareto-efficiency: Characterizations and Fairness". In: Proceedings of the 26th ACM Conference on Economics and Computation. 2025, p. 447.

- Moshe Babaioff, Uriel Feige, and Noam Manaker Morag. "Truthful-in-Expectation Mechanisms for MMS Approximation". 2026. arXiv: 2604.27211 [cs.GT]. https://arxiv.org/abs/2604.27211.

- Xin Huang and Shengwei Zhou. An FPTAS for 7/9-Approximation to Maximin Share Allocations. 2025. arXiv: 2511.13056 [cs.GT]. https://arxiv.org/abs/2511.13056.

- David Kurokawa, Ariel D. Procaccia, and Junxing Wang. "Fair Enough: Guaranteeing Approximate Maximin Shares". In: J. ACM 65.2 (2018), 8:1–8:27.

- Georgios Amanatidis, Georgios Birmpas, George Christodoulou, and Evangelos Markakis. "Truthful Allocation Mechanisms Without Payments: Characterization and Implications on Fairness". In: ACM Conference on Economics and Computation (ACM-EC). 2017, pp. 545–562.

- Xiaolin Bu and Biaoshuai Tao. "Truthful and Almost Envy-Free Mechanism of Allocating Indivisible Goods: the Power of Randomness". In: 2025 IEEE 66th Annual Symposium on Foundations of Computer Science (FOCS). 2025, pp. 2766–2795.
