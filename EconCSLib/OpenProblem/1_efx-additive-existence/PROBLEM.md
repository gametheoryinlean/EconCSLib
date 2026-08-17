---
name: EFX for Additive Valuations
contributor: Simina Branzei and Ariel Procaccia
---

## Existence of EFX Allocations for Additive Valuations

### Problem Description

In the **fair division of indivisible resources**, there is a set $M=\{1,\ldots,m\}$ of goods and a set $N=\{1,\ldots,n\}$ of agents. Each agent $i\in N$ has a valuation function $v\_i:2^M\rightarrow \mathbb{R}\_{\geq 0}$, typically assumed to be monotone. A valuation is **additive** if $v\_i(S) = \sum\_{j\in S} v\_i(\{j\})$ for all $S\subseteq M$.

An allocation $A=(A_1,A_2,\ldots,A_n)$ is a partition of the items among the agents. Because exact envy-freeness is generally unattainable with indivisible items (e.g., allocating a single diamond to two agents), the literature focuses on relaxations. The most promising candidate solution concept is **Envy-Free up to Any Good (EFX)**.

An allocation is **EFX** if no agent $i$ envies any other agent $j$ after the hypothetical removal of any single good $g$ from agent $j$'s bundle:

$$
v_i(A_i) \geq v_i(A_j \setminus \{g\}) \quad \text{for all } i, j \in N \text{ and for all } g \in A_j.
$$

### Known Results

**Positive Results:**

- Exact EFX allocations are guaranteed to exist for any number of agents with identical valuations, and for 3 agents with additive valuations (Chaudhury, Garg, and Mehlhorn, 2024).
- For additive valuations, an exact EFX allocation exists that leaves at most $n-2$ items unallocated to charity (Berger et al., 2022). The existence of $(1-\varepsilon)$-EFX allocations with $O((n/\varepsilon)^{1/2})$ charity for additive valuations has also been established (Akrami et al., 2024).
- Simulated annealing finds exact EFX allocations for additive valuations with random instances in experiments.

**Impossibility Results:**

- Akrami, Mayorov, Mehlhorn, Srinivas, and Weidenbach (2026) used SAT-solving to construct a counterexample showing that exact EFX allocations do not always exist for $n\geq 3$ agents and $m\geq n+5$ items with submodular (and general monotone) valuations. These counterexamples explicitly rely on submodular/subadditive complementarities and do not apply to additive valuations.
- Mackenzie and Suzuki (2026) provided a compact, human-verifiable counterexample for 3 agents and 8 items refuting EFX existence for weighted coverage (submodular) valuations, again not applicable to the additive case.

### Research Goal

Do exact EFX allocations always exist for the canonical case of **additive valuations** for $n\geq 4$ agents? The case of 3 agents is resolved (Chaudhury, Garg, and Mehlhorn, 2024), and for 3 types of agents is resolved as well. All known counterexamples to EFX existence are for more general types of valuations (submodular/subadditive), leaving the additive case as the central open question in fair division.

### Key References

* Akrami, Hannaneh, Noga Alon, Bhaskar Ray Chaudhury, Jugal Garg, Kurt Mehlhorn, and Ruta Mehta. "EFX: a simpler approach and an (almost) optimal guarantee via rainbow cycle number." Operations Research (2024).
* Akrami, Hannaneh, Ivan Mayorov, Kurt Mehlhorn, S. Srinivas, and Christoph Weidenbach. "A Counterexample to EFX: $n \ge 3$ Agents, $m \ge n+5$ Items, Submodular Valuations via SAT-Solving." arXiv Preprint (2026). Available at https://arxiv.org/abs/2604.18216.
* Chaudhury, Bhaskar Ray, Jugal Garg, and Kurt Mehlhorn. "EFX Exists for Three Agents." Journal of the ACM (2024).
* Plaut, Benjamin, and Tim Roughgarden. "Almost Envy-Freeness with General Valuations." SIAM Journal on Discrete Mathematics 34.2 (2020): 1039-1068.
* Vishwa Prakash HV, Pratik Ghosal, Prajakta Nimbhorkar, Nithin Varma. "EFX Exists for Three Types of Agents", ACM EC 2025, Available at https://arxiv.org/abs/2410.13580.
