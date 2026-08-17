---
name: EFX Approximation, Charity, and Chores
contributor: Simina Branzei
---

## Envy-Freeness up to Any Good (EFX): Approximations, Charity, and Chores

### Problem Description

In the **fair division of indivisible resources**, there is a set $M=\{1,\ldots,m\}$ of items and a set $N=\{1,\ldots,n\}$ of agents. Each agent $i\in N$ has a valuation function $v_i:2^M\rightarrow \mathbb{R}\_{\geq 0}$ (for goods) or a cost function $c_i:2^M\rightarrow \mathbb{R}\_{\geq 0}$ (for chores), typically assumed to be monotone. Common classes of valuations include additive, submodular, and subadditive.

An allocation $A=(A_1,A_2,\ldots,A_n)$ is a partition of the items among the agents. Because exact envy-freeness is generally unattainable with indivisible items (e.g., allocating a single diamond to two agents), the literature focuses on relaxations. The most promising candidate solution concept is **Envy-Free up to Any Good (EFX)**.

An allocation is **EFX for goods** if no agent $i$ envies any other agent $j$ after the hypothetical removal of any single good $g$ from agent $j$'s bundle:

$$
v_i(A_i) \geq v_i(A_j \setminus \{g\}) \quad \text{for all } i, j \in N \text{ and for all } g \in A_j.
$$

Symmetrically, an allocation is **EFX for chores** if agent $i$'s envy toward another agent $j$ is eliminated if any single chore is removed from agent $i$'s own bundle:

$$
c_i(A_i \setminus \{g\}) \leq c_i(A_j) \quad \text{for all } i, j \in N \text{ and for all } g \in A_i.
$$

Because exact EFX allocations are not guaranteed to exist for all valuation classes, several meaningful variants are studied:

- **$\alpha$-Approximate EFX**: For goods, an allocation is $\alpha$-EFX (for $\alpha\in[0,1]$) if $v_i(A_i)\geq \alpha\cdot v_i(A_j\setminus\{g\})$ for all $i,j\in N$ and $g\in A_j$. The notion is similarly defined for chores.

- **EFX with Charity**: A partial allocation where a subset of items $C\subset M$ is left unallocated (donated to "charity"), ensuring the allocation of the remaining items is exactly EFX, while minimizing the size of the charity $|C|$.

### Known Results

**Positive Results and Algorithms:**

- $1/2$-EFX allocations exist for subadditive valuations (Plaut and Roughgarden, 2020).
- For additive valuations, an exact EFX allocation exists that leaves at most $n-2$ items unallocated to charity (Berger et al., 2022). The existence of $(1-\varepsilon)$-EFX allocations with $O((n/\varepsilon)^{1/2})$ charity for additive valuations has also been established (Akrami et al., 2024).

**Impossibility Results:**

- Akrami, Mayorov, Mehlhorn, Srinivas, and Weidenbach (2026) used SAT-solving to construct a counterexample showing that in the case of goods, exact EFX allocations do not always exist for $n\geq 3$ agents and $m\geq n+5$ items with submodular (and general monotone) valuations. They also proved EFX does always exist for 3 agents with up to 7 items.
- Mackenzie and Suzuki (2026) provided a compact, human-verifiable, and highly symmetric counterexample for 3 agents and 8 goods, refuting EFX existence for the well-structured class of weighted coverage (submodular) valuations.
- He and Tao (2026) showed that for the case of bads with additive costs, an exact EFX allocation is not guaranteed to exist.

**Limits of Approximation:**

- While $1/2$-EFX allocations are known to exist for subadditive valuations, Mackenzie and Suzuki (2026) established that no universally guaranteed $\alpha$-EFX allocation exists for any $\alpha > 2^{-1/6} \approx 0.891$ under monotone subadditive valuations.

### Research Goal

Even though there are now counterexamples demonstrating that exact EFX allocations do not universally exist for non-additive valuations, the quest to identify the limits of fair division remains very rich. Key research directions include:

(1) **Closing the Approximation Gap**: For monotone submodular and subadditive valuations, the best universal guarantee lies somewhere between $1/2$ (the known constructive lower bound) and $\approx 0.891$ (the impossibility upper bound). What is the tightest universally guaranteed approximation ratio $\alpha$?

(2) **Minimizing Charity**: Design an allocation mechanism that guarantees exact EFX while strictly bounding the number of items given to charity. What is the theoretical minimum number of items that must be given to charity to achieve EFX for submodular valuations?

(3) **EFX for Chores**: Translate these existence questions and approximation barriers to the domain of indivisible chores. What is the best possible approximation ratio $\alpha$, and what is the minimal charity required to reach exact EFX for chores?

### Key References

* Akrami, Hannaneh, Noga Alon, Bhaskar Ray Chaudhury, Jugal Garg, Kurt Mehlhorn, and Ruta Mehta. "EFX: a simpler approach and an (almost) optimal guarantee via rainbow cycle number." Operations Research (2024).
* Akrami, Hannaneh, Ivan Mayorov, Kurt Mehlhorn, S. Srinivas, and Christoph Weidenbach. "A Counterexample to EFX: $n \ge 3$ Agents, $m \ge n+5$ Items, Submodular Valuations via SAT-Solving." arXiv Preprint (2026). Available at https://arxiv.org/abs/2604.18216.
* Amanatidis, Georgios, Haris Aziz, Georgios Birmpas, Aris Filos-Ratsikas, Bo Li, Hervé Moulin, Alexandros A. Voudouris, and Xiaowei Wu. "Fair division of indivisible goods: Recent progress and open questions." Artificial Intelligence (2023).
* Chaudhury, Bhaskar Ray, Jugal Garg, and Kurt Mehlhorn. "EFX Exists for Three Agents." Journal of the ACM (2024).
* Chaudhury, Bhaskar Ray, Telikepalli Kavitha, Kurt Mehlhorn, and Alkmini Sgouritsa. "A Little Charity Guarantees Almost Envy-Freeness." SIAM Journal on Computing (2021).
* Mackenzie, Simon, and Mashbat Suzuki. "Counterexamples to EFX for Submodular and Subadditive Valuations." arXiv Preprint (2026).
* Plaut, Benjamin, and Tim Roughgarden. "Almost Envy-Freeness with General Valuations." SIAM Journal on Discrete Mathematics 34.2 (2020): 1039-1068.
* Wentao He and Biaoshuai Tao. "EFX for Additive Chores: Nonexistence, Pareto Incompatibility, and Bi-Valued Existence". arXiv Preprint https://arxiv.org/pdf/2606.08872.
