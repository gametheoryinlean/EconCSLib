---
name: Prophet Inequality for Subadditive CA
contributor: Paul Duetting
---

## Constant-Factor Prophet Inequality for Subadditive Combinatorial Auctions via Static Item Pricing

### Problem Description

Consider a combinatorial auction with a set $M$ of $m$ items and a set $N$ of $n$ buyers. Each buyer $i \in N$ has a valuation function $v_i : 2^M \to \mathbb{R}\_{\geq 0}$. We assume that each $v_i$ is drawn independently from a known prior distribution $\mathcal{D}_i$. The buyers arrive online in a fixed (or adversarial) order.

We focus on **subadditive** valuations, meaning that for any buyer $i$ and any two bundles $S, T \subseteq M$, $v_i(S \cup T) \leq v_i(S) + v_i(T)$.

The seller wishes to post **static item prices** $p \in \mathbb{R}\_{\geq 0}^m$. When buyer $i$ arrives, they observe the remaining set of unsold items $M_i \subseteq M$ and the prices $p$, and select a bundle $S_i \subseteq M_i$ that maximizes their quasi-linear utility:

$$
S_i \in \arg\max_{S \subseteq M_i} \left( v_i(S) - \sum_{j \in S} p_j \right)
$$

The benchmark is the expected offline optimal social welfare: $\mathbb{E}[\text{OPT}] = \mathbb{E}\left[\max_{(O_1, \dots, O_n)} \sum_{i \in N} v_i(O_i)\right]$, where $(O_1, \dots, O_n)$ is a valid partition of the items.

### Research Goal

Does there exist a universal constant $C > 0$ such that, for any set of items $M$ and any set of independent subadditive valuation distributions $\{\mathcal{D}_i\}_{i \in N}$, there exists a static item price vector $p \in \mathbb{R}_{\geq 0}^m$ guaranteeing an expected social welfare of at least $\frac{1}{C} \mathbb{E}[\text{OPT}]$?

**Qualifications and Assumptions:**

- **(a) Arrival Order:** The problem is open even for a fixed and known arrival order. Most results typically work for any (worst-case) arrival order, and some also under adversarial arrival order.
- **(b) Computational Tractability:** For the core of this open problem, we are entirely unconcerned with computational tractability. The question is purely existential: does such a price vector exist?
- **(c) Tie-Breaking Rules:** Because buyers may have multiple utility-maximizing bundles, a tie-breaking rule must be specified. Ideally, the pricing scheme should be robust enough that **any** tie-breaking rule (even adversarial) works. However, resolving the problem affirmatively under specific assumptions (e.g., lexicographical tie-breaking, or seller-favorable tie-breaking) would still be highly interesting and a significant step forward, while a negative result that only holds for specific tie-breaking rules would be weaker.

### Known Results

- **Constant-Factor for XOS via Static Pricing:** Feldman, Gravin, and Lucier (2014) demonstrate a constant-factor approximation for the narrower class of XOS (fractionally subadditive) valuations using static posted prices. This serves as the blueprint for the type of result we hope to achieve (or refute) for general subadditive valuations. The factor 2 impossibility from the classic single-item prophet inequality is the best known impossibility. Showing a stronger lower bound would be interesting as well.

- **SOTA Static Pricing for Subadditive:** If we restrict ourselves strictly to static posted pricing, the current state-of-the-art for subadditive valuations yields an $\mathcal{O}(\log \log m)$ approximation (Dütting, Feldman, Kesselheim, and Lucier, 2020).

- **Constant-Factor for Subadditive (Non-Static):** A breakthrough by Correa and Cristi (2023) gives an $\mathcal{O}(1)$ prophet inequality for subadditive valuations. However, this result is not achieved via static posted pricing, but rather relies on more complex dynamic pricing mechanisms.

- **General Reductions to Posted Prices:** Recent work (Dütting et al., 2023) establishes a general reduction that can turn prophet inequalities into posted-price mechanisms. However, this reduction inherently relies on dynamic pricing and does not guarantee the existence of **static** prices.

- **Polynomial-Time Results for XOS:** While our open problem suspends computational constraints, it is worth noting that for XOS valuations, constant-factor approximations via static pricing can be achieved in polynomial time given suitable oracle access to the valuations (Dütting, Feldman, Kesselheim, and Lucier, 2016).

### Key References

Download the following papers read them carefully before proceeding.

1. Feldman, Gravin, and Lucier, "Combinatorial Auctions via Posted Prices" (2014). Available at https://arxiv.org/pdf/1411.4916 — establishes the constant-factor result for XOS via static pricing.

2. Dütting, Feldman, Kesselheim, and Lucier, "Prophet Inequalities Made Easy" (2020). Available at https://arxiv.org/pdf/2004.09784 — current state-of-the-art $\mathcal{O}(\log \log m)$ approximation for subadditive via static pricing.

3. Correa and Cristi, "Prophet Inequalities for Subadditive Combinatorial Auctions" (2023). Available at https://www.dii.uchile.cl/~jcorrea/papers/Manuscripts/2023CC.pdf — breakthrough $\mathcal{O}(1)$ prophet inequality for subadditive (non-static).

Also consult:
- "Prophet Inequalities vs. Posted-Price Mechanisms" (2023). Available at https://livrepository.liverpool.ac.uk/3177238/1/Prophet\_Pricing\_Accepted.pdf — general reduction from prophet inequalities to dynamic posted prices.
- Dütting, Feldman, Kesselheim, and Lucier, "Polynomial-Time Approximation Schemes for XOS Combinatorial Auctions" (2016). Available at https://arxiv.org/pdf/1612.03161 — polynomial-time results for XOS.
