---
name: Truthful Mechanism for Submodular CA
contributor: Sebastien Lahaie
---

## Truthful Mechanism for Submodular Combinatorial Auctions: Closing the Gap to $O(\log \log m)$

### Problem Description

In a **combinatorial auction**, there is a set $M$ of $m$ indivisible items and a set $N$ of $n$ bidders. Each bidder $i \in N$ has a **monotone submodular** valuation function $v_i : 2^M \to \mathbb{R}\_{\geq 0}$ with $v_i(\emptyset) = 0$, satisfying:
- **Monotonicity**: $v_i(S) \leq v_i(T)$ for all $S \subseteq T \subseteq M$.
- **Submodularity (diminishing returns)**: $v_i(S \cup \{j\}) - v_i(S) \geq v_i(T \cup \{j\}) - v_i(T)$ for all $S \subseteq T \subseteq M$ and $j \notin T$.

The goal is to find an allocation $(S_1, S_2, \ldots, S_n)$ that is a partition of the items among the bidders, maximizing the **social welfare**:

$$
\text{maximize} \quad \sum_{i=1}^n v_i(S_i).
$$

The valuations are private information of the bidders, accessed through **demand oracle queries**: given a price vector $p \in \mathbb{R}^m\_{\geq 0}$, the oracle for bidder $i$ returns $S^* \in \arg\max\_{S \subseteq M} \left(v_i(S) - \sum_{j \in S} p_j\right)$.

A mechanism is **(universally) truthful** if it is a probability distribution over deterministic truthful mechanisms—i.e., no bidder can improve their outcome by misreporting their valuation, regardless of the mechanism's random coins.

The **approximation ratio** of a truthful mechanism is the worst-case ratio between the expected social welfare achieved by the mechanism and the optimal social welfare $\text{OPT} = \max_{(S_1, \ldots, S_n)} \sum_{i=1}^n v_i(S_i)$.

### Known Results

- **Non-Truthful Algorithms:** Without the truthfulness constraint, monotone submodular welfare maximization can be approximated to within a factor of $1 - 1/e \approx 0.632$ using the continuous greedy algorithm with value queries (Vondrák, STOC 2008). This is tight in the value oracle model.

- **Known Truthful Mechanisms:** The quest for truthful mechanisms with good approximation ratios has a long history:
 - $O(\sqrt{m})$-approximation (Dobzinski, Nisan, and Schapira, 2005\)
 - $O(\log^2 m)$-approximation (Dobzinski, Nisan, and Schapira, 2006\)
 - $O(\log m \cdot \log \log m)$-approximation (Dobzinski, 2007\)
 - $O(\log m)$-approximation (Krysta and Vöcking, 2012\)
 - $O(\sqrt{\log m})$-approximation (Dobzinski, 2016\)
 - $O((\log \log m)^3)$-approximation (Assadi, Kesselheim, and Singla, 2021))

For the special case of **submodular** bidders, an improved analysis yields an $O((\log \log m)^2)$-approximation. This is the current state of the art.

### Research Goal

Design a **(universally) truthful** mechanism for combinatorial auctions with **monotone submodular valuations** that achieves an $O(\log \log m)$-approximation to the optimal social welfare, using a polynomial number of demand oracle queries. That is, construct a mechanism such that for any instance:

$$
\mathbb{E}\left[\sum_{i=1}^n v_i(S_i)\right] \geq \Omega\left(\frac{1}{\log \log m}\right) \cdot \text{OPT},
$$

where the expectation is over the mechanism's internal randomness.

This would improve upon the current best $O((\log \log m)^2)$-approximation of Assadi, Kesselheim, and Singla (SODA 2021\) by removing one $\log \log m$ factor. Possible directions include:
- Tightening the analysis of the existing mechanism from Assadi, Kesselheim, and Singla, which loses a $\log \log m$ factor in bounding the welfare contribution across "levels" of their hierarchical grouping scheme.
- Designing a new mechanism with a refined hierarchical decomposition or bundling strategy that avoids the extra logarithmic loss.
- Combining ideas from the non-truthful $O(\log \log m)$-approximation algorithms (which exist for the broader subadditive class via prophet inequality techniques) with truthfulness-preserving reductions.

### Key References

Download the following paper and read it carefully before proceeding.

1\. Assadi, Kesselheim, and Singla, "Improved Truthful Mechanisms for Subadditive Combinatorial Auctions: Breaking the Logarithmic Barrier" (SODA 2021). Available at https://arxiv.org/pdf/2010.01420 — establishes the current-best $O((\log \log m)^3)$ approximation for subadditive and $O((\log \log m)^2)$ for submodular bidders.

Also consult:
- Dobzinski, "Breaking the Logarithmic Barrier for Truthful Combinatorial Auctions with Submodular Bidders" (STOC 2016). Available at https://arxiv.org/pdf/1602.08194 — the $O(\sqrt{\log m})$ predecessor mechanism.
- Vondrák, "Optimal Approximation for the Submodular Welfare Problem in the Value Oracle Model" (STOC 2008\) — the non-truthful $1 - 1/e$ benchmark.
- Dughmi and Vondrák, "Limitations of Randomized Mechanisms for Combinatorial Auctions" (Games and Economic Behavior, 2015). Available at https://arxiv.org/pdf/1011.3321 — impossibility results for truthful mechanisms.
