---
name: Submodular Welfare Maximization with Demand Oracle
contributor: Renato Paes Leme
---

## Submodular Welfare Maximization with Demand Oracle: Breaking the $(1-1/e)$ Barrier

### Problem Description

In the **Submodular Welfare Maximization (SWM)** problem, we are given a set $M$ of $m$ indivisible items and $n$ agents. Each agent $i$ has a monotone submodular valuation function $v_i : 2^M \to \mathbb{R}_{\geq 0}$ with $v_i(\emptyset) = 0$. The goal is to find a partition (or allocation) of items $(S_1, S_2, \ldots, S_n)$ into $n$ disjoint subsets that maximizes the **social welfare**:

$$
\text{maximize} \quad \sum_{i=1}^n v_i(S_i).
$$

A function $v : 2^M \to \mathbb{R}_{\geq 0}$ is **monotone submodular** if:

- **Monotonicity**: $v(S) \leq v(T)$ for all $S \subseteq T \subseteq M$.
- **Submodularity (diminishing returns)**: $v(S \cup \{j\}) - v(S) \geq v(T \cup \{j\}) - v(T)$ for all $S \subseteq T \subseteq M$ and $j \notin T$.

The valuation functions are accessed through oracles. Two important oracle models are:

1\. **Value Oracle**: Given a set $S \subseteq M$, returns $v_i(S).$
2\. **Demand Oracle**: Given a price vector $p \in \mathbb{R}^m_{\geq 0}$, returns the set $S^* \in \arg\max\_{S \subseteq M} (v_i(S) - \sum\_{j \in S} p_j)$ that maximizes the agent's utility (value minus total price).

The demand oracle is strictly more powerful than the value oracle: a demand oracle can simulate a value oracle with polynomial overhead, but the converse is not true.

### Known Results

- **Value Oracle Model**: Vondrák (STOC 2008) proved that the optimal approximation ratio for the SWM problem in the value oracle model is exactly $1 - 1/e \approx 0.6321$. This is achieved by the continuous greedy algorithm combined with pipage rounding, and no algorithm using only value queries can do better.

- **Demand Oracle Model**: Feige and Vondrák (Theory of Computing, 2010) showed that the $1 - 1/e$ barrier can be broken in the demand oracle model. They designed an algorithm achieving an approximation ratio of $(1 - 1/e + \epsilon)$ for some small constant $\epsilon > 0$. Their approach combines the continuous greedy algorithm with a "correction" phase that uses demand queries to improve upon the $(1-1/e)$-approximate solution. The improvement $\epsilon$ obtained in their work is very small (roughly $\epsilon \approx 10^{-6}$ or smaller).

### Research Goal

Design an algorithm for the **Submodular Welfare Maximization** problem using **demand oracle queries** that achieves an approximation ratio of at least $1 - 1/e + 0.01 \approx 0.642$. That is, for any instance of SWM with monotone submodular valuations, the algorithm must output an allocation $(S_1, \ldots, S_n)$ such that:

$$
\mathbb{E}\left[\sum_{i=1}^n v_i(S_i)\right] \geq (1 - 1/e + 0.01) \cdot \text{OPT},
$$

where $\text{OPT} = \max_{(T_1, \ldots, T_n)} \sum_{i=1}^n v_i(T_i)$ is the value of the optimal allocation.

The algorithm should run in polynomial time in $n$ and $m$, using a polynomial number of demand oracle queries.

### Key Reference

Download the paper at https://theory.stanford.edu/~jvondrak/data/submod-improve.pdf and read it carefully before proceeding. This paper (Feige and Vondrák, "The Submodular Welfare Problem with Demand Queries", Theory of Computing, 2010) establishes the current state of the art and describes the algorithmic framework you should build upon.

Also consult:
- Vondrák, "Optimal Approximation for the Submodular Welfare Problem in the Value Oracle Model" (STOC 2008) — for the $1 - 1/e$ upper bound in the value oracle model and the continuous greedy algorithm.
