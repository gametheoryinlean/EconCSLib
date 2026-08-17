---
name: Online Submodular Welfare  in Random Order
contributor: Vahab Mirrokni
---

## Online Submodular Welfare Maximization in Random Order: Breaking the $1/2$ Barrier

### Problem Description

In the **Online Submodular Welfare Maximization** problem, we are given $m$ agents, each with a monotone submodular valuation function $v_\ell : 2^{[n]} \to \mathbb{R}_{\geq 0}$ with $v_\ell(\emptyset) = 0$. A set of $n$ items arrives **one at a time** in an online fashion. When item $j$ arrives, the algorithm must make an **immediate, irrevocable** decision about which agent to assign it to, without knowledge of future items.

A function $v : 2^{[n]} \to \mathbb{R}_{\geq 0}$ is **monotone submodular** if:
- **Monotonicity**: $v(S) \leq v(T)$ for all $S \subseteq T$.
- **Submodularity (diminishing returns)**: $v(S \cup \{j\}) - v(S) \geq v(T \cup \{j\}) - v(T)$ for all $S \subseteq T$ and $j \notin T$.

The goal is to maximize the **social welfare** $\sum_{\ell=1}^m v_\ell(S_\ell)$, where $S_\ell$ is the set of items assigned to agent $\ell$.

**Arrival order models:**
- **Adversarial order**: The adversary chooses both the instance and the arrival order. In this model, no algorithm can achieve a competitive ratio better than $1/2$ for general monotone submodular valuations.
- **Random order**: The adversary chooses the instance (items and valuation functions), but the items arrive in a **uniformly random permutation**. This is the model we study.

The **competitive ratio** of an online algorithm $\text{ALG}$ is:

$$
\rho = \inf_{\text{instances}} \frac{\mathbb{E}[\text{ALG}]}{\text{OPT}},
$$

where $\text{OPT}$ is the optimal offline social welfare and the expectation is over the random arrival order (and any randomness of the algorithm).

### Known Results

- **Adversarial order**: The simple greedy algorithm (assign each arriving item to the agent with the highest marginal value) achieves a competitive ratio of $1/2$, and this is tight for adversarial order.

- **Random order**: Korula, Mirrokni, and Zadimoghaddam (2017) showed that the greedy algorithm achieves a competitive ratio of at least $0.505$ in the random order model, resolving a longstanding open problem of whether the $1/2$ barrier could be broken. For special cases (weighted matching, weighted coverage, "second-order supermodular" functions), they achieve $0.51$.

- **Secretary-style algorithms**: The problem is closely related to the $m$-secretary problem and online matching. For the special case of unit-demand (matching) valuations, better ratios are known.

### Research Goal

Design an algorithm for the **Online Submodular Welfare Maximization** problem in the **random order model** that achieves a competitive ratio of at least $1/2 + 0.01 = 0.51$. That is, for any instance with monotone submodular valuations, the algorithm must produce an allocation satisfying:

$$
\mathbb{E}\left[\sum_{\ell=1}^m v_\ell(S_\ell)\right] \geq 0.51 \cdot \text{OPT},
$$

where the expectation is over the uniformly random arrival order and any internal randomness of the algorithm.

The algorithm may use the greedy approach as a starting point, but significant new ideas will likely be needed. Possible directions include:
- Improved analysis of greedy or modified greedy algorithms.
- Sample-and-optimize approaches (use an initial fraction of items as a "sample" to learn the instance, then optimize over the remaining items).
- Primal-dual or LP-relaxation-based approaches adapted to the online random-order setting.
- Combining greedy with randomized rounding of a fractional solution.

### Key Reference

Download the paper at https://arxiv.org/pdf/1712.05450 and read it carefully before proceeding. This paper (Korula, Mirrokni, and Zadimoghaddam, "Online Submodular Welfare Maximization: Greedy Beats 1/2 in Random Order", 2017\) establishes the current state of the art and provides the analytical framework you should build upon.
