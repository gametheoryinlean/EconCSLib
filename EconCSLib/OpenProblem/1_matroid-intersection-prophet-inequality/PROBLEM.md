---
name: Matroid Intersection Prophet Inequalities
contributor: Matt Weinberg
---

## Prophet Inequalities for the Intersection of Matroids

### Problem Description

A **prophet inequality** considers the following setting. There are $n$ elements, each with a random non-negative value $v_i$ drawn independently from a known distribution $D_i$. A feasibility constraint specifies which subsets of elements may be selected. Elements arrive in some order, and upon arrival their value is revealed. An online algorithm must irrevocably decide whether to accept or reject each element upon arrival, subject to the feasibility constraint. The goal is to maximize the expected total value of accepted elements. The **competitive ratio** (or approximation factor) of the algorithm is the ratio of its expected value to the expected value of the **prophet** (the offline optimum that sees all values in advance and selects the best feasible set).

This problem concerns feasibility constraints that are the **intersection of $p$ matroids**. Intersection of matroids captures a wide range of combinatorial constraints; for example, the intersection of two partition matroids can encode bipartite matching. The central open question is:

**What is the asymptotically optimal competitive ratio achievable for prophet inequalities over the intersection of $p$ matroids?**

### Known Results

**Upper Bounds (Algorithms):**

- The best known algorithms achieve an $O(p)$-approximation (i.e., competitive ratio $\Theta(1/p)$). This holds for arbitrary matroids, arbitrary (non-i.i.d.) distributions, and against an omniscient adversary choosing the arrival order (Kleinberg and Weinberg, 2012; Feldman, Svensson, and Zenklusen, 2016 via Online Contention Resolution Schemes).

**Lower Bounds (Impossibility):**

- Kleinberg and Weinberg (2012) established an $\Omega(\sqrt{p})$ lower bound on the approximation factor (i.e., no algorithm can achieve competitive ratio better than $O(1/\sqrt{p})$). Their construction uses i.i.d. Bernoulli random variables and writes the feasibility constraint as the intersection of partition matroids.
- Saxena, Velusamy, and Weinberg (2023) improved the lower bound to $p^{1/2 + \Omega(1/\log \log p)}$ by writing the construction of Kleinberg and Weinberg (2012) as the intersection of asymptotically fewer partition matroids, leveraging techniques of Alon and Alweiss (2020) on the product dimension of graphs.

**The Gap:**

- The best algorithm achieves an $O(p)$-approximation. The best lower bound is $p^{1/2 + \Omega(1/\log \log p)}$. Closing this gap is a major open problem.

### A Concrete Combinatorics Problem

The lower bound question reduces to a clean combinatorics problem about the **product dimension** of graphs.

**Definition.** The **product dimension** of a graph $G$, denoted $\mathrm{pdim}(G)$, is the minimum number of proper vertex colorings of $G$ such that every pair of non-adjacent vertices receives the same color in at least one coloring.

Let $Q(\ell, r)$ denote the product dimension of the graph consisting of $r$ disjoint cliques of size $\ell$. The key question is:

**What is (asymptotically) $Q(q, q^q)$?**

- **Lower bound:** There is a trivial lower bound of $q$.
- **Upper bound:** Kleinberg and Weinberg (2012) give an upper bound of $q^2$. Saxena, Velusamy, and Weinberg (2023) improve this to $q^{2 - O(1/\log \log q)}$, building on the techniques of Alon and Alweiss (2020).

**Connection to prophet inequalities:** Kleinberg and Weinberg (2012) show that a grid construction with $q^q$ rows and $q$ columns, with i.i.d. $\mathrm{Bernoulli}(1/q)$ random variables, exhibits a lower bound of $\Theta(q)$ on the approximation factor. This construction can be written as the intersection of $Q(q, q^q)$ partition matroids. Therefore, the upper bound of $q^{2 - O(1/\log \log q)}$ on $Q(q, q^q)$ translates to a lower bound of $q^{1/2 + \Omega(1/\log \log q)}$ on the approximation factor for matroid intersection prophet inequalities. Resolving $Q(q, q^q)$ would directly improve the prophet inequality lower bound.

**Note on related work:** Alon and Alweiss (2020) study $Q(\ell, r)$ for general $\ell$ and $r$, and obtain an improved construction when $r \to \infty$ as a function of $\ell$. However, their construction does not directly improve $Q(p, p^p)$; the improvement in Saxena, Velusamy, and Weinberg (2023) essentially leverages the Alon–Alweiss techniques in the general case to obtain a slight improvement for $Q(p, p^p)$.

### A Lattice of Problems

A problem concerning matroid intersection prophet inequalities can be interesting along several dimensions, giving rise to a rich lattice of variants:

- **Class of matroids:** arbitrary matroids, partition matroids, etc.
- **Class of distributions:** arbitrary, i.i.d., i.i.d. Bernoulli, etc.
- **Arrival order:** omniscient adversary, prophet adversary, fixed-order adversary, random order, chosen order.
- **Instance restrictions:** arbitrary instances, symmetric instances (invariant under a wide class of permutations), the "KW12 grid" construction (a grid with $r$ rows and $\ell$ columns, where it is feasible to accept any number of elements from the same row but all accepted elements must be from the same row, and the question is how many matroids and which matroids are needed), or the "KW12 grid with product dimension proof" (requiring partition matroids and the product dimension proof approach).

**Remarkably**, the best algorithm for any setting in this lattice achieves $O(p)$ (even for arbitrary distributions, arbitrary matroids, and an omniscient adversary, via OCRS). The best lower bound for any setting in this lattice is $p^{1/2 + \Omega(1/\log \log p)}$ (even for the ostensibly much easier problem of a specific symmetric construction with i.i.d. Bernoulli random variables and chosen arrival order).

### Research Goal

(1) **Close the approximation gap:** Determine the asymptotically optimal approximation factor for prophet inequalities over the intersection of $p$ matroids. The current gap is between $p^{1/2 + \Omega(1/\log \log p)}$ and $O(p)$.

(2) **Resolve the product dimension question:** Determine the asymptotic value of $Q(q, q^q)$, the product dimension of the graph with $q^q$ disjoint cliques of size $q$. The current gap is between $q$ and $q^{2 - O(1/\log \log q)}$. This is a self-contained combinatorics problem whose resolution would directly improve the prophet inequality lower bound.

### Key References

* Kleinberg, Robert, and S. Matthew Weinberg. "Matroid Prophet Inequalities." STOC 2012.
* Feldman, Moran, Ola Svensson, and Rico Zenklusen. "Online Contention Resolution Schemes." SODA 2016.
* Saxena, Raghuvansh R., Santhoshini Velusamy, and S. Matthew Weinberg. "An Improved Lower Bound for Matroid Intersection Prophet Inequalities." ITCS 2023. Available at https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ITCS.2023.95.
* Alon, Noga, and Ryan Alweiss. "On the Product Dimension of Clique Factors." European Journal of Combinatorics 86 (2020).
* Lovász, László, Jaroslav Nešetřil, and Aleš Pultr. "On a Product Dimension of Graphs." Journal of Combinatorial Theory, Series B 29.1 (1980): 47-67.
