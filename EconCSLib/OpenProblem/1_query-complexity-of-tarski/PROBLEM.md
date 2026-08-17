---
name: Query Complexity of Tarski
contributor: Aviad Rubinstein
rating: Hard
---

## Query Complexity of Tarski Fixed Points

### Problem Description

**Tarski's fixed point theorem** states that every monotone function $f: L  
\rightarrow L$ on a complete lattice $L$ has a fixed point; moreover, the set of  
fixed points itself forms a complete lattice (and in particular has a least and a  
greatest element). The theorem is among the most widely used existence results in  
economics (e.g., for equilibria of supermodular games), verification (e.g., for  
model checking), and mathematics.

Despite its ubiquity, the **computational complexity** of finding such fixed  
points has only recently received systematic study. The computational problem is  
formalized as follows:

**The Tarski Problem**: Given black-box (query) access to a monotone function  
$f: [N]^d \rightarrow [N]^d$ on the $d$-dimensional grid with side length $N$  
(where $x \leq y$ iff $x_i \leq y_i$ for all $i$), find a fixed point $x^*$  
such that $f(x^*) = x^*$.

Tarski's theorem guarantees that such a fixed point exists. The fundamental  
question is: **How many queries to $f$ are necessary and sufficient to find a  
fixed point, as a function of $N$ and $d$?**

### Known Results

**Upper bounds:**

- The naive algorithm based on iterating $f$ starting from the bottom of the
   lattice requires $O(N^d)$ queries.
- A recursive binary-search algorithm (Dang, Qi, and Ye, 2011) finds a fixed
   point in $O(\log^d N)$ queries.
- Chen and Li (2022) improved this to $O(\log^{\lceil (d+1)/2 \rceil} N)$.
- Chen, Li, and Yannakakis (2026) further improved this to $O(\log^{\lceil
   (d-1)/3 \rceil + 1} N)$ for constant $d$, using a new framework based on
   safe partial-information functions.

**Lower bounds:**

- Etessami, Papadimitriou, Rubinstein, and Yannakakis (2020) proved that any
   (even randomized) algorithm requires $\Omega(\log^2 N)$ queries for $d = 2$.
   This lower bound immediately extends to all $d \geq 2$.
- Brânzei, Phillips, and Recker (2025) proved an $\tilde{\Omega}(d \cdot
   \log^2 N)$ lower bound for general $d$ using a "herringbone" construction.

**Tight results for small dimensions:**

- The query complexity is $\Theta(\log^2 N)$ for $d = 2$ (Etessami et al.,
   2020), $d = 3$ (following immediately from the $d=2$ lower bound of Etessami
   et al. combined with the upper bound of Chen, Li, and Yannakakis, 2026), and
   $d = 4$ (Chen, Li, and Yannakakis, 2026).

**Greatest/least fixed point:**

- Finding the greatest or least fixed point requires $\Theta(d \cdot N)$
   queries in the black-box model and is NP-hard in the white-box (circuit)
   model (Etessami et al., 2020).

**Complexity-class placement (white-box model):**

- In the white-box model (where $f$ is given as a Boolean circuit), the
   general Tarski problem is in PLS $\cap$ PPAD (Etessami et al., 2020).
- The Unique Tarski problem (where $f$ is promised to have a unique fixed
   point) has the same query complexity as the general problem (black-box
   reduction).

**Connections to games:**

- Computing equilibria of **supermodular games** is computationally equivalent
   to the Tarski problem (Etessami et al., 2020). For two-player supermodular
   games where one player's strategy space is one-dimensional, an equilibrium
   can be found in $O(\log N)$ queries.
- Computing (approximating) the value of **Condon's stochastic games** and
   **Shapley's stochastic games** reduces to the Tarski problem.

### Research Goal

The central open problem is to determine the query complexity of the Tarski  
problem as a function of dimension $d$. It is known that the complexity is  
$\Theta(\log^2 N)$ for $d \leq 4$ and, more generally, $O(\log^{\lceil (d-1)/3  
\rceil + 1} N)$ — i.e., $\Theta(\log^d N)$ is **not** tight. The key question  
is:

**Is the query complexity $\log^{\Theta(d)}(N)$?**

More specifically:

**(1) Prove stronger lower bounds** beyond the current $\tilde{\Omega}(d \cdot  
\log^2 N)$, ideally showing $\Omega(\log^{c \cdot d} N)$ for some constant $c >  
0$, or

**(2) Design algorithms with query complexity $\text{poly}(\log N)$** for every  
fixed $d$, breaking the $\log^{\Theta(d)} N$ barrier.

The current state of affairs leaves a significant gap: the lower bound is  
$\tilde{\Omega}(d \cdot \log^2 N)$ while the upper bound is $O(\log^{\lceil  
(d-1)/3 \rceil + 1} N)$, which for large $d$ is roughly $O(\log^{d/3} N)$.

### Challenges

1\.  **The curse of dimensionality in lower bounds**: The known $\Omega(\log^2  
   N)$ lower bound constructions (based on "herringbone" hard instances) do not  
   straightforwardly extend beyond $\Theta(\log^2 N)$. The adversarial  
   functions used exploit coupling between two coordinates, and scaling these  
   constructions to involve genuine $d$-dimensional interaction is the core  
   barrier.

2\.  **Algorithmic barriers**: The recursive binary-search approach naturally  
   yields $O(\log^d N)$ by peeling off one dimension at a time. Beating this  
   requires exploiting cross-dimensional structure in the monotone function —  
   recent algorithms do so via "safe partial-information" techniques, but the  
   improvements saturate at roughly $\log^{d/3} N$.

3\.  **Unique vs. general Tarski**: While the query complexities of the general  
   and unique-fixed-point versions are equivalent (by black-box reduction), the  
   unique version admits cleaner structural arguments. Understanding whether  
   the uniqueness promise can be leveraged algorithmically in the white-box  
   model is an open direction.

4\.  **White-box complexity**: The problem lies in PLS $\cap$ PPAD, but its exact  
   complexity-theoretic status (e.g., whether it is complete for CLS or some  
   other subclass of TFNP) remains unresolved. Resolving this would connect the  
   query-complexity question to circuit-complexity barriers.

### Key References

*   Brânzei, Simina, Reed Phillips, and Nicholas Recker. "Query complexity of
   the Tarski fixed point problem in high dimensions." arXiv preprint (2025).
*   Chen, Xi, and Yuhao Li. "Improved upper bounds for finding Tarski fixed
   points." Proceedings of the ACM Conference on Economics and Computation
   (EC). 2022.
*   Chen, Xi, Yuhao Li, and Mihalis Yannakakis. "The mystery deepens: On the
   query complexity of Tarski fixed points." arXiv preprint arXiv:2604.00268
   (2026).
*   Dang, Chuangyin, Qi Qi, and Yinyu Ye. "Computations and complexities of
   Tarski's fixed points and supermodular games." arXiv preprint (2011).
*   Etessami, Kousha, Christos Papadimitriou, Aviad Rubinstein, and Mihalis
   Yannakakis. "Tarski's theorem, supermodular games, and the complexity of
   equilibria." Proceedings of the Innovations in Theoretical Computer
   Science Conference (ITCS). 2020.
*   Fearnley, John, Paul W. Goldberg, Alexandros Hollender, and Rahul Savani.
   "The complexity of gradient descent: CLS = PPAD $\cap$ PLS." Journal of the
   ACM (2023).
