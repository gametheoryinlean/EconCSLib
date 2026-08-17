---
name: Disproving Strong MSP
contributor: Anonymous Contribution
---

## Disproving the Strong Matroid Secretary Conjecture

### Problem Description

A **matroid** $\mathcal{M} = (E, \mathcal{I})$ consists of a finite ground set $E$ with $|E| = n$ and a collection $\mathcal{I} \subseteq 2^E$ of **independent sets** satisfying:
- **Hereditary**: $\emptyset \in \mathcal{I}$, and if $A \subseteq B \in \mathcal{I}$ then $A \in \mathcal{I}$.
- **Exchange**: If $A, B \in \mathcal{I}$ with $|A| < |B|$, there exists $e \in B \setminus A$ with $A \cup \{e\} \in \mathcal{I}$.

The **rank** $r = r(\mathcal{M})$ is the size of any maximal independent set (called a **base**). The **uniform matroid** $U_{n,k}$ has ground set of size $n$ and independent sets $\mathcal{I} = \{S \subseteq E : |S| \leq k\}$.

In the **Matroid Secretary Problem (MSP)**, each element $e \in E$ has a non-negative weight $w(e) \geq 0$. The elements arrive in a **uniformly random order** — a permutation $\sigma$ drawn uniformly from $S_n$. Upon arrival of element $e$, the algorithm observes $w(e)$ and must immediately and irrevocably decide to **accept** or **reject** $e$. The constraint is that the set of accepted elements must remain independent in $\mathcal{M}$ at all times. The objective is to maximize the total weight of accepted elements.

The **competitive ratio** of an algorithm $\mathcal{A}$ on matroid $\mathcal{M}$ is:

$$
\alpha(\mathcal{A}, \mathcal{M}) = \inf_{w : E \to \mathbb{R}_{\geq 0}} \frac{\mathbb{E}_\sigma[\mathcal{A}(\mathcal{M}, w, \sigma)]}{\mathrm{OPT}(\mathcal{M}, w)}
$$

where $\mathrm{OPT}(\mathcal{M}, w) = \max_{B \in \mathcal{B}} \sum_{e \in B} w(e)$ is the maximum weight of any base, and the expectation is over the random arrival order $\sigma$. The **optimal competitive ratio** for matroid $\mathcal{M}$ is:

$$
\alpha^*(\mathcal{M}) = \sup_{\mathcal{A}} \alpha(\mathcal{A}, \mathcal{M}).
$$

### The Conjectures

**Matroid Secretary Conjecture (MSC)** (Babaioff, Immorlica, and Kleinberg, 2007): There exists a universal constant $c > 0$ such that for every matroid $\mathcal{M}$, $\alpha^*(\mathcal{M}) \geq c$.

**Strong Matroid Secretary Conjecture (SMSC)**: For every matroid $\mathcal{M}$, $\alpha^*(\mathcal{M}) \geq 1/e$.

The SMSC generalizes the classical secretary problem: for $U\_{n,1}$ (the rank-1 uniform matroid — pick at most one element), the optimal competitive ratio is exactly $1/e$ as $n \to \infty$, achieved by the classic "wait-then-pick" algorithm that rejects the first $\lfloor n/e \rfloor$ elements and then accepts the first element exceeding all previously seen values. Since any matroid contains $U\_{n,1}$ as a restriction (by considering a single element), $1/e$ is the best possible target for a universal guarantee.

### Known Results

**General algorithms (upper bounds on achievable ratio):**

| Algorithm | Competitive Ratio | Reference |
|:----------|:-----------------|:----------|
| Greedy sampling | $O(1/\log r)$ | Babaioff, Immorlica, Kleinberg (2007) |
| Improved greedy | $O(1/\sqrt{\log r})$ | Chakraborty and Lachish (2012) |
| Hierarchical sampling | $O(1/\log \log r)$ | Lachish (2014) |
| Simpler hierarchical | $O(1/\log \log r)$ (better constant) | Feldman, Svensson, Zenklusen (2015) |

The best known competitive ratio for general matroids is $\Omega(1/\log \log r)$. The MSC (even the weak $O(1)$ version) remains open.

**Specific matroid classes with $O(1)$-competitive algorithms:**

| Matroid Class | Best Known Ratio | Reference |
|:-------------|:----------------|:----------|
| Uniform $U_{n,k}$ | $1/e$ (as $n \to \infty$, fixed $k/n$) | Kleinberg (2005) |
| Partition matroids | $O(1)$ | Babaioff, Immorlica, Kleinberg (2007) |
| Graphic matroids | $\approx 3.95$ | Korula and Pál (2009); improved in subsequent work |
| Transversal matroids | $O(1)$ | Dimitrov and Plaxton (2012); Kesselheim et al. (2013) |
| Laminar matroids | $O(1)$ | Im and Wang (2011); Jaillet, Soto, Zenklusen (2013) |
| Regular matroids | $O(1)$ | Dinitz and Kortsarz (2014) |
| Gammoids | $O(1)$ | Soto (2011) |

**Lower bounds (impossibility results):**
- The classical secretary problem gives $\alpha^*(U\_{n,1}) = 1/e$, which is **tight**: no algorithm achieves competitive ratio $> 1/e$ for $U\_{n,1}$, and the optimal algorithm matches this.
- There are **no known impossibility results** ruling out a $1/e$-competitive algorithm when the matroid is known. The SMSC is neither proved nor disproved.

### Research Goal

**Primary Goal:** Disprove the Strong Matroid Secretary Conjecture by exhibiting a  matroid $\mathcal{M}$ for which no online algorithm can achieve competitive ratio $1/e$. Formally, show that there exists a matroid $\mathcal{M}$ and a constant $\varepsilon > 0$ such that:

$$
\alpha^*(\mathcal{M}) \leq \frac{1}{e} - \varepsilon.
$$

That is, for every algorithm $\mathcal{A}$, there exists a weight function $w$ such that:

$$
\frac{\mathbb{E}_\sigma[\mathcal{A}(\mathcal{M}, w, \sigma)]}{\mathrm{OPT}(\mathcal{M}, w)} \leq \frac{1}{e} - \varepsilon.
$$

**A Potentially Easier Goal (Ordinal MSP):** Disprove the SMSC in the ordinal (comparison-based) model, where the algorithm only observes relative orderings between element weights, not their actual values. This is described in detail below.

---

### The Ordinal Matroid Secretary Problem

In the **ordinal MSP**, the algorithm does not see numerical weights. Instead, upon arrival of element $e_t$ at time $t$, the algorithm learns only the **relative ranking** of $e_t$ among all elements seen so far: i.e., it knows the total order on $\{e\_{\sigma(1)}, \ldots, e\_{\sigma(t)}\}$ induced by $w$, but not the values $w(e\_{\sigma(i)})$ themselves.

An **ordinal algorithm** is one whose accept/reject decisions depend only on:
- The matroid $\mathcal{M}$,
- The set of previously seen elements and their relative order,
- The rank of the current element among those seen so far,
- Internal randomness.

The **ordinal competitive ratio** is:

$$
\alpha^*_{\mathrm{ord}}(\mathcal{M}) = \sup_{\mathcal{A} \text{ ordinal}} \;\inf_{w : E \to \mathbb{R}_{\geq 0}} \;\frac{\mathbb{E}_\sigma[\mathcal{A}(\mathcal{M}, w, \sigma)]}{\mathrm{OPT}(\mathcal{M}, w)}.
$$

Since ordinal algorithms are a subset of all algorithms, $\alpha^*_{\mathrm{ord}}(\mathcal{M}) \leq \alpha^*(\mathcal{M})$ for all $\mathcal{M}$.

**Key observation for rank 1:** For $U\_{n,1}$, the classical optimal algorithm ("skip $\lfloor n/e \rfloor$, then pick the next record") is inherently ordinal — it uses only comparisons, never actual values. Therefore $\alpha^*\_{\mathrm{ord}}(U\_{n,1}) = \alpha^*(U\_{n,1}) = 1/e$, and there is no separation between ordinal and cardinal algorithms for rank 1\.

**Why ordinal is easier to attack for higher rank:** For matroids of rank $r \geq 2$, cardinal algorithms can use the actual numerical weights to set thresholds, estimate the optimal value, or calibrate acceptance probabilities — strategies unavailable to ordinal algorithms. An ordinal algorithm that must select multiple elements faces an inherent information bottleneck: knowing only that element $e$ is the "3rd best seen so far" provides no information about how $w(e)$ compares to the maximum weight, which affects how much accepting $e$ costs in the competitive ratio.

**Goal for the ordinal version:** Find a matroid $\mathcal{M}$ of rank $r \geq 2$ such that:

$$
\alpha^*_{\mathrm{ord}}(\mathcal{M}) < \frac{1}{e}.
$$

This means showing that for every ordinal algorithm $\mathcal{A}$, there exists a weight vector $w$ (consistent with the orderings the algorithm might observe) such that $\mathbb{E}[\mathcal{A}]/\mathrm{OPT} < 1/e - \varepsilon$.

> [!NOTE]
> An ordinal impossibility result would not directly disprove the SMSC (which allows cardinal algorithms), but it would:
> 1. Establish a **separation** between ordinal and cardinal algorithms for the MSP, which is unknown today.
> 2. Show that the $1/e$ barrier of the classical secretary problem is **not robust** to matroid constraints under ordinal information.
> 3. Provide key structural insights about which matroids are hard and why, potentially guiding attacks on the full (cardinal) SMSC.

### Key References

1\. Babaioff, Immorlica, and Kleinberg, "Matroids, Secretary Problems, and Online Mechanisms" (SODA 2007, JACM 2018). Available at https://arxiv.org/abs/0709.4432 — introduced the MSP and both the MSC and SMSC.

2\. Feldman, Svensson, and Zenklusen, "A Simple $O(\log\log(\mathrm{rank}))$-Competitive Algorithm for the Matroid Secretary Problem" (SODA 2015, Math. Oper. Res. 2018). Available at https://arxiv.org/abs/1404.4473 — current best general algorithm.

3\. Lachish, "O(log log Rank) Competitive Ratio for the Matroid Secretary Problem" (FOCS 2014). Available at https://arxiv.org/abs/1411.4700 — first $O(\log\log r)$ algorithm.

4\. Kleinberg, "A Multiple-Choice Secretary Algorithm with Applications to Online Auctions" (SODA 2005). — The $k$-secretary problem for uniform matroids.

5\. Korula and Pál, "Algorithms for Secretary Problems on Graphs and Hypergraphs" (ICALP 2009). — $O(1)$-competitive algorithms for graphic matroids.

6\. Dinitz and Kortsarz, "Matroid Secretary for Regular and Decomposable Matroids" (ICALP 2014, SICOMP 2014). — Extended to regular matroids via Seymour's decomposition.

7\. Soto, "Matroid Secretary Problem in the Random-Assignment Model" (SODA 2011, SICOMP 2013). Available at https://arxiv.org/abs/1107.2462 — results for gammoids and the random-assignment variant.

8\. Feldman, Svensson, and Zenklusen, "Online Contention Resolution Schemes" (SODA 2016, SICOMP 2021). Available at https://arxiv.org/abs/1508.00142 — OCRSs and their connection to the MSP.

9\. Dynkin, "The Optimum Choice of the Instant for Stopping a Markov Process" (Soviet Math. Doklady, 1963). — The classical $1/e$ result for the secretary problem.
