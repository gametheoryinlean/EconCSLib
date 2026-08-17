---
name: Static Posted Pricing for Multi-Unit Combinatorial Auctions
contributor: Brendan Lucier
---

## Static Posted Pricing for Bayesian Combinatorial Auctions with XOS Valuations

### Problem Description

Consider a **Bayesian combinatorial auction** with a set of items and $n$ buyers arriving sequentially. Each buyer $i$ has a **fractionally subadditive (XOS)** valuation $v_i$ over bundles of items, drawn from a known (but not necessarily i.i.d.) distribution. There are at least $k$ copies of each item. The seller's objective is to maximize **social welfare** using a **static posted pricing** mechanism: a single price is set for each item before buyers arrive, and each buyer, upon arrival, purchases a welfare-maximizing bundle at the posted prices while supply lasts.

When $k=1$, this is the classical **prophet inequality** setting, where a static item pricing achieves a competitive ratio of $1/2$ against the hindsight optimal welfare for XOS valuations. As $k \to \infty$ in the single-item setting, the competitive ratio of a static pricing approaches $1$.

The central open question is: **does the best achievable competitive ratio of a static item pricing tend to $1$ as $k \to \infty$ in the combinatorial (XOS) setting?**

### Known Results

**Positive Results:**

- For a single item ($k=1$) with multiple buyers, a static posted price achieves a $1/2$-competitive ratio against the prophet (optimal hindsight welfare). This is tight for static pricing (Krengel and Sucheston, 1977; Samuel-Cahn, 1984).
- Chawla, Devanur, and Lykouris (2020) gave a static pricing for the multi-unit single-item setting ($k > 1$) that achieves a competitive ratio increasing gradually with $k$, and subsequent work by Jiang, Ma, and Zhang showed this is the optimal static pricing for every value of $k$.
- For XOS combinatorial valuations with $k$ copies, Feldman, Gravin, and Lucier (2015) showed that a static item pricing achieves a $1/2$-competitive ratio (matching the single-copy bound).
- Chawla, Dang, Huang, and Wang (2025) showed that **dynamic** item pricings (where prices change over time) can asymptotically match the single-item static pricing competitive ratio. They also developed a non-adaptive pricing where item prices are set up front but increase as supply decreases, achieving a competitive ratio that increases strictly as a function of $k$.

**Negative Results:**

- Chawla, Dang, Huang, and Wang (2025) proved that the multi-unit combinatorial setting is **strictly harder** than the single-item counterpart: there is a gap between the competitive ratios achievable by static item pricings in the two settings. In particular, static pricings in the combinatorial XOS setting cannot match the single-item multi-unit competitive ratio for every $k$.

**Gap:**

- It remains open whether any static item pricing scheme can achieve a competitive ratio that tends to $1$ as $k \to \infty$ in the combinatorial XOS setting, despite the known possibility in the single-item multi-unit setting.

### Research Goal

Does the best achievable competitive ratio of a **static posted item pricing** for Bayesian combinatorial auctions with XOS buyer valuations (drawn from known, not necessarily i.i.d., distributions, with sequential arrival) tend to $1$ as the number of copies $k$ tends to infinity?

### Key References

* Chawla, Shuchi, Trung Dang, Zhiyi Huang, and Yifan Wang. "Multi-Unit Combinatorial Prophet Inequalities." arXiv Preprint (2025). Available at https://arxiv.org/abs/2505.16054.
* Chawla, Shuchi, Nikhil Devanur, and Thodoris Lykouris. "Static Pricing for Multi-Unit Prophet Inequalities." arXiv Preprint (2020). Available at https://arxiv.org/abs/2007.07990.
* Feldman, Michal, Nick Gravin, and Brendan Lucier. "Combinatorial Auctions via Posted Prices." SODA 2015.
* Dütting, Paul, Michal Feldman, Thomas Kesselheim, and Brendan Lucier. "Prophet Inequalities Made Easy: Stochastic Optimization by Pricing Nonstochastic Inputs." SIAM Journal on Computing 49.3 (2020): 540-582.
