---
name: Revenue Optimal DSIC Auction
contributor: Yanchen Jiang, David Parkes and Tonghan Wang
---

## Provably Revenue Optimal DSIC Sealed-Bid Auctions

### Problem Description

We consider **sealed-bid auctions** with a set of $n$ bidders,
$N=\{1,\ldots,n\}$, and $m$ items, $M=\{1,\ldots,m\}$, with $m>1$ and $n>1$.
Bidder $i$ has a valuation function $v_i:2^M\rightarrow \mathbb{R}\_{\ge 0}$.
Valuations are continuous. We consider both **additive valuations**, where
$v_i(S)=\sum\_{j\in S}v_i(j)$, and **unit-demand valuations**, where
$v_i(S)=\max\_{j\in S}v_i(j)$.

Valuation $v_i$ is drawn independently from a known distribution $F_i$ over
$V_i$, with $v_i(j)\in[0,v_{\max}]$ for all $i,j$. Let $\mathbf{F}=(F_1,\ldots,F_n)$,
$V=\prod_i V_i$, and write $\mathbf{v}_i=(v_i(1),\ldots,v_i(m))$.

An auction is a pair $(g,p)$, where $g:V\rightarrow \mathcal X$ is a feasible
allocation rule and $p_i:V\rightarrow \mathbb{R}_{\ge 0}$ is bidder $i$'s
payment rule. Let $g_i(\mathbf{b})\subseteq M$ denote the bundle allocated to bidder
$i$ at bid profile $\mathbf{b}=(b_1,\ldots,b_n)$. Bidder $i$'s utility is
$u_i(v_i;\mathbf{b})=v_i(g_i(\mathbf{b}))-p_i(\mathbf{b})$. In full generality, the allocation
rule may be randomized.

The auction is **dominant-strategy incentive compatible (DSIC)**, or
**strategy-proof (SP)**, if $u_i(v_i;(v_i,\mathbf{b}\_{-i}))\geq u_i(v_i;(b_i,\mathbf{b}\_{-i}))$ for all $i\in N$, $v_i,b_i\in V_i$, and $\mathbf{b}\_{-i}\in V\_{-i}$. It is
**individually rational (IR)** if $u_i(v_i;(v_i,\mathbf{b}\_{-i}))\geq 0$ for all $i\in
N$, $v_i\in V_i$, and $\mathbf{b}\_{-i}\in V\_{-i}$.

The optimal auction design problem is to identify a DSIC and IR auction
maximizing expected revenue:

$$
\mathcal{R}(\mathbf{F})=\sup_{(g,p)\in \mathrm{DSIC}\cap \mathrm{IR}}\mathbb{E}_{\mathbf{v}\sim \mathbf{F}}\left[\sum_{i=1}^n p_i(\mathbf{v})\right].
$$

### Research Goal

(1) **Computational Goal**: For some continuous distribution $\mathbf{F}$, some $n>1$
   and $m>1$, learn an auction $(g^\star,p^\star)$ expressed by neural networks
   or other representations such that $\mathbb{E}_{\mathbf{v}\sim \mathbf{F}}\left[\sum_i
   p_i^\star(\mathbf{v})\right]=\mathcal{R}(\mathbf{F})$, together with a rigorous proof
   of DSIC, IR, and revenue optimality.
(2) **Characterization Goal**: For some continuous distribution $\mathbf{F}$, some
   $n>1$ and $m>1$, give an explicit characterization of a revenue-optimal DSIC
   and IR auction $(g^\star,p^\star)$.

### Challenges

Myerson’s seminal work (1981) characterizes optimal auctions for the sale of a
single item. Within the class of DSIC, multi-item auctions, the only analytical
results of which we are aware pertain either to variants of the single-bidder
setting, including Daskalakis et al., 2015; Giannakopoulos and Koutsoupias,
2014; Manelli and Vincent, 2006; Pavlov, 2010, or to the setting with two items
whose value distributions each have support of size two (Yao, 2017). Obtaining
provably revenue-optimal DSIC auctions in multi-bidder, multi-item settings,
with continuous value distributions, remains a long-standing open challenge.

### Relation to Known Results

Neural mechanism design methods, termed "differentiable economics," such as
RochetNet (Dütting et al., 2024), GemNet (Wang, Jiang, and Parkes, 2024),
Lottery AMA (Curry, Sandholm, and Dickerson, 2023), AMenuNet (Duan et al.,
2023), and MenuNet (Shen, Tang, and Zuo, 2019\) can search directly over exactly
strategy-proof auction classes and produce interpretable candidate mechanisms.
There is also progress on neural computation methods for computing dual
certificates on optimal revenue (Jiang, Parkes, and Wang, 2026). The open
challenge, for the $m>1, n>1$ case, is to turn such AI-discovered mechanisms
into provably optimal results, through either a computational or
characterization-based path.

### Key References

*   Cai, Yang, Constantinos Daskalakis, and S. Matthew Weinberg. "An algorithmic
   characterization of multi-dimensional mechanisms." Proceedings of the
   forty-fourth annual ACM symposium on Theory of computing. 2012\.
*   Curry, Michael, Tuomas Sandholm, and John Dickerson. "Differentiable
   economics for randomized affine maximizer auctions." Proceedings of the
   Thirty-Second International Joint Conference on Artificial Intelligence.
   2023\.
*   Daskalakis, Constantinos, Alan Deckelbaum, and Christos Tzamos. "Strong
   duality for a multiple-good monopolist." Proceedings of the Sixteenth ACM
   Conference on Economics and Computation. 2015\.
*   Duan, Zhijian, Haoran Sun, Yurong Chen, and Xiaotie Deng. "A scalable neural
   network for DSIC affine maximizer auction design." Advances in Neural
   Information Processing Systems 36 (2023): 56169-56185.
*   Dütting, Paul, Zhe Feng, Harikrishna Narasimhan, David C. Parkes, and Sai
   Srivatsa Ravindranath. "Optimal auctions through deep learning: Advances in
   differentiable economics." Journal of the ACM 71.1 (2024): 1-53.
*   Giannakopoulos, Yiannis, and Elias Koutsoupias. "Duality and optimality of
   auctions for uniform distributions." Proceedings of the fifteenth ACM
   conference on Economics and computation. 2014\.
*   Jiang, Yanchen, David C. Parkes, and Tonghan Wang. "Duality for Optimal
   Multi-Item, Multi-Bidder Auction Design: Revenue Certificates through Deep
   Learning." Proceedings of the 27th ACM Conference on Economics and
   Computation. 2026\.
*   Manelli, Alejandro M., and Daniel R. Vincent. "Bundling as an optimal
   selling mechanism for a multiple-good monopolist." Journal of Economic
   Theory 127.1 (2006): 1-35.
*   Myerson, Roger B. "Optimal auction design." Mathematics of operations
   research 6.1 (1981): 58-73.
*   Pavlov, Gregory. "Optimal mechanism for selling two goods." The B.E. Journal
   of Theoretical Economics 11.1 (2011).
*   Rochet, Jean-Charles. "A necessary and sufficient condition for
   rationalizability in a quasi-linear context." Journal of Mathematical
   Economics 16.2 (1987): 191-200.
*   Shen, Weiran, Pingzhong Tang, and Song Zuo. "Automated Mechanism Design via
   Neural Networks." Proceedings of the 18th International Conference on
   Autonomous Agents and MultiAgent Systems. 2019\.
*   Wang, Tonghan, Yanchen Jiang, and David C. Parkes. "GemNet: Menu-Based,
   Strategy-Proof Multi-Bidder Auctions Through Deep Learning." Proceedings of
   the 25th ACM Conference on Economics and Computation. 2024\.
*   Yao, Andrew Chi-Chih. "Dominant-strategy versus bayesian multi-item
   auctions: Maximum revenue determination and comparison." Proceedings of the
   2017 ACM Conference on Economics and Computation. 2017\.
