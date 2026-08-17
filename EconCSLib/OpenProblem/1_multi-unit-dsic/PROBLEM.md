---
name: Multi Unit DSIC
contributor: Noam Nisan
---

## Dominant-Strategy Incentive-Compatible Mechanisms for Multiunit Auctions

### Problem Description

#### Basic Setting

In a **multiunit auction** $m$ identical indivisible items are being auctioned among $n$ bidders.  We are thinking of $n$ as a small number and of $m$ as a very large number, where we would want the running time to be polynomial in $n$ and in the description size of $m$, i.e., in $log(m)$.  Each bidder $i$ has a **valuation function** $v_i : \{1…m\} \rightarrow \Re_+$ that is monotone, $v_i(j+1) \ge v_i(j)$ for every $1 \le j < m$.  The goal is to find an allocation $(m_1, m_2, …, m_n)$ with $\sum_i m_i \le m$, that maximizes **social welfare**, $\sum_i v_i(m_i)$.

#### Model of Computation

The “input size” here is $m$ real numbers for each of the $n$ players.  As we view $m$ as large we want algorithms whose running time is **sublinear** in the input size.  There are various possible models here, the most general of which is the communication complexity model where we count bits of communication between the bidders and the mechanism.  We will proceed in a related simpler model for which the problem is still interesting, the **value query** model where the algorithm/mechanism is allowed to query for the value of $v_i(j)$ of any player $i$ and number of items $j$, and our complexity measure is the total number of queries made.

#### Incentive Compatibility

We are looking for a **deterministic, dominant strategy incentive compatible (DSIC) mechanism**.  A deterministic mechanism $M$ receives as input the valuations $v_1…v_n$ and produces as output an allocation $m_1…m_n$ (with $\sum_i m_i \le m$) and payment amounts $p_1…p_n$ from the bidders to the auctioneer.  DSIC means that for every player $i$, every valuation $v_i$ of player $i$, every possible valuations of the other players $v\_{-i}$, and every possible "fake bid" $v'_i$ of player $i$, if we denote by $(m_i, p_i)$ the outcome of the mechanism for player $i$ on inputs $(v_i,v\_{-i})$ and denote by $(m'_i, p'_i)$ the outcome of the mechanism for player $i$ on inputs $(v'_i,v\_{-i})$ then we have $v_i(m_i)-p_i \ge v_i(m'_i)-p'_i$.

### What is known

#### Computational Status

In terms of pure computation, ignoring any incentive issues, a number of queries that is linear in $m$ (i.e. exponential in $\log m$) is required to produce the exact welfare-maximizing allocation.  An $\alpha=(1-\epsilon)$ approximation, for every $\epsilon>0$ can be done with polynomially (in $n$ and $\log m$) many value queries.

#### Possibility Results

* For the case of **downward sloping** valuations (where $v_i(j+2)-v_i(j+1) \le v_i(j+1)-v_i(j)$ for all $i$ and $j$) as originally studied by Vickrey can be solved exactly with polynomially (in $n$ and $\log m$) many queries and thus the VCG mechanism gives an optimal allocation for this subcase.

* For the general case, there exists a DSIC mechanism that uses polynomially (in $n$ and $\log m$) many value queries and produces an **$\alpha=1/2$ approximation** [Dobzinski and Nisan 2007].

* For the case of **single minded bidders**, there exists a DSIC mechanism that runs in polynomial (in $n$ and $\log m$) time and produces an $\alpha=(1-\epsilon)$ approximation for any $\epsilon>0$ [Briest, Krysta, and Vocking 2011].

* If we allow **randomized** DSIC mechanisms then there exist such mechanisms that use polynomially (in $n$ and $\log m$) many value queries and produces an $\alpha=(1-\epsilon)$ approximation for any $\epsilon>0$ [Dobzinski and Dughmi 2009] and even universally-truthful ones [Vocking, 2012].

* If we change our computation model and consider complexity where the input is presented in certain simple bidding languages, then an $\alpha=(1-\epsilon)$ approximation for any $\epsilon>0$ is possible in time polynomial in the input size [Dobzinski and Nisan 2007].

#### Impossibility Results

* For the case of exactly 2 bidders, DSIC mechanisms that **always allocate all items**, $m_1+m_2=m$, cannot produce an $\alpha$-approximation for any $\alpha>1/2$ with $\mathrm{poly}(n, \log m)$ queries [Lavi, Mu'alem and Nisan 2003].

* **Maximal in Range** mechanisms (those that fully optimize over a subset of the range of possible allocations) cannot produce an $\alpha$-approximation for any $\alpha>1/2$ with $\mathrm{poly}(n, \log m)$ queries [Dobzinski and Nisan 2007].

* **Scalable Mechanisms** (those that are invariant to "units":  multiplying all valuations by a constant does not change the allocation) cannot produce an $\alpha$-approximation for any $\alpha>1/2$ with $\mathrm{poly}(n, \log m)$ queries [Dobzinski and Nisan 2011].

### Research Goal

Does there exist a deterministic DSIC mechanism for multiunit auctions that makes at most $\mathrm{poly}(n, \log m)$ value queries on each input and has an approximation factor better than $1/2$? I.e., that for some $\alpha > 1/2$ and every $v_1,\ldots,v_n$ satisfies $\sum_i v_i(m_i) \ge \alpha \sum_i v_i(\mathrm{opt}_i)$, where $(m_1,\ldots,m_n)$ is the allocation produced by the mechanism for input $(v_1,\ldots,v_n)$ and $(\mathrm{opt}_1,\ldots,\mathrm{opt}_n)$ is the welfare-maximizing allocation for $(v_1,\ldots,v_n)$.

This is probably the simplest concrete open problem that directly studies the clash between computational complexity and incentive compatibility which comes into play in cases where exact optimization is not computationally tractable but decent approximations are so. This class of problems is arguably the most basic class of open problems in the field of Algorithmic Mechanism Design. The question was asked more or less in this form in [Dobzinski and Nisan, 2007] and the same type of question for combinatorial auctions was already mentioned in [Lehmann, O'callaghan and Shoham, 2002].

### Key References

The following survey contains a detailed description of many of the results stated above and all references.

* "Algorithmic Mechanism Design: Through the lens of Multiunit auctions" by N. Nisan. In Handbook of Game Theory with Economic Applications, Volume 4, Pages: 477-515, Editors: H. Peyton Young, Shmuel Zamir, Elsevier, 2015.

The latest impossibility result appears in the following paper.

* "Multi-unit auctions: beyond Roberts." by S. Dobzinski and N. Nisan. In Proceedings of EC 2011.
