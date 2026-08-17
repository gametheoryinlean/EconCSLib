---
name: Deterministic Subadditive CA
contributor: Shahar Dobzinski
---

## Deterministic Incentive-Compatible Mechanisms for Combinatorial Auctions when Bidders have Subadditive Valuations

### Problem Description

#### Basic Setting

In a **combinatorial auction** $m$ indivisible items are being auctioned among
$n$ bidders.  Each bidder $i$ has a **valuation function** $v_i : 2^M \rightarrow \mathbb{R}$. Each valuation function is monotone (for each item $j$ and bundle
$S$, $v_i(S+\{j\})\geq v_i(S)$) and normalized ($v_i(\emptyset)=0$). The goal is to find
an allocation $(S_1, S_2, \ldots, S_n)$ (if $i\neq j$ then $S_i\cap S_j=\emptyset$) that
maximizes **social welfare**, $\sum_i v_i(S_i)$.

#### Model of Computation

Our main interest is in the communication complexity model where we count the
number of bits the bidders need to transfer in order to determine the output. We
are interested in algorithms with communication complexity poly(m,n).

We consider only deterministic mechanisms.

#### Incentive Compatibility

We are looking for a **deterministic, dominant strategy incentive compatible
(DSIC) mechanism**.  A deterministic mechanism $M$ receives as input the
valuations $v_1…v_n$ and produces as output an allocation $(S_1…S_n)$ and
payments $p_1…p_n$ that the participants pay.  DSIC means that for every player
$i$, every valuation $v_i$ of player $i$, every possible valuations of the other
players $v\_{-i}$, and every other possible $v'_i$ of player $i$, if we denote by
$(S_i, p_i)$ the outcome of the mechanism for player $i$ on inputs
$(v_i,v\_{-i})$ and denote by $(S'_i, p'_i)$ the outcome of the mechanism for
player $i$ on inputs $(v'_i,v\_{-i})$ then we have $v_i(S_i)-p_i \ge
v_i(S'_i)-p'_i$.

### What is known

#### Computational Status

Ignoring incentive issues, Feige (2006) provides a 2-approximation algorithm for
this problem (that is, always finds a solution with social welfare at least half
of the optimal social welfare). For every constant $\epsilon > 0$, an approximation
ratio of $2 - \epsilon$ requires exponential communication (Dobzinski, Nisan,
Schapira, 2005)..

#### Possibility Results

*   Dobzinski, Nisan, and Schapira (2005) provide a deterministic DSIC mechanism
   that provides an approximation ratio of $O(\sqrt{m})$.
*   Qiu and Weinberg (2024) improve this ratio to $O(\sqrt{m/\log m})$.

#### Impossibility Results

*   Dobzinski (2016) suggests the notion of **taxation complexity** of DSIC
   mechanisms and shows two ways of proving impossibilities: one for two
   players using simultaneous communication, and the other by showing that the
   taxation complexity is a lower bound on the communication complexity and
   utilizing this.
*   Assadi, Khandeparkar, Saxena, and Weinberg (2020) are the first to show a
   separation between the communication complexity of truthful mechanisms and
   non-truthful mechanisms for combinatorial auctions. They achieve this by
   applying the taxation complexity framework via the simultaneous
   communication path. Therefore, their separation is restricted to only two
   players. Furthermore, it works only for a subclass of subadditive
   valuations.
*   Ron, Thomas, Weinberg, and Zhang (2024) prove a separation for three players
   mechanisms by giving a lower bound on the taxation complexity of
   three-player mechanisms. However, the class of valuations they use also
   includes non-subadditive valuations.

### Research Goal

Prove or disprove: there is a deterministic DSIC mechanism for combinatorial
auctions that uses $\mathrm{poly}(m,n)$ communication and achieves an approximation ratio of $2$.

### Key References

*   Shahar Dobzinski: Computational Efficiency Requires Simple Taxation. FOCS
   2016: 209-218
*   Shahar Dobzinski, Noam Nisan, Michael Schapira: Approximation algorithms for
   combinatorial auctions with complement-free bidders. STOC 2005: 610-618
*   Uriel Feige: On maximizing welfare when utility functions are subadditive.
   STOC 2006: 41-50
*   Sepehr Assadi, Hrishikesh Khandeparkar, Raghuvansh R. Saxena, S. Matthew
   Weinberg: Separating the communication complexity of truthful and
   non-truthful combinatorial auctions. STOC 2020: 1073-1085
*   Shiri Ron, Clayton Thomas, S. Matthew Weinberg, Qianfan Zhang: Communication
   Separations for Truthful Auctions: Breaking the Two-Player Barrier. FOCS
   2024: 386-405
