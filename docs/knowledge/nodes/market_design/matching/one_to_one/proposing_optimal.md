---
id: market_design.matching.one_to_one.proposing_optimal
title: Proposing-Side Optimal Stable Matching
kind: theorem
status: proved
primary_topic: market_design
topics:
  - market_design
  - market_design.matching
  - market_design.matching.one_to_one
uses:
  - market_design.matching.one_to_one.gale_shapley_stable
lean:
  modules:
    - EconCSLib.MarketDesign.Matching.Optimal
  declarations:
    - GS.galeShapley_isProposingOptimal
source:
  spans:
    - artifact: msz-game-theory
      locator: "Chapter 22, Theorem 22.11"
      format: section
      note: "Men-proposing GS is weakly best stable matching for men, weakly worst for women"
verification:
  statement: accepted
  proof: accepted
  alignment: aligned
tags:
  - matching
  - optimality
  - gale-shapley
---

# Proposing-Side Optimal Stable Matching

**Theorem.** Let $\mu^M$ denote the matching produced by the men-proposing
Gale-Shapley algorithm on $(M, W, \succ)$. Then:

1. **Men-optimal.** For every man $i \in M$ and every stable matching $\mu$:

   $$\mu^M(i) \succeq_i \mu(i)$$

   I.e., every man weakly prefers his match in $\mu^M$ to his match in any
   other stable matching.

2. **Women-pessimal.** For every woman $j \in W$ and every stable matching $\mu$:

   $$\mu(j) \succeq_j \mu^M(j)$$

   I.e., every woman weakly prefers her match in any other stable matching
   to her match in $\mu^M$.

A symmetric pair of statements holds for the women-proposing algorithm with
roles swapped.

## Conventions

- Write $\mu(a)$ for the partner of agent $a$ under matching $\mu$, in either
  direction; the matching bijection gives $\mu(i) = j \iff \mu(j) = i$.
- Preferences are **strict**: each agent's preference list is a full ranking
  with no ties (the standard marriage-market setting). Strictness is used in
  the women-pessimal part.
- The men-proposing algorithm has each man propose down his list in
  **decreasing order of preference**, advancing past any woman who rejects
  him or who later displaces him.
- The market is **balanced** ($|M| = |W|$) with full preference lists, so the
  men-proposing algorithm terminates with a **perfect matching** — every agent
  is matched. This is the termination half of the [[gale_shapley_stable]]
  existence result this node builds on, and is what lets the conclusion below
  speak of *the* partner $\mu^M(i)$ of each man.

## Proof

Call a man-woman pair $(i, j)$ **achievable** if some stable matching matches
$i$ to $j$.

### Men-optimal

We prove the invariant: **throughout the men-proposing algorithm, no man is
ever rejected by an achievable partner**, where "rejected" covers both a fresh
proposal turned away and a tentatively-held man later displaced.

*Base case.* Before any proposals are made no rejection has occurred, so the
invariant holds vacuously.

*Inductive step.* Assume the invariant holds up to the current round, and for
contradiction suppose man $i$ is rejected by an achievable partner $j$ in this
round. Pick a stable matching $\mu$ with $\mu(i) = j$. When $j$ rejects $i$ she
is holding some man $i'$ with $i' \succ_j i$.

We show $i'$ strictly prefers $j$ to his $\mu$-partner $\mu(i')$:

- $(i', \mu(i'))$ is achievable (witnessed by $\mu$), so by the inductive
  hypothesis $i'$ has **not** been rejected by $\mu(i')$ up to this round.
- $j \neq \mu(i')$: otherwise $\mu$ would match both $i$ and $i'$ to $j$, which
  is impossible for a one-to-one matching (note $i' \neq i$ since
  $i' \succ_j i$).
- Hence $i'$ has not yet **proposed** to $\mu(i')$. For if he had proposed and
  (by the IH) not been rejected, the invariant would force $i'$ to be holding
  $\mu(i')$ right now — but he is holding $j \neq \mu(i')$.
- Yet $i'$ *has* proposed to $j$ (he is holding her). Since men propose in
  decreasing order of preference, every woman $i'$ has not yet proposed to —
  in particular $\mu(i')$ — is strictly below $j$ in his ranking:
  $j \succ_{i'} \mu(i')$.

So $(i', j)$ is a blocking pair for $\mu$: $i' \succ_j i = \mu(j)$ on the woman
side, and $j \succ_{i'} \mu(i')$ on the man side. This contradicts the
stability of $\mu$. Therefore $j$ is not achievable for $i$, establishing the
invariant.

*Conclusion.* At termination man $i$ is held by some woman $\mu^M(i)$ (his last
and most recent successful proposal). Let $j$ be any achievable partner of
$i$. By the invariant $i$ was not rejected by $j$, so either $j = \mu^M(i)$, or
$i$ never proposed to $j$. In the latter case $j$ lies strictly below
$\mu^M(i)$ in $i$'s ranking (he proposed exactly to the prefix of his list up
to $\mu^M(i)$), so $\mu^M(i) \succ_i j$. Either way $\mu^M(i) \succeq_i j$.
Taking $j = \mu(i)$ for an arbitrary stable matching $\mu$ — achievable by
definition — yields the men-optimal statement.

### Women-pessimal

Fix a stable matching $\mu$ and a woman $j$; set $i = \mu^M(j)$ and
$i' = \mu(j)$. Suppose for contradiction that $j$ is strictly better off under
$\mu^M$, i.e. $i \succ_j i'$.

Applying the men-optimal statement to man $i$ (whose $\mu^M$-partner is $j$) gives
$j = \mu^M(i) \succeq_i \mu(i)$. Moreover $\mu(i) \neq j$ — otherwise
$\mu(j) = i = i'$ would make $i \succ_j i'$ read $i \succ_j i$, false — so by
strictness of preferences the comparison is strict: $j \succ_i \mu(i)$.

Then $(i, j)$ blocks $\mu$: $i \succ_j i' = \mu(j)$ on the woman side and
$j \succ_i \mu(i)$ on the man side, contradicting stability. Hence no woman is
strictly better off under $\mu^M$; that is, $\mu(j) \succeq_j \mu^M(j)$.

## Consequences

The set of stable matchings has a **distinguished extremal element** on each
side. Combined with the [[lattice]] structure, this gives an explicit
characterization of the boundary of the stable set.

## References

- [MSZ Ch.22, Thm 22.11] Maschler, Solan, Zamir, *Game Theory*.
- Gale & Shapley (1962), original optimality observation.
- Roth & Sotomayor (1990), *Two-Sided Matching*, Ch. 2.
