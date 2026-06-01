---
id: social_choice.fair_division.indivisible.efx_exists_two_agents
title: EFX Existence — Two Agents, Any Finite Good Set
kind: theorem
status: staged
primary_topic: social_choice
topics:
  - social_choice
  - social_choice.fair_division
  - social_choice.fair_division.indivisible
uses:
  - social_choice.fair_division.indivisible.efx_singleton_bundle
  - social_choice.fair_division.indivisible.additive_valuation
lean:
  modules:
    - EconCSLib.SocialChoice.FairDivision.Indivisible.EFX
  declarations:
    - SocialChoice.FairDivision.Indivisible.efx_exists_two_agents
verification:
  statement: accepted
  proof: accepted
  alignment: aligned
tags:
  - fair-division
  - indivisible
  - efx
  - existence
---

# EFX Existence — Two Agents, Any Finite Good Set

**Theorem.** For any two agents and any finite good set $G$, with an
*additive* valuation $w : \mathrm{Fin}\ 2 \to G \to \mathbb{R}$
([[social_choice.fair_division.indivisible.additive_valuation]]) whose
weights are nonnegative for each agent, there exists an EFX allocation
([[social_choice.fair_division.indivisible.efx]]).

In Lean: `SocialChoice.FairDivision.Indivisible.efx_exists_two_agents`.
Hypotheses: `[Fintype G]`, `[DecidableEq G]`, `AdditiveValuation (Fin 2) G`,
and per-agent nonnegativity (`∀ g, 0 ≤ w.weight i g` for $i \in \{0, 1\}$).

## Proof outline

A cut-and-choose-style construction:

1. **Enumerate allocations.** Range over $2^{|G|}$ candidate splits of
   `allGoods` into two bundles via the helper `mkAlloc`. The feasible
   set is nonempty (`feasible_nonempty`).

2. **Pick an optimal split.** Choose a split that maximises agent $0$'s
   value of their own bundle, subject to agent $1$ choosing the larger-
   for-them side (`optimal_exists`). Additivity + nonneg weights make
   this maximin choice well-defined on a finite set.

3. **EFX verification.** Closed by the two pair-specific lemmas:
   - *Agent 0 is EFX* (`agent0_efx`): removing any item from agent 1's
     bundle, the maximin choice ensures agent 0's value of the
     residual cannot exceed agent 0's own bundle value.
   - *Agent 1 is EFX* (`agent1_efx`): they took the better half by
     construction; removing any item from agent 0's bundle only
     decreases its value (by additivity + nonneg weights), so agent 1
     still prefers their own.

The Lean proof factors out `mkAlloc_isAllocation`, `feasible_nonempty`,
`optimal_exists` for the partition-enumeration argument, then
`agent0_efx` and `agent1_efx` close the two EFX directions
separately.

## Status of the wider EFX problem

| Agent count | EFX existence |
|---|---|
| $n = 2$ | ✅ (this theorem) |
| $n = 3$ | ✅ (Chaudhury–Garg–Mehlhorn 2020, **not formalised** here) |
| $n \ge 4$ | 🔓 **open** |

The 2-agent existence is the only case the library proves in full
generality; the 3-agent case is on the porting roadmap but not yet
formalised.

## References

- [AGT Chapter 11] Nisan, Roughgarden, Tardos, and Vazirani, *Algorithmic Game Theory*. EFX existence for two agents.
- Plaut, B. and Roughgarden, T. (2018). "Almost Envy-Freeness with General Valuations". *SODA*. arXiv:1707.04769.
- Chaudhury, B. R., Garg, J., and Mehlhorn, K. (2020). "EFX Allocations for Three Agents". *EC*. arXiv:2005.06878.
