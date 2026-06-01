---
id: game_theory.strategic_game.dominant_implies_nash
primary_topic: game_theory.strategic_game
topics:
  - game_theory.strategic_game
  - game_theory.strategic_game.equilibrium
title: Dominant Strategy Profile is a Nash Equilibrium
kind: theorem
status: admitted
uses:
  - game_theory.strategic_game.nash_equilibrium
  - game_theory.strategic_game.weakly_dominant_strategy
lean:
  modules:
    - EconCSLib.GameTheory.StrategicGame.NashEquilibrium
  declarations:
    - IsNashEquilibrium.of_dominant
verification:
  statement: accepted
  proof: accepted
  alignment: aligned
generality:
  reviewed: true
  prompt: "Is this the standard relationship between dominance and Nash?"
  verdict: "Yes. If every player has a weakly dominant strategy, the resulting profile is Nash."
tags:
  - strategic-game
  - equilibrium
  - dominance
---

# Dominant Strategy Profile is a Nash Equilibrium

If every player \(i\) plays a weakly dominant strategy \(s_i\), then the resulting
profile \(\sigma = (s_i)_{i \in I}\) is a Nash equilibrium.

*Proof.* A weakly dominant strategy weakly dominates every alternative. In particular,
for any player \(i\) and any deviation \(s'_i\), we have
\(u_i(\sigma[i \mapsto s'_i]) \le u_i(\sigma)\). This means each player is best
responding, so \(\sigma\) is a Nash equilibrium. \(\square\)

## References

- [MSZ, Chapter 2] Maschler, Solan, and Zamir, *Game Theory*. Relationship between dominant strategies and Nash equilibrium.
