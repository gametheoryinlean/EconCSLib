---
id: game_theory.repeated_game.core.history
title: Repeated Game History
kind: definition
status: staged
primary_topic: game_theory.repeated_game
topics:
  - game_theory.repeated_game
  - game_theory.repeated_game.core
uses:
  - game_theory.repeated_game.core.repeated_game
verification:
  definition: accepted
  proof: not_applicable
tags:
  - repeated-game
  - history
---

# Repeated Game History

For a repeated game with stage action profile space $A = \prod_i A_i$
([[game_theory.repeated_game.core.repeated_game]]), a **length-$t$ history** is a
sequence of $t$ past action profiles:
$$
h_t = (a_0, a_1, \dots, a_{t-1}) \in A^t.
$$

The empty history $h_0 = \emptyset$ corresponds to stage 0 before any
play occurs.

## Strategy spaces over histories

- A **pure strategy** for player $i$ is a function
  $\sigma_i : \bigcup_t A^t \to A_i$ that picks an action for every
  possible history.
- A **behavioural strategy** is
  $\sigma_i : \bigcup_t A^t \to \Delta(A_i)$.

The set of all possible histories $\bigcup_t A^t$ is countably infinite
even for finite $A$, so the strategy space is enormous. Equilibrium
arguments typically restrict to:

- **Automaton strategies**: strategies implementable by a finite-state
  automaton reading $h_t$ — the standard tool for folk-theorem
  constructions (grim trigger, tit-for-tat, etc.).
- **Markovian / Markov-1 strategies**: depend only on the last action
  profile $a_{t-1}$ (or short-memory variants).

## Observability variants

The "public history" assumption above gives every player the entire
$h_t$. Other observability structures yield different games:

- *Private monitoring*: each player observes only their own action and
  a private signal correlated with the action profile.
- *Public-imperfect monitoring*: all players observe the same public
  signal, but not the underlying action profile.

These are central to dynamic mechanism design and reputation theory; the
folk theorem changes form in the imperfect-monitoring setting
(Fudenberg-Levine-Maskin 1994).

## References

- [MSZ Chapter 13] Maschler, Solan, and Zamir, *Game Theory*.
- Mailath, G. and Samuelson, L. (2006). *Repeated Games and Reputations.* Oxford.
- [MFoGT Chapter 8] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*.
