---
name: Meaning of a Game
contributor: Christos Papadimitriou
---

## Computing the Meaning of a Game

### Problem Description

The **Nash equilibrium** has been the dominant solution concept in game theory
since Nash's 1950 existence proof. However, serious computational deficiencies
have eroded confidence in it as "the meaning of the game": computing a Nash
equilibrium is PPAD-complete even for two-player games, the multiplicity of
equilibria resists principled selection, and — most critically — natural
learning dynamics fail to converge to Nash equilibria. This last objection dates
back to Shapley (1964), who exhibited a $3 \times 3$ game in which fictitious
play cycles, and has been significantly amplified since: it was recently proved
that no dynamic — locally tractable or not — can converge to precisely the Nash
equilibria under reasonable convergence requirements.

An alternative paradigm, proposed by Papadimitriou and Piliouras (2019) and
developed in a series of subsequent works by Biggar, Piliouras, and
Papadimitriou, redefines the meaning of a game in dynamical terms:

> **The meaning of a game** $G$ is a function $\mu_G$ that maps any prior
> distribution over the mixed strategy profiles of $G$ to the posterior (limit)
> distribution over the **attractors** of the **replicator dynamic** in $G$.

That is, the meaning of a game is the way in which repeated play transforms the
collective behavior of the players. The replicator dynamic — gradient descent
on the players' utilities, equivalently the continuous-time limit of the
multiplicative weights update algorithm — is a canonical choice, and the concept
is robust to many other natural learning dynamics.

This reformulation leads to two concrete computational problems:

> **(1) Attractor Computation**: Given a game $G$ in normal form, compute a
> description of the attractors of the replicator dynamics in $G$.

> **(2) Limit Prediction**: Given a game $G$ and a mixed strategy profile $x$,
> compute the attractor to which the replicator dynamic converges starting at
> $x$.

### Known Results

**The unlearnability of Nash equilibria:**

-   Shapley (1964) showed that fictitious play can cycle and fail to converge to
   Nash equilibria in simple $3 \times 3$ games.
-   Milionis, Papadimitriou, Piliouras, and Spendlove (PNAS, 2023\) proved an
   impossibility theorem: there exists a game in which no dynamic whatsoever
   — locally tractable or not — can converge globally and uniformly to the
   Nash equilibria.
-   Biggar, Papadimitriou, and Piliouras (2026) showed that while two families
   of Nash-convergent dynamics exist in non-degenerate games, both are
   intractable to compute locally unless complexity classes collapse ($\mathsf{P
   } = \mathsf{PPAD}$ or $\mathsf{NP} = \mathsf{RP}$, respectively).
-   They further proved that any uniformly Nash-convergent dynamic equipped with
   a locally tractable Lyapunov function cannot be locally tractable unless
   $\mathsf{PPAD} = \mathsf{CLS}$, and formulated the **Impossibility
   Conjecture**: if a locally tractable Nash-convergent dynamic exists for all
   games, then $\mathsf{P} = \mathsf{PPAD}$.

**Towards computing attractors:**

-   The **Fundamental Theorem of Dynamical Systems** (Conley, 1978\) guarantees
   that every dynamical system on a compact space converges to its chain
   recurrent components, guided by a Lyapunov function. In games, these
   components — the attractors of the replicator dynamic — are the natural
   candidates for the "answer" that replaces Nash equilibria.
-   Biggar and Shames (ALT, 2023; ALT, 2024) characterized the attractor of the
   replicator dynamic in zero-sum games via the **response graph** and **chain
   components**, providing structural descriptions of the limit behavior.
-   Biggar and Papadimitriou (ALT, 2026) showed how to compute stable limit
   cycles of learning in games, and established **sink equilibria** as the
   attractors of learning in a general framework.
-   Hakim, Milionis, Papadimitriou, and Piliouras (SAGT, 2024) gave a
   polynomial-time algorithm for an approximate version of the limit prediction
   problem: given a game and a starting profile, computing (approximately)
   which attractor the replicator dynamic converges to.

### Research Goal

Determine whether the meaning of a game can be computed efficiently:

**(1)** Prove or disprove that there is a polynomial-time algorithm which, given
any game $G$ in normal form, outputs a description of the attractors of the
replicator dynamics in $G$.

**(2)** Prove or disprove that there is a polynomial-time algorithm which, given
a game $G$ and a mixed strategy profile $x$, computes the limit attractor of
the replicator dynamic starting at $x$.

### Key References

*   Biggar, Oliver, and Christos Papadimitriou. "Computing stable limit cycles
   of learning in games." arXiv preprint arXiv:2602.11315 (2026).
*   Biggar, Oliver, and Christos Papadimitriou. "Sink equilibria and the
   attractors of learning in games." Proceedings of The 37th International
   Conference on Algorithmic Learning Theory (ALT). 2026.
*   Biggar, Oliver, Christos Papadimitriou, and Georgios Piliouras. "On the
   complexity of learning Nash equilibria." arXiv preprint arXiv:2602.16016
   (2026).
*   Biggar, Oliver, and Iman Shames. "The replicator dynamic, chain components
   and the response graph." Proceedings of The 34th International Conference
   on Algorithmic Learning Theory (ALT). 2023.
*   Biggar, Oliver, and Iman Shames. "The attractor of the replicator dynamic
   in zero-sum games." Proceedings of The 35th International Conference on
   Algorithmic Learning Theory (ALT). 2024.
*   Conley, Charles C. Isolated Invariant Sets and the Morse Index. American
   Mathematical Society, 1978.
*   Daskalakis, Constantinos, Paul W. Goldberg, and Christos H. Papadimitriou.
   "The complexity of computing a Nash equilibrium." SIAM Journal on Computing
   39.1 (2009): 195–259.
*   Hakim, Rida, Jason Milionis, Christos Papadimitriou, and Georgios
   Piliouras. "Swim till you sink: computing the limit of a game." International
   Symposium on Algorithmic Game Theory (SAGT). 2024.
*   Milionis, Jason, Christos Papadimitriou, Georgios Piliouras, and Kelly
   Spendlove. "An impossibility theorem in game dynamics." Proceedings of the
   National Academy of Sciences 120.41 (2023).
*   Papadimitriou, Christos, and Georgios Piliouras. "Game dynamics as the
   meaning of a game." ACM SIGecom Exchanges 16.2 (2019): 53–63.
*   Shapley, Lloyd S. "Some topics in two-person games." Advances in Game
   Theory. Annals of Mathematics Studies 52. Princeton University Press, 1964.
