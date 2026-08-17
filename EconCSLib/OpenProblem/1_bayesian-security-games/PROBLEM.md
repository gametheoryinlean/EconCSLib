---
name: Bayesian Security Games
contributor: Vincent Conitzer
---

## Computing Nash Equilibria in Bayesian Security Games

### Problem Description

A **Bayesian simple security game** consists of:
- A set of **targets** $T$.
- A number of **defensive resources** $r\leq |T|$ for the defender.
- A set of **attacker types** $\Theta$ with a probability distribution over them.
- For every target $t\in T$: defender utilities $u\_1^0(t)$ and $u\_1^1(t)$ with $u\_1^0(t)\leq u\_1^1(t)$ (the defender prefers that an attacked target is defended), and for every attacker type $\theta\in\Theta$: attacker utilities $u\_2^0(\theta,t)$ and $u\_2^1(\theta,t)$ with $u\_2^0(\theta,t)\geq u\_2^1(\theta,t)$ (the attacker prefers that the attacked target is undefended).

The game proceeds as follows. The **defender** chooses a subset of $r$ targets to assign her resources to. The **attacker**, after learning his type $\theta$, chooses a target $t$ to attack. If no defensive resource was assigned to $t$, the defender and attacker receive utilities $u\_1^0(t)$ and $u\_2^0(\theta,t)$, respectively. If a defensive resource was assigned to $t$, they receive $u\_1^1(t)$ and $u\_2^1(\theta,t)$, respectively.

A **(Bayes-)Nash equilibrium** is a pair of strategies — a mixed strategy for the defender over subsets of $r$ targets, and a mapping from attacker types to (mixed) target choices — such that neither player can improve their expected utility by unilateral deviation.

### Research Goal

Determine whether a (Bayes-)Nash equilibrium can be computed in **polynomial time** for Bayesian simple security games.

### Known Results

- **Stackelberg vs. Nash**: In the security games literature, the standard solution concept is a **Stackelberg mixed strategy**, where the defender commits to a mixed strategy first and the attacker best-responds. For general two-player normal-form games, computing Stackelberg equilibria can be done in polynomial time (Conitzer and Sandholm, 2006; von Stengel and Zamir, 2010), while computing Nash equilibria is PPAD-complete (Daskalakis, Goldberg, and Papadimitriou, 2009; Chen, Deng, and Teng, 2009).

- **Reversed complexity landscape**: In simple security games — where the normal form has exponential size but the game has compact structure — the situation appears reversed. Computing **Stackelberg** mixed strategies is **NP-hard** (Li, Korzhyk, Conitzer, and Parr), while Nash equilibrium computation appears easier.

- **Non-Bayesian multi-resource variant**: For a simpler, non-Bayesian variant where the attacker has multiple resources, a polynomial-time algorithm for Nash equilibrium exists (Korzhyk, Conitzer, and Parr, 2011).

- **Interchangeability**: The (Bayes-)Nash equilibria of these games satisfy the **interchangeability property**, so equilibrium selection is not an issue — all equilibria yield the same payoffs.

- **Algorithmic status**: A seemingly fast algorithm for Bayesian Nash equilibrium exists (Li, Korzhyk, Conitzer, and Parr), but its worst-case polynomial running time has not been established.

### Challenges

The key difficulty is the **exponential-size strategy space** of the defender: the number of pure strategies is $\binom{|T|}{r}$, which is exponential in $r$. Despite the compact game representation, standard equilibrium computation methods do not directly apply. The existing algorithm exploits the game's structure but its worst-case complexity remains unresolved. The Bayesian aspect (multiple attacker types) further complicates the analysis compared to the non-Bayesian case, where polynomial-time algorithms are known.

### Key References

* Chen, Xi, Xiaotie Deng, and Shang-Hua Teng. "Settling the complexity of computing two-player Nash equilibria." Journal of the ACM 56.3 (2009).
* Conitzer, Vincent, and Tuomas Sandholm. "Computing the optimal strategy to commit to." Proceedings of the ACM Conference on Electronic Commerce (EC). 2006.
* Daskalakis, Constantinos, Paul Goldberg, and Christos H. Papadimitriou. "The complexity of computing a Nash equilibrium." SIAM Journal on Computing 39.1 (2009): 195-259.
* Kiekintveld, Christopher, Manish Jain, Jason Tsai, James Pita, Fernando Ordóñez, and Milind Tambe. "Computing optimal randomized resource allocations for massive security games." Proceedings of the Eighth International Joint Conference on Autonomous Agents and Multi-Agent Systems (AAMAS). 2009.
* Korzhyk, Dmytro, Vincent Conitzer, and Ronald Parr. "Security games with multiple attacker resources." Proceedings of the Twenty-Second International Joint Conference on Artificial Intelligence (IJCAI). 2011.
* von Stengel, Bernhard, and Shmuel Zamir. "Leadership games with convex strategy sets." Games and Economic Behavior 69 (2010): 446-457.
