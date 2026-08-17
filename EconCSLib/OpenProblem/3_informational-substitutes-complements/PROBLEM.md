---
name: Operational Characterizations of Informational Substitutes and Complements
contributor: Yiling Chen
---

## Operational Characterizations of Informational Substitutes and Complements

### Problem Description

A Bayesian information structure consists of a decision-relevant random event $E$, $n$ random base signals $A\_1,\ldots, A\_n$, and a common prior distribution $P$ over $(E,A\_1,\ldots,A\_n)$. A decision maker observes the realization of some signal or combination of signals, updates their belief about $E$ by Bayes' rule, and then chooses an optimal action.

Without loss of generality, one can view general decision problems in terms of proper scoring rules. Equivalently, the decision maker has a convex expected score function

$$
G:\Delta(E)\to \mathbb{R},
$$

where $G(q)$ is the expected utility of acting optimally when the posterior belief on $E$ is $q$. For a signal $X$, let $p_x=P(E=\cdot\mid X=x)$ and define its value by

$$
V_G(X)=\mathbb{E}_{x}[G(p_x)].
$$

Here $X$ can be a single signal, a tuple of signals, or a partial disclosure of a signal. If the decision maker first observes $X$ and then also observes $Y$, write

$$
\Delta_G(Y\mid X) := V_G(X,Y)-V_G(X).
$$

This is the marginal value of adding $Y$ when $X$ is already known.

The substitute/complement distinction can be stated using this marginal-value notation. Suppose $C$ is background information already available, and $A$ and $B$ are two additional sources. The source $A$ makes $B$ less valuable if

$$
\Delta_G(B\mid C) \geq \Delta_G(B\mid C,A),
$$

or equivalently,

$$
V_G(C,B)-V_G(C) \geq V_G(C,A,B)-V_G(C,A).
$$

This is the basic substitutes inequality: learning $B$ has diminishing marginal value after $A$ has already been learned. Complements reverse the inequality: learning $B$ becomes more valuable after $A$ has already been learned.

There are three strengths of informational substitutes. In the weak version, $A$, $B$, and $C$ range over collections of whole base signals. In the moderate version, the same comparison must remain true after deterministic summaries of signals are revealed. In the strong version, it must remain true even after arbitrary randomized partial disclosures, or garblings, of signals. Thus, the definitions form a hierarchy: weak substitutes/complements concern whole signals, while strong substitutes/complements concern all possible partial ways of revealing those signals.

While mathematically clean, these definitions are not yet operational. The open problem is to find structural, useful, and efficiently checkable characterizations of when a distributional information structure and a decision problem, represented by $G$, induce substitutes or complements.

### Why This Matters

Informational substitutes and complements play a role analogous to substitutes and complements for goods, but in settings where the objects being combined are signals, experiments, reports, or data sources.

In prediction markets and related strategic information-revelation games, strong substitutes correspond to immediate information aggregation: informed agents have incentives to reveal information early. Strong complements correspond to delayed information aggregation: agents may prefer to wait until others have revealed their information. Thus, an operational test for substitutability or complementarity would help predict equilibrium behavior and guide the design of scoring-rule markets and other information elicitation mechanisms.

In algorithmic information acquisition, weak substitutes make the value of selected signals a submodular objective. This enables greedy and submodular-maximization methods for signal-selection problems subject to constraints such as cardinality or budget. Without such structure, and especially in complementary regimes, signal selection can be computationally hard.

### Known Results

Several benchmark classes are known, but they cover only extremes.

- For the log scoring rule, signals that are conditionally independent given the state $E$ are strong substitutes. This result is special to the log score: conditionally independent signals need not be substitutes for the quadratic scoring rule.

- Independent signals are strong complements for any decision problem $G$ whose Bregman divergence $D_G$ is jointly convex. This includes the log and quadratic scoring rules, but not arbitrary decision problems.

- There are strong negative results for universal substitutability. Apart from trivial cases, one should not expect an information structure to be substitutable for every decision problem. This suggests that a useful theory must characterize the pair consisting of the information structure and the decision problem, rather than the signal distribution alone.

### Research Goal

Develop tractable, operational characterizations of informational substitutes and complements for general decision problems represented by proper scoring rules.

More concretely, given finite $(E,A_1,\ldots,A_n,P)$ and a convex expected score function $G$, characterize when the induced value function

$$
V_G(S)=\mathbb{E}\left[G(P(E=\cdot\mid A_S))\right]
$$

is weakly, moderately, or strongly submodular or supermodular on the relevant signal lattice.

A satisfactory solution could take any of the following forms.

1. **Structural characterization.** Give necessary and sufficient conditions, or sharp sufficient conditions with meaningful converses, stated directly in terms of the joint distribution $P(E,A\_1,\ldots,A\_n)$ and the convex geometry of $G$.

2. **Posterior-geometric characterization.** Characterize substitutes and complements through the arrangement of posterior beliefs $p\_{a\_S}$ in $\Delta(E)$ and the Bregman divergence $D\_G$. For example, identify when learning one signal causes a posterior movement that is a mean-preserving contraction or expansion, in the relevant Bregman geometry, after conditioning on other information.

3. **Algorithmic certification.** Given an explicit finite information structure and a succinct description of $G$, design an efficient procedure that either certifies weak, moderate, or strong substitutes/complements or outputs a counterexample inequality or garbling.

4. **Special-case complete classifications.** Fully solve important base cases, such as binary state and two finite signals, binary state and arbitrarily many binary signals, the log scoring rule, the quadratic scoring rule, or graphical information structures.

### Key References

Download and read the following paper carefully before proceeding.

1. Yiling Chen and Bo Waggoner, "Informational Substitutes" FOCS 2016. Available at https://arxiv.org/pdf/1703.08636 -- introduces weak, moderate, and strong informational substitutes and complements; proves the revelation principle for decision problems and proper scoring rules; gives generalized-entropy and Bregman-divergence characterizations; and develops prediction-market and signal-selection applications.

Also consult:

- Alexander Frankel and Emir Kamenica, "Quantifying Information and Uncertainty", American Economic Review 2019. Available at https://faculty.chicagobooth.edu/-/media/faculty/emir-kamenica/documents/aer20181897.pdf -- characterizes valid measures of information and uncertainty, including their Bregman-divergence structure.

- Yiling Chen, Stanko Dimitrov, Rahul Sami, Daniel M. Reeves, David M. Pennock, Robin D. Hanson, Lance Fortnow, and Rica Gonen, "Gaming Prediction Markets: Equilibrium Strategies with a Market Maker", Algorithmica 2010. Available at https://bpb-us-e1.wpmucdn.com/sites.harvard.edu/dist/b/845/files/2025/01/algorithmica10.pdf -- studies logarithmic market-scoring-rule equilibria under conditionally independent and unconditionally independent signals.

- Yuqing Kong and Grant Schoenebeck, "Optimizing Bayesian Information Revelation Strategy in Prediction Markets: the Alice Bob Alice Case", ITCS 2018. Available at https://drops.dagstuhl.de/storage/00lipics/lipics-vol094-itcs2018/LIPIcs.ITCS.2018.14/LIPIcs.ITCS.2018.14.pdf -- studies optimal first-round information revelation in the Alice-Bob-Alice game.

- Eric Neyman and Tim Roughgarden, "Are You Smarter Than a Random Expert? The Robust Aggregation of Substitutable Signals". Available at https://arxiv.org/pdf/2111.03153 -- introduces projective substitutes for robust forecast aggregation under squared loss and gives an operational projection-based substitute condition.
