# Two-player nonlocal games: classical and entangled values

A two-player one-round game is $G = (X, Y, A, B, \pi, V)$ with finite question sets $X, Y$, finite answer sets $A, B$, a
probability distribution $\pi$ on $X \times Y$ and a predicate $V : X \times Y \times A \times B \to \{0,1\}$. The classical value is the
maximum over deterministic strategies $a : X \to A$, $b : Y \to B$ of $\sum_{x,y} \pi(x,y) V(x,y,a(x),b(y))$; shared
randomness does not increase it. The entangled (tensor-product) value is the supremum, over all finite dimensions
$d_A, d_B$, states on $\mathbb{C}^{d_A} \otimes \mathbb{C}^{d_B}$ and families of projective measurements indexed by the questions,
of the winning probability, a supremum over unbounded dimensions rather than a maximum in a fixed dimension; pure
states with POVMs give the same supremum. The commuting-operator value is a different notion.
The classical value is at most the entangled value, which is at most $1$.

## Expansion

A good expansion adds a page for each pending prerequisite below and links it under the dependency sections.

- Statement prerequisite: Finite-dimensional quantum state (pure and mixed).
- Statement prerequisite: Measurements (POVM, projective) and the Born rule.

## Sources

- Z. Ji, A. Natarajan, T. Vidick, J. Wright and H. Yuen, "MIP* = RE", arXiv:2001.04383v3, Section 1.1, equation (5) (classical value with shared randomness), Section 1.2, equation (6) and the inequality $\mathrm{val}(G) \le \mathrm{val}^*(G)$, and Definitions 5.1–5.3 (games, tensor-product strategies, tensor-product value as a supremum). <https://arxiv.org/abs/2001.04383>
- R. de Wolf, *Quantum Computing: Lecture Notes*, arXiv:1907.09415v6, §17.1 (the two-party non-locality setting with shared randomness or entanglement). <https://arxiv.org/pdf/1907.09415v6>
