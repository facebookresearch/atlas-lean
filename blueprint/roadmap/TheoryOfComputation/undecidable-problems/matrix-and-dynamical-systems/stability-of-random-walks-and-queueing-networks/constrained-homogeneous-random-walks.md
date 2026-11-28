# Constrained homogeneous random walks in the orthant

Constrained homogeneous random walks are Markov chains on the lattice points of the nonnegative orthant that move by unit steps whose distribution depends only on which coordinates are currently zero, with transition probabilities fixed on each face.

For $d\ge0$ let $\mathbb Z_+^d$ be the set of $d$-dimensional vectors with nonnegative integer entries. For $\Lambda\subseteq\{1,\dots,d\}$ the *face* $\mathbb Z_+^d(\Lambda)$ is the set of $z$ with $z_i>0$ for $i\in\Lambda$ and $z_i=0$ for $i\notin\Lambda$. A *constrained homogeneous random walk* in $\mathbb Z_+^d$ is a Markov chain $Q(t)$, $t=0,1,2,\dots$, given by rational transition probabilities $p(\Lambda,\Delta)$ (each a fraction of integers) for $\Lambda\subseteq\{1,\dots,d\}$ and $\Delta\in\{-1,0,1\}^d$, with $\sum_\Delta p(\Lambda,\Delta)=1$ for each $\Lambda$ and $p(\Lambda,\Delta)=0$ whenever $\Delta_i=-1$ for some $i\notin\Lambda$; from a state on the face $\mathbb Z_+^d(\Lambda)$ it moves to $Q(t)+\Delta$ with probability $p(\Lambda,\Delta)$. The walk is *deterministic* if every $p(\Lambda,\Delta)$ is $0$ or $1$.

## Depends on

None.

## Proof depends on

None.

## Remarks

These walks are the embedded chains of many Markovian queueing networks. Their stability (positive recurrence) and linear Lyapunov functions are defined on the theorem pages of this folder that use them.

## Sources

- David Gamarnik, "On the Undecidability of Computing Stationary Distributions and Large Deviation Rates for Constrained Random Walks", *Mathematics of Operations Research* 32(2), 2007, pp. 257–265, doi:[10.1287/moor.1060.0247](https://doi.org/10.1287/moor.1060.0247); read in arXiv:math/0204268v1 ([arXiv](https://arxiv.org/abs/math/0204268v1)), whose numbering is used here: Section 3 (the model and the deterministic case).
- Bjorn Poonen, "Undecidable problems: a sampler", in *Interpreting Gödel: Critical Essays* (J. Kennedy, ed.), Cambridge University Press, 2014, pp. 211–241, doi:[10.1017/CBO9780511756306.015](https://doi.org/10.1017/CBO9780511756306.015); read in arXiv:1204.0299v2 ([arXiv](https://arxiv.org/abs/1204.0299v2)), Section 11 (Probability: the description of the walk), section numbering of arXiv:1204.0299v2.
