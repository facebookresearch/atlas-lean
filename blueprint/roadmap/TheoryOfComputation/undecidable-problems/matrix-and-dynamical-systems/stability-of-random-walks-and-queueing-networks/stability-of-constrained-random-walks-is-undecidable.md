# Stability of constrained homogeneous random walks is undecidable

No algorithm decides, given a constrained homogeneous random walk in the nonnegative orthant and a starting point, whether the walk is stable, even when every transition probability is 0 or 1; the same holds for single-station queueing systems under generalized priority policies.

For $C>0$ let $X_C=\{z\in\mathbb Z_+^d:\sum_iz_i< C\}$. The walk *started at* $a\in\mathbb Z_+^d$ is *stable* if there is $C>0$ such that, with probability $1$, the walk with $Q(0)=a$ visits $X_C$ infinitely often; this is the formulation of Poonen's survey, the one in which the starting point is part of the instance. Gamarnik's Definition 1 of the 2007 paper (*positive recurrence*) also requires the expected hitting time of $X_C$ to be finite from every state, and does not depend on a starting point. The dimension $d\ge0$ is part of the input, and the transition probabilities are rational numbers, given as fractions of integers.

**Theorem (Gamarnik).** There is no algorithm that decides, given the dimension $d$, the rational transition probabilities $p(\Lambda,\Delta)$ of a [constrained homogeneous random walk](constrained-homogeneous-random-walks.md) in $\mathbb Z_+^d$ and a starting point $a\in\mathbb Z_+^d$, whether the walk started at $a$ is stable in this sense. This remains undecidable when all the probabilities are $0$ or $1$, i.e. for deterministic walks.

As a remark, the same holds, by the 2002 paper as summarized in Section 7 of the 2007 paper, for the stability of a single-station queueing system: $I$ part types, type $i$ visiting the station $J_i$ times with unit service time per visit, one part of type $i$ arriving at each multiple of a fixed integer $M$ with rational probability $p_i$, the system $(Q, u)$ being *stable* if some finite $C$ bounds the total number of parts for infinitely many $t$ with probability $1$, and the scheduling following a *generalized priority* policy $u$, i.e. a policy whose scheduling decision is a fixed function of which buffers are nonempty.

## Depends on

- [Constrained homogeneous random walks in the orthant](constrained-homogeneous-random-walks.md)
- [Decidability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Two-counter machines are universal](../../../equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

Gamarnik shows that deterministic constrained walks can simulate any Turing machine, through counter machines. The undecidable property behind the reduction is the stability of counter machines: whether a two-counter machine started in a given configuration with both counters zero keeps both counters bounded, which is undecidable by a simple reduction from the halting problem (as recalled by Gamarnik and Katz). A good expansion links pages for the stability of counter machines and for the simulation by walks.

## Sources

- Bjorn Poonen, "Undecidable problems: a sampler", in *Interpreting Gödel: Critical Essays* (J. Kennedy, ed.), Cambridge University Press, 2014, pp. 211–241, doi:[10.1017/CBO9780511756306.015](https://doi.org/10.1017/CBO9780511756306.015); read in arXiv:1204.0299v2 ([arXiv](https://arxiv.org/abs/1204.0299v2)), Section 11 (Probability), section numbering of arXiv:1204.0299v2.
- David Gamarnik, "On the Undecidability of Computing Stationary Distributions and Large Deviation Rates for Constrained Random Walks", *Mathematics of Operations Research* 32(2), 2007, pp. 257–265, doi:[10.1287/moor.1060.0247](https://doi.org/10.1287/moor.1060.0247); read in arXiv:math/0204268v1 ([arXiv](https://arxiv.org/abs/math/0204268v1)), whose numbering is used here: Sections 3 (model and linear Lyapunov functions), 4 (counter machines, Theorem 1), 5 (Theorem 2 and Proposition 1), 6 (Theorem 3), 7 (Theorem 4) and 8 (Theorem 6).
- David Gamarnik and Dmitriy Katz, "On deciding stability of multiclass queueing networks under buffer priority scheduling policies", *The Annals of Applied Probability* 19(5), 2009, pp. 2008–2037, doi:[10.1214/09-AAP597](https://doi.org/10.1214/09-AAP597); read in arXiv:0708.1034v2, the reprint of the published article, whose numbering is used here: Section 3.2 (stability of counter machines, with the earlier paper below as the source).
- David Gamarnik, "On Deciding Stability of Constrained Homogeneous Random Walks and Queueing Systems", *Mathematics of Operations Research* 27(2), 2002, pp. 272–293, doi:[10.1287/moor.27.2.272.321](https://doi.org/10.1287/moor.27.2.272.321) (cited beside the survey above and the paper below, which state its results; not read here).
