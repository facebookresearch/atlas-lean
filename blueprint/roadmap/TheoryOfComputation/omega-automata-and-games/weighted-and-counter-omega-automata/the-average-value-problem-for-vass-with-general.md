# The average-value problem for VASS with general linear costs is undecidable

No algorithm decides whether a vector addition system with states over the natural numbers has an infinite computation, or an ultimately periodic one,
whose long-run average cost stays below a threshold when each state weighs the counters by its own linear cost function.

A $k$-dimensional *vector addition system with states* $\mathcal{V} = (Q, Q_0, \delta)$ over $\mathbb{N}$ has states $Q$, initial states $Q_0$ and transitions $(q, q', \vec{y}) \in Q \times Q \times \mathbb{Z}^k$; a *computation* is an infinite sequence of configurations $(q_i, \vec{x}_i) \in Q \times \mathbb{N}^k$ starting in
some $(q_0, \vec{0})$ with $q_0 \in Q_0$, each step following a transition $(q_i, q_{i+1}, \vec{y})$ with $\vec{x}_{i+1} = \vec{x}_i + \vec{y}$; it is *regular* if its path of transitions is ultimately periodic. A *cost function* is given by a labeling $l : Q \to \mathbb{N}^k$, with $f(q, \vec{x}) = l(q) \cdot \vec{x}$; it is *uniform* if
$l$ is constant. For a computation $\pi$ with configurations $\pi[0], \pi[1], \dots$, let

$$
\mathrm{LimAvg}(f(\pi)) = \liminf_{k \to \infty} \frac{1}{k+1} \sum_{i=0}^{k} f(\pi[i]) .
$$

The *average-value problem* (resp. *regular average-value problem*) asks, given $\mathcal{V}$, $f$ and a rational $\lambda$, whether some computation (resp. some regular computation) $\pi$ has $\mathrm{LimAvg}(f(\pi)) \le \lambda$.

**Theorem.** For vector addition systems with states over $\mathbb{N}$ and general cost functions, the average-value problem and the regular average-value problem are undecidable.

In contrast, with uniform cost functions whose coefficients are nonzero both problems are decidable, being inter-reducible with configuration reachability; whether some regular computation has finite long-run average is decidable; and over $\mathbb{Z}$, without the nonnegativity
constraint, the regular average-value problem with general costs is NP-complete and both problems with uniform costs are in polynomial time. For two-player games on such systems the average-value problem is undecidable already with uniform costs.

## Depends on

None.

## Proof depends on

- [Two-counter machines are universal](../../equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)
- [Halting is undecidable](../../computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halts.md)

## Expansion

The proof reduces the halting problem for Minsky machines. The constructed system reads blocks $u_1 \# u_2 \# \cdots$; its finite control checks that each block encodes a terminating computation provided every zero test is correct, and counters $c_1, c_2$ hold the register values minus one, the state
recording whether a register is $0$, $1$ or $c_i + 1$. Since a vector addition system cannot test for zero, the state may claim that a register is $0$ or $1$ while $c_i > 0$; the cost function returns $c_i$ in exactly those states. As costs are natural numbers, a regular computation has average value $0$
only if all costs along its period vanish, so all tests are correct and the blocks encode terminating computations. For arbitrary computations two further counters force the block lengths to stay bounded, so that average value $0$ again yields a block with all costs $0$. Conversely, a
terminating computation with encoding $u$ gives the computation labeled $(\# u)^\omega$ of average value $0$. Büchi conditions used in the construction are eliminated.

## Sources

- K. Chatterjee, T. A. Henzinger and J. Otop, "Long-run average behavior of vector addition systems with states", in *30th International Conference on Concurrency Theory (CONCUR 2019)*, LIPIcs 140, paper 27, 2019, doi:10.4230/LIPIcs.CONCUR.2019.27; read in arXiv:1905.05537v1: the undecidability theorem for natural-valued VASS with general cost functions with its proof sketch, the definitions of Section 2, the decidability theorems for uniform costs and for integer-valued VASS, and the remarks on games.
