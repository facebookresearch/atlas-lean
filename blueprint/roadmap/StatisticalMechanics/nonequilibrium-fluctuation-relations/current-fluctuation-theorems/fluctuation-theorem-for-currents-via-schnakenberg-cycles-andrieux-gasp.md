# Fluctuation theorem for currents via Schnakenberg cycles

Let $X$ be an irreducible continuous-time Markov jump process on a finite state space whose transition graph is connected and in which every transition has a reverse transition, in its stationary state. Orient the edges, choose a spanning tree, and let each chord $e_c$ outside the tree define an oriented fundamental cycle $c$ (Schnakenberg's construction), with affinity $A_c = \ln \prod_{e \in c} r(e)/r(-e)$, the products taken along the cycle in its orientation. Let $J_c(t)$ be the integrated current through the chord of $c$ up to time $t$ (net number of jumps along it) and $j_c(t) = J_c(t)/t$ the empirical current. Andrieux and Gaspard (2007) prove that the scaled cumulant generating function

$$Q(\eta) = -\lim_{t\to\infty} \frac1t \ln E\bigl[e^{-\eta\cdot J(t)}\bigr]$$

satisfies $Q(\eta) = Q(A - \eta)$ for all $\eta$; with this convention $-Q(\eta)$ is the dominant eigenvalue of the tilted generator (their Eq. (47)). Consequently the large deviation rate function $I$ of the empirical currents satisfies $I(-j) - I(j) = A \cdot j$, that is, the probability of $j(t)$ near $j$ and of $j(t)$ near $-j$ have logarithmic ratio $t\, A\cdot j$ as $t \to \infty$.

## Depends on

- [Large deviation principle for a sequence of measures](../../../Probability/large-deviations/large-deviation-principle/satisfies-ldp.md)
- [Rate matrix](../../../Probability/markov-chains/finite-continuous-time-markov-chains/rate-matrices-of-finite-continuous-time-markov-c/is-rate-matrix.md)
- [Path of a continuous-time Markov chain](../../../Probability/markov-chains/finite-continuous-time-markov-chains/finite-continuous-time-markov-chains-as-path-pro/ctmc-path.md)

## Expansion

1. The model: the oriented transition graph, spanning trees, chords and oriented fundamental cycles as integer circulations (not the binary cycle space), Schnakenberg's affinities and the chord currents.
2. The tilted generator $L_\eta$ (a Metzler matrix) and the identification of $-Q(\eta)$ with its Perron eigenvalue, via [Perron–Frobenius](../../../LinearAlgebra/special-matrices/perron-frobenius-theorem/perron-frobenius.md) applied to $L_\eta + cI$ for large $c$.
3. The symmetry $Q(\eta) = Q(A - \eta)$ from the characteristic determinant, as in the source (Eqs. (34)–(39), (45)–(47), with the determinant in Eqs. (48)–(59)).
4. The large deviation form via the [Gärtner–Ellis theorem](../../../Probability/large-deviations/satisfies-ldp-of-tendsto-scaled-cgf.md), with differentiability of $Q$ as a hypothesis and the passage from integer to continuous times.
5. How the cycle currents and affinities change when a different spanning tree is chosen.

## Proof depends on

- [Perron–Frobenius theorem](../../../LinearAlgebra/special-matrices/perron-frobenius-theorem/perron-frobenius.md)
- [Gärtner–Ellis theorem](../../../Probability/large-deviations/satisfies-ldp-of-tendsto-scaled-cgf.md)

## Sources

- D. Andrieux and P. Gaspard, Fluctuation theorem for currents and Schnakenberg network theory, J. Stat. Phys. 127 (2007), 107–131, Eqs. (34)–(39), (45)–(59), (71)–(74). <https://arxiv.org/abs/cond-mat/0512254>
