# Håstad: MAX-E3LIN-2 is NP-hard to approximate beyond 1/2

For all $\delta, \varepsilon > 0$ with $1/2 + \varepsilon < 1 - \delta$, the promise problem $\mathrm{GapE3LIN}_2(1-\delta, 1/2 + \varepsilon)$ is NP-hard: given a system of linear equations over $\mathbb{F}_2$, each on exactly three distinct variables, distinguish systems in which some assignment satisfies at least a $1 - \delta$ fraction of the equations from systems in which every assignment satisfies at most a $1/2 + \varepsilon$ fraction. Hence for every $\rho > 1/2$, a polynomial-time $\rho$-approximation algorithm for MAX-E3LIN-2 implies $\mathrm{P} = \mathrm{NP}$; the factor $1/2$ is attained by a random assignment.

## Proof sketch

Reduce from Label Cover with soundness $\eta(\varepsilon, \delta)$: replace each vertex by a folded long code table and each edge by all instances of Håstad's 3-bit test, written as weighted linear equations (folding is enforced by identifying complementary positions). Completeness $1-\delta$ comes from the long codes of a satisfying labelling, and soundness from spectral decoding.

## Depends on

- [Label Cover (projection games)](../two-prover-games-and-parallel-repetition/label-cover-projection-games.md)
- [NP-complete decision problems](../../complexity-classes/mahaney-s-theorem/npcomplete.md)

## Proof depends on

- [Label Cover is NP-hard with perfect completeness and arbitrarily small soundness](../two-prover-games-and-parallel-repetition/label-cover-np-hard-with-small-soundness.md)
- [Fourier expansion and completeness of Håstad's 3-bit test](fourier-expansion-of-hastads-test.md)
- [Spectral decoding: Håstad's test against Label Cover](spectral-decoding-for-hastads-test.md)

## Sources

- J. Håstad, "Some Optimal Inapproximability Results", Journal of the ACM 48(4), 2001.
- O. Goldreich, "Computational Complexity: A Conceptual Perspective", Cambridge University Press, 2008.
